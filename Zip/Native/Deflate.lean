import Zip.Native.BitWriter
import Zip.Native.Inflate
import Std.Tactic.BVDecide

/-!
  Pure Lean DEFLATE compressor.

  Level 0: stored blocks (uncompressed).
  Level 1: greedy LZ77 matching with fixed Huffman codes.
  Level 2: lazy LZ77 matching with fixed Huffman codes.
-/

namespace Zip.Native.Deflate

/-- Maximum data bytes per stored block (2^16 - 1). -/
private def maxBlockSize : Nat := 65535

/-- Compress data into raw DEFLATE stored blocks (level 0).
    Splits into blocks of at most 65535 bytes. Each block has:
    - 1 byte: BFINAL (bit 0) | BTYPE=00 (bits 1-2), rest zero
    - 2 bytes LE: LEN (number of data bytes)
    - 2 bytes LE: NLEN (one's complement of LEN)
    - LEN bytes: raw data

    Empty input produces one final stored block with LEN=0. -/
def deflateStored (data : ByteArray) : ByteArray := Id.run do
  let mut result := ByteArray.empty
  if data.size == 0 then
    -- Empty: one final stored block with LEN=0
    result := result.push 0x01  -- BFINAL=1, BTYPE=00
    result := result.push 0x00  -- LEN low
    result := result.push 0x00  -- LEN high
    result := result.push 0xFF  -- NLEN low
    result := result.push 0xFF  -- NLEN high
    return result
  let mut pos := 0
  while pos < data.size do
    let remaining := data.size - pos
    let blockSize := min remaining maxBlockSize
    let isFinal := pos + blockSize >= data.size
    -- Header byte: BFINAL (bit 0), BTYPE=00 (bits 1-2)
    result := result.push (if isFinal then 0x01 else 0x00)
    -- LEN (16-bit LE)
    let len := blockSize.toUInt16
    result := result.push (len &&& 0xFF).toUInt8
    result := result.push ((len >>> 8) &&& 0xFF).toUInt8
    -- NLEN (one's complement of LEN, 16-bit LE)
    let nlen := len ^^^ 0xFFFF
    result := result.push (nlen &&& 0xFF).toUInt8
    result := result.push ((nlen >>> 8) &&& 0xFF).toUInt8
    -- Raw data
    result := result ++ data.extract pos (pos + blockSize)
    pos := pos + blockSize
  return result

/-- Compute canonical Huffman codewords from code lengths (RFC 1951 §3.2.2).
    Returns array indexed by symbol of (codeword, code_length).
    Assumes all non-zero lengths are ≤ `maxBits` (15 for DEFLATE). -/
def canonicalCodes (lengths : Array UInt8) (maxBits : Nat := 15) :
    Array (UInt16 × UInt8) :=
  let lsList := lengths.toList.map UInt8.toNat
  let blCount := Huffman.Spec.countLengths lsList maxBits
  let ncNat := Huffman.Spec.nextCodes blCount maxBits
  let nextCode : Array UInt32 := ncNat.map fun n => n.toUInt32
  go lengths nextCode 0 (Array.replicate lengths.size (0, 0))
where
  go (lengths : Array UInt8) (nextCode : Array UInt32) (i : Nat)
      (result : Array (UInt16 × UInt8)) : Array (UInt16 × UInt8) :=
    if h : i < lengths.size then
      let len := lengths[i]
      if len > 0 then
        if hlen : len.toNat < nextCode.size then
          let code := nextCode[len.toNat]
          let result' := result.set! i (code.toUInt16, len)
          let nextCode' := nextCode.set! len.toNat (code + 1)
          go lengths nextCode' (i + 1) result'
        else
          go lengths nextCode (i + 1) result
      else
        go lengths nextCode (i + 1) result
    else result
  termination_by lengths.size - i

def fixedLitCodes : Array (UInt16 × UInt8) :=
  canonicalCodes Inflate.fixedLitLengths

def fixedDistCodes : Array (UInt16 × UInt8) :=
  canonicalCodes Inflate.fixedDistLengths

/-- `canonicalCodes.go` preserves array size. -/
private theorem canonicalCodes_go_size (lengths : Array UInt8) (nextCode : Array UInt32)
    (i : Nat) (result : Array (UInt16 × UInt8)) (hrs : result.size = lengths.size) :
    (canonicalCodes.go lengths nextCode i result).size = lengths.size := by
  unfold canonicalCodes.go
  by_cases hi : i < lengths.size
  · simp only [hi, ↓reduceDIte]
    by_cases hlen : lengths[i] > 0
    · simp only [hlen, ↓reduceIte]
      by_cases hnc : lengths[i].toNat < nextCode.size
      · simp only [hnc, ↓reduceDIte]
        exact canonicalCodes_go_size lengths _ (i + 1) _ (by
          simp only [Array.set!_eq_setIfInBounds, Array.setIfInBounds]
          split <;> simp [Array.size_set, hrs])
      · simp only [show ¬(lengths[i].toNat < nextCode.size) from hnc, ↓reduceDIte]
        exact canonicalCodes_go_size lengths nextCode (i + 1) result hrs
    · simp only [show ¬(lengths[i] > 0) from hlen, ↓reduceIte]
      exact canonicalCodes_go_size lengths nextCode (i + 1) result hrs
  · simp only [show ¬(i < lengths.size) from hi, ↓reduceDIte]; exact hrs
termination_by lengths.size - i

private theorem canonicalCodes_size' (lengths : Array UInt8) (maxBits : Nat) :
    (canonicalCodes lengths maxBits).size = lengths.size := by
  unfold canonicalCodes
  exact canonicalCodes_go_size lengths _ 0 _ (by simp [Array.size_replicate])

@[simp] protected theorem fixedLitCodes_size : fixedLitCodes.size = 288 := by
  show (canonicalCodes Inflate.fixedLitLengths).size = 288
  rw [canonicalCodes_size']
  simp [Inflate.fixedLitLengths, Array.size_append, Array.size_replicate]

@[simp] protected theorem fixedDistCodes_size : fixedDistCodes.size = 32 := by
  show (canonicalCodes Inflate.fixedDistLengths).size = 32
  rw [canonicalCodes_size']
  simp [Inflate.fixedDistLengths, Array.size_replicate]

/-- Inner loop for `findTableCode`: linear search through base/extra tables.
    Requires `baseTable.size ≤ extraTable.size` for safe indexing. -/
def findTableCode.go (baseTable : Array UInt16) (extraTable : Array UInt8)
    (value : Nat) (i : Nat) (hsize : baseTable.size ≤ extraTable.size) :
    Option (Nat × Nat × UInt32) :=
  if h1 : i + 1 < baseTable.size then
    if baseTable[i + 1].toNat > value then
      let extra := (extraTable[i]'(by omega)).toNat
      let extraVal := (value - (baseTable[i]'(by omega)).toNat).toUInt32
      some (i, extra, extraVal)
    else
      findTableCode.go baseTable extraTable value (i + 1) hsize
  else if h2 : i < baseTable.size then
    let extra := (extraTable[i]'(by omega)).toNat
    let extraVal := (value - baseTable[i].toNat).toUInt32
    some (i, extra, extraVal)
  else
    none
termination_by baseTable.size - i

/-- Search a base/extra table pair for the code covering `value`.
    Returns (code_index, extra_bits_count, extra_bits_value).
    Used for both length codes (RFC 1951 §3.2.5) and distance codes. -/
def findTableCode (baseTable : Array UInt16) (extraTable : Array UInt8)
    (value : Nat) (hsize : baseTable.size ≤ extraTable.size := by decide) :
    Option (Nat × Nat × UInt32) :=
  findTableCode.go baseTable extraTable value 0 hsize

/-- Find length code for length 3–258.
    Returns (code_index 0–28, extra_bits_count, extra_bits_value). -/
def findLengthCode (length : Nat) : Option (Nat × Nat × UInt32) :=
  findTableCode Inflate.lengthBase Inflate.lengthExtra length

/-- Find distance code for distance 1–32768.
    Returns (code 0–29, extra_bits_count, extra_bits_value). -/
def findDistCode (dist : Nat) : Option (Nat × Nat × UInt32) :=
  findTableCode Inflate.distBase Inflate.distExtra dist

/-- `findTableCode.go` returns an index < baseTable.size when successful. -/
private theorem findTableCode_go_idx_lt {baseTable : Array UInt16} {extraTable : Array UInt8}
    {value i : Nat} {hsize : baseTable.size ≤ extraTable.size}
    {idx extraN : Nat} {extraV : UInt32}
    (h : findTableCode.go baseTable extraTable value i hsize = some (idx, extraN, extraV)) :
    idx < baseTable.size := by
  unfold findTableCode.go at h
  split at h
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
    · exact findTableCode_go_idx_lt h
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
    · exact nomatch h
termination_by baseTable.size - i

/-- `findLengthCode` returns idx < 29. -/
private theorem findLengthCode_idx_lt {len idx extraN : Nat} {extraV : UInt32}
    (h : findLengthCode len = some (idx, extraN, extraV)) : idx < 29 :=
  findTableCode_go_idx_lt h

/-- `findDistCode` returns dIdx < 30. -/
private theorem findDistCode_idx_lt {dist dIdx dExtraN : Nat} {dExtraV : UInt32}
    (h : findDistCode dist = some (dIdx, dExtraN, dExtraV)) : dIdx < 30 :=
  findTableCode_go_idx_lt h

inductive LZ77Token where
  | literal : UInt8 → LZ77Token
  | reference : (length : Nat) → (distance : Nat) → LZ77Token
  deriving BEq, Inhabited

/-! ## Packed tokens (Wave 3b)

Every `LZ77Token` push in the matcher hot loops allocates a boxed
constructor cell. `packTok` encodes a token in one unboxed `UInt32` instead:
literals are the byte value (tag bit 31 clear); references set bit 31 and
carry the length in bits 16–30 and the distance in bits 0–15. The field
split is forced by the DEFLATE ranges: `dist ≤ 32768 = 2^15` needs 16 bits
exactly (32768 itself does not fit in 15), so the distance owns bits 0–15
and the length (`≤ 258 < 2^15`) sits at bit 16 with 15 bits of room below
the tag. `unpackTok` is the boxed *spec-level view* of a packed token;
`unpackTok_packTok` shows the view recovers every encodable token, which is
what lets `Zip/Spec/LZ77PackedCorrect.lean` prove the packed matcher twins
(`lz77ChainIterP`/`lz77ChainLazyIterP`) equal to the boxed matchers viewed
through `unpackTok`. -/

/-- Pack a token into one `UInt32`: literal `b` ↦ `b`; reference ↦
    `1<<<31 ||| len<<<16 ||| dist`. Lossless on encodable tokens
    (`unpackTok_packTok`). -/
@[inline] def packTok : LZ77Token → UInt32
  | .literal b => b.toUInt32
  | .reference len dist => ((1 : UInt32) <<< 31) ||| (len.toUInt32 <<< 16) ||| dist.toUInt32

/-- Boxed view of a packed token (left inverse of `packTok` on encodable
    tokens: `unpackTok_packTok`). -/
@[inline] def unpackTok (w : UInt32) : LZ77Token :=
  if w &&& ((1 : UInt32) <<< 31) = 0 then
    .literal w.toUInt8
  else
    .reference ((w >>> 16) &&& 0x7FFF).toNat (w &&& 0xFFFF).toNat

/-- `unpackTok` recovers every token within the encoder bounds (literals
    unconditionally; references with `3 ≤ len ≤ 258`, `1 ≤ dist ≤ 32768` —
    exactly the `Enc` predicate of the matcher encodability theorems). The
    bit-level facts are discharged by `bv_decide` after `generalize`-ing the
    `Nat → UInt32` casts into variables carrying their `≤` bounds. -/
theorem unpackTok_packTok (t : LZ77Token)
    (h : match t with
      | .literal _ => True
      | .reference len dist => 3 ≤ len ∧ len ≤ 258 ∧ 1 ≤ dist ∧ dist ≤ 32768) :
    unpackTok (packTok t) = t := by
  match t with
  | .literal b =>
    have h1 : (b.toUInt32 &&& ((1 : UInt32) <<< 31)) = 0 := by bv_decide
    have h2 : b.toUInt32.toUInt8 = b := by bv_decide
    simp [unpackTok, packTok, h1, h2]
  | .reference len dist =>
    obtain ⟨_, h258, h1d, h32768⟩ := h
    have hl : len.toUInt32.toNat = len := by simp [Nat.toUInt32]; omega
    have hd : dist.toUInt32.toNat = dist := by simp [Nat.toUInt32]; omega
    simp only [packTok, unpackTok]
    generalize len.toUInt32 = l at hl
    generalize dist.toUInt32 = d at hd
    have hlu : l ≤ 258 := by rw [UInt32.le_iff_toNat_le]; show l.toNat ≤ 258; omega
    have hdu : d ≤ 32768 := by rw [UInt32.le_iff_toNat_le]; show d.toNat ≤ 32768; omega
    have hcond : ¬((((1 : UInt32) <<< 31) ||| l <<< 16 ||| d) &&& ((1 : UInt32) <<< 31)) = 0 := by
      bv_decide
    have hlen : ((((1 : UInt32) <<< 31) ||| l <<< 16 ||| d) >>> 16) &&& 0x7FFF = l := by bv_decide
    have hdist : (((1 : UInt32) <<< 31) ||| l <<< 16 ||| d) &&& 0xFFFF = d := by bv_decide
    rw [if_neg hcond, hlen, hdist, hl, hd]

/-- Simple hash-based greedy LZ77 matcher.
    Scans input left-to-right, emitting literals or back-references. -/
def lz77Greedy (data : ByteArray) (windowSize : Nat := 32768) :
    Array LZ77Token :=
  if data.size < 3 then
    (trailing data 0).toArray
  else
    let hashSize := 65536
    (mainLoop data windowSize hashSize
      (.replicate hashSize 0) (.replicate hashSize false) 0).toArray
where
  @[inline] hash3 (data : ByteArray) (pos : Nat) (hashSize : Nat)
      (h : pos + 2 < data.size) : Nat :=
    -- Hash arithmetic in `UInt32` (single machine ops) rather than `Nat`
    -- (whose bitwise XOR/shift are slow); `.toNat % hashSize` keeps the exact
    -- same index, so `hash3_eq` stays `rfl` and the `< hashSize` bound holds.
    let a := (data[pos]'(by omega)).toUInt32
    let b := (data[pos + 1]'(by omega)).toUInt32
    let c := (data[pos + 2]'(by omega)).toUInt32
    ((a ^^^ (b <<< 5) ^^^ (c <<< 10)).toNat % hashSize)
  countMatch (data : ByteArray) (p1 p2 maxLen : Nat)
      (h1 : p1 + maxLen ≤ data.size) (h2 : p2 + maxLen ≤ data.size) : Nat :=
    go data p1 p2 0 maxLen h1 h2
  go (data : ByteArray) (p1 p2 i maxLen : Nat)
      (h1 : p1 + maxLen ≤ data.size) (h2 : p2 + maxLen ≤ data.size) : Nat :=
    if hi : i < maxLen then
      if (data[p1 + i]'(by omega)) == (data[p2 + i]'(by omega)) then
        go data p1 p2 (i + 1) maxLen h1 h2
      else i
    else i
  termination_by maxLen - i
  trailing (data : ByteArray) (pos : Nat) : List LZ77Token :=
    if h : pos < data.size then
      .literal (data[pos]'h) :: trailing data (pos + 1)
    else []
  termination_by data.size - pos
  updateHashes (data : ByteArray) (hashSize : Nat)
      (hashTable : Array Nat) (hashValid : Array Bool)
      (pos j matchLen : Nat) : Array Nat × Array Bool :=
    if j < matchLen then
      if h : pos + j + 2 < data.size then
        let hsh := hash3 data (pos + j) hashSize h
        updateHashes data hashSize (hashTable.set! hsh (pos + j))
          (hashValid.set! hsh true) pos (j + 1) matchLen
      else
        updateHashes data hashSize hashTable hashValid pos (j + 1) matchLen
    else
      (hashTable, hashValid)
  termination_by matchLen - j
  mainLoop (data : ByteArray) (windowSize hashSize : Nat)
      (hashTable : Array Nat) (hashValid : Array Bool) (pos : Nat) :
      List LZ77Token :=
    if hlt : pos + 2 < data.size then
      let h := hash3 data pos hashSize hlt
      if hht : h < hashTable.size then
        if hhv : h < hashValid.size then
          let matchPos := hashTable[h]
          let isValid := hashValid[h]
          let hashTable := hashTable.set! h pos
          let hashValid := hashValid.set! h true
          if hcond : isValid ∧ matchPos < pos ∧ pos - matchPos ≤ windowSize then
            have hmp : matchPos < pos := hcond.2.1
            let maxLen := min 258 (data.size - pos)
            have hmaxLenP : pos + maxLen ≤ data.size := by omega
            have hmaxLenM : matchPos + maxLen ≤ data.size := by omega
            let matchLen := countMatch data matchPos pos maxLen hmaxLenM hmaxLenP
            if hge : matchLen ≥ 3 then
              if hle : pos + matchLen ≤ data.size then
                have : data.size - (pos + matchLen) < data.size - pos := by omega
                let (hashTable, hashValid) :=
                  updateHashes data hashSize hashTable hashValid pos 1 matchLen
                .reference matchLen (pos - matchPos) ::
                  mainLoop data windowSize hashSize hashTable hashValid (pos + matchLen)
              else
                .literal (data[pos]'(by omega)) ::
                  mainLoop data windowSize hashSize hashTable hashValid (pos + 1)
            else
              .literal (data[pos]'(by omega)) ::
                mainLoop data windowSize hashSize hashTable hashValid (pos + 1)
          else
            .literal (data[pos]'(by omega)) ::
              mainLoop data windowSize hashSize hashTable hashValid (pos + 1)
        else
          .literal (data[pos]'(by omega)) ::
            mainLoop data windowSize hashSize hashTable hashValid (pos + 1)
      else
        .literal (data[pos]'(by omega)) ::
          mainLoop data windowSize hashSize hashTable hashValid (pos + 1)
    else
      trailing data pos
  termination_by data.size - pos
  decreasing_by all_goals omega

/-- Iterative (tail-recursive, Array-accumulating) version of `lz77Greedy`.
    Same output, but does not overflow the stack on large inputs because
    `mainLoop` and `trailing` accumulate into an `Array` parameter instead
    of building a `List` via cons.  The existing `lz77Greedy` is preserved
    unchanged for proofs. -/
def lz77GreedyIter (data : ByteArray) (windowSize : Nat := 32768) :
    Array LZ77Token :=
  if data.size < 3 then
    trailing data 0 #[]
  else
    let hashSize := 65536
    mainLoop data windowSize hashSize
      (.replicate hashSize 0) (.replicate hashSize false) 0 #[]
where
  @[inline] hash3 (data : ByteArray) (pos : Nat) (hashSize : Nat)
      (h : pos + 2 < data.size) : Nat :=
    -- Hash arithmetic in `UInt32` (single machine ops) rather than `Nat`
    -- (whose bitwise XOR/shift are slow); `.toNat % hashSize` keeps the exact
    -- same index, so `hash3_eq` stays `rfl` and the `< hashSize` bound holds.
    let a := (data[pos]'(by omega)).toUInt32
    let b := (data[pos + 1]'(by omega)).toUInt32
    let c := (data[pos + 2]'(by omega)).toUInt32
    ((a ^^^ (b <<< 5) ^^^ (c <<< 10)).toNat % hashSize)
  countMatch (data : ByteArray) (p1 p2 maxLen : Nat)
      (h1 : p1 + maxLen ≤ data.size) (h2 : p2 + maxLen ≤ data.size) : Nat :=
    go data p1 p2 0 maxLen h1 h2
  go (data : ByteArray) (p1 p2 i maxLen : Nat)
      (h1 : p1 + maxLen ≤ data.size) (h2 : p2 + maxLen ≤ data.size) : Nat :=
    if hi : i < maxLen then
      if (data[p1 + i]'(by omega)) == (data[p2 + i]'(by omega)) then
        go data p1 p2 (i + 1) maxLen h1 h2
      else i
    else i
  termination_by maxLen - i
  trailing (data : ByteArray) (pos : Nat) (acc : Array LZ77Token) :
      Array LZ77Token :=
    if h : pos < data.size then
      trailing data (pos + 1) (acc.push (.literal data[pos]))
    else acc
  termination_by data.size - pos
  updateHashes (data : ByteArray) (hashSize : Nat)
      (hashTable : Array Nat) (hashValid : Array Bool)
      (pos j matchLen : Nat) : Array Nat × Array Bool :=
    if j < matchLen then
      if h : pos + j + 2 < data.size then
        let hsh := hash3 data (pos + j) hashSize h
        updateHashes data hashSize (hashTable.set! hsh (pos + j))
          (hashValid.set! hsh true) pos (j + 1) matchLen
      else
        updateHashes data hashSize hashTable hashValid pos (j + 1) matchLen
    else
      (hashTable, hashValid)
  termination_by matchLen - j
  mainLoop (data : ByteArray) (windowSize hashSize : Nat)
      (hashTable : Array Nat) (hashValid : Array Bool) (pos : Nat)
      (acc : Array LZ77Token) :
      Array LZ77Token :=
    if hlt : pos + 2 < data.size then
      let hsh := hash3 data pos hashSize hlt
      if hht : hsh < hashTable.size then
        if hhv : hsh < hashValid.size then
          let matchPos := hashTable[hsh]
          let isValid := hashValid[hsh]
          let hashTable := hashTable.set! hsh pos
          let hashValid := hashValid.set! hsh true
          if hcond : isValid ∧ matchPos < pos ∧ pos - matchPos ≤ windowSize then
            have hmp : matchPos < pos := hcond.2.1
            let maxLen := min 258 (data.size - pos)
            have hmaxLenP : pos + maxLen ≤ data.size := by omega
            have hmaxLenM : matchPos + maxLen ≤ data.size := by omega
            let matchLen := countMatch data matchPos pos maxLen hmaxLenM hmaxLenP
            if hge : matchLen ≥ 3 then
              if hle : pos + matchLen ≤ data.size then
                have : data.size - (pos + matchLen) < data.size - pos := by omega
                let (hashTable, hashValid) :=
                  updateHashes data hashSize hashTable hashValid pos 1 matchLen
                mainLoop data windowSize hashSize hashTable hashValid
                  (pos + matchLen)
                  (acc.push (.reference matchLen (pos - matchPos)))
              else
                mainLoop data windowSize hashSize hashTable hashValid (pos + 1)
                  (acc.push (.literal (data[pos]'(by omega))))
            else
              mainLoop data windowSize hashSize hashTable hashValid (pos + 1)
                (acc.push (.literal (data[pos]'(by omega))))
          else
            mainLoop data windowSize hashSize hashTable hashValid (pos + 1)
              (acc.push (.literal (data[pos]'(by omega))))
        else
          mainLoop data windowSize hashSize hashTable hashValid (pos + 1)
            (acc.push (.literal (data[pos]'(by omega))))
      else
        mainLoop data windowSize hashSize hashTable hashValid (pos + 1)
          (acc.push (.literal (data[pos]'(by omega))))
    else
      trailing data pos acc
  termination_by data.size - pos
  decreasing_by all_goals omega

/-- Per-position chain-head insertion with one runtime bounds check (Wave 3
    Step 0.2, same pattern as `chainWalkGuarded`/`updateHashesGuarded` below):
    read the old head of bucket `h`, point the bucket at `pos`, and link
    `prev[pos]` to the old head. The single guard discharges all three accesses
    statically; the fallback keeps the original panic-checked operations and is
    dead in practice — `hashTable`/`prev` sizes are fixed at allocation.
    Provably equal to the panic-checked sequence (`headInsertGuarded_eq` in
    `LZ77ChainCorrect`). -/
@[inline] def headInsertGuarded (hashTable prev : Array Nat) (h pos : Nat) :
    Nat × Array Nat × Array Nat :=
  if hg : h < hashTable.size ∧ pos < prev.size then
    let head := hashTable[h]'hg.1
    (head, hashTable.set h pos hg.1, prev.set pos head hg.2)
  else
    let head := hashTable[h]!
    (head, hashTable.set! h pos, prev.set! pos head)

/-- Single guarded chain-head probe (for the lazy matcher's lookahead position,
    which reads a bucket head without inserting): one runtime bounds check,
    panic-checked fallback (dead in practice). Provably equal to `hashTable[h]!`
    (`headProbeGuarded_eq` in `LZ77ChainCorrect`). -/
@[inline] def headProbeGuarded (hashTable : Array Nat) (h : Nat) : Nat :=
  if hb : h < hashTable.size then hashTable[h]'hb else hashTable[h]!

/-- Greedy LZ77 with bounded-depth hash chains: at each position, walk the
    `prev` chain from the bucket head up to `maxChain` candidates and keep the
    longest in-window match. This finds far longer matches than the single-probe
    `lz77Greedy`/`lz77Lazy` (it reaches C-reference ratio on text).

    The chain is only a *heuristic for finding* candidates — validity is
    re-established at the moment of emission by `countMatch` (verifies the bytes)
    plus the explicit `matchPos < pos` / `pos - matchPos ≤ windowSize` guards, so
    the `prev`/`hashTable` array contents never enter the correctness proof.
    Buckets and `prev` are initialised to the sentinel `data.size` (≥ every real
    position), so an unset chain link fails the `cand < pos` guard and stops the
    walk — no separate validity bitmap needed. Reuses `lz77Greedy`'s
    `hash3`/`countMatch`/`trailing` helpers (and their proofs). -/
def lz77Chain (data : ByteArray) (maxChain : Nat) (windowSize : Nat := 32768)
    (insertCap : Nat := 1000000000) :
    Array LZ77Token :=
  if data.size < 3 then
    (lz77Greedy.trailing data 0).toArray
  else
    let hashSize := 65536
    (mainLoop data windowSize hashSize maxChain
      (.replicate hashSize data.size) (.replicate data.size data.size) 0 insertCap).toArray
where
  /-- Walk the `prev` chain up to `fuel` steps from `cand`, keeping the longest
      in-window match `(bestLen, bestPos)`. Stops at the first out-of-window or
      out-of-range link (`cand ≥ pos`, incl. the `data.size` sentinel). -/
  chainWalk (data : ByteArray) (prev : Array Nat) (windowSize pos maxLen : Nat)
      (hpm : pos + maxLen ≤ data.size) (cand fuel bestLen bestPos : Nat) : Nat × Nat :=
    if fuel = 0 then (bestLen, bestPos)
    else if hc : cand < pos ∧ pos - cand ≤ windowSize then
      have hcand : cand + maxLen ≤ data.size := by omega
      let ml := lz77Greedy.countMatch data cand pos maxLen hcand hpm
      let (bl, bp) := if ml > bestLen then (ml, cand) else (bestLen, bestPos)
      -- Early stop: a match of the maximum possible length cannot be beaten, so
      -- stop walking the chain. Provably zero ratio loss; on repetitive input
      -- (matches reach `maxLen` immediately) this restores near-greedy speed.
      if bl ≥ maxLen then (bl, bp)
      else chainWalk data prev windowSize pos maxLen hpm (prev[cand]!) (fuel - 1) bl bp
    else (bestLen, bestPos)
  termination_by fuel
  decreasing_by omega
  /-- Insert positions `pos+1 .. pos+min(matchLen-1, insertCap)` into the chains so
      later matches can reach them: `prev[p] := head[bucket]`, then `head[bucket] := p`.
      `insertCap` bounds the interior insertions per match — a small cap (fast levels)
      defers most of this work for speed at a ratio cost; a large cap inserts every
      position (best ratio). The chain is a heuristic, so any cap stays correct. -/
  updateHashes (data : ByteArray) (hashSize : Nat)
      (hashTable prev : Array Nat) (pos j matchLen insertCap : Nat) : Array Nat × Array Nat :=
    if j < matchLen ∧ j ≤ insertCap then
      if h : pos + j + 2 < data.size then
        let hsh := lz77Greedy.hash3 data (pos + j) hashSize h
        let head := hashTable[hsh]!
        updateHashes data hashSize (hashTable.set! hsh (pos + j)) (prev.set! (pos + j) head)
          pos (j + 1) matchLen insertCap
      else
        updateHashes data hashSize hashTable prev pos (j + 1) matchLen insertCap
    else (hashTable, prev)
  termination_by matchLen - j
  decreasing_by all_goals omega
  mainLoop (data : ByteArray) (windowSize hashSize maxChain : Nat)
      (hashTable prev : Array Nat) (pos insertCap : Nat) : List LZ77Token :=
    if hlt : pos + 2 < data.size then
      let h := lz77Greedy.hash3 data pos hashSize hlt
      let (head, hashTable, prev) := headInsertGuarded hashTable prev h pos
      let maxLen := min 258 (data.size - pos)
      have hmaxLenP : pos + maxLen ≤ data.size := by omega
      let (matchLen, matchPos) :=
        chainWalk data prev windowSize pos maxLen hmaxLenP head maxChain 0 0
      if hge : matchLen ≥ 3 then
        if hle : pos + matchLen ≤ data.size then
          have : data.size - (pos + matchLen) < data.size - pos := by omega
          let (hashTable, prev) := updateHashes data hashSize hashTable prev pos 1 matchLen insertCap
          .reference matchLen (pos - matchPos) ::
            mainLoop data windowSize hashSize maxChain hashTable prev (pos + matchLen) insertCap
        else
          .literal (data[pos]'(by omega)) ::
            mainLoop data windowSize hashSize maxChain hashTable prev (pos + 1) insertCap
      else
        .literal (data[pos]'(by omega)) ::
          mainLoop data windowSize hashSize maxChain hashTable prev (pos + 1) insertCap
    else
      lz77Greedy.trailing data pos
  termination_by data.size - pos
  decreasing_by all_goals omega

/-! ### Proven-bounds matcher hot loops (Wave 2d)

The `prev`/`hashTable` chain state is a pure heuristic — its contents never enter
any correctness proof (validity is re-established at emission by `countMatch` +
the window guards), so panic-checked `[..]!` access on it is wasted work in the
two hottest matcher loops (the chain walk and the per-match hash insertion).

`chainWalkFast`/`updateHashesFast` are byte-for-byte copies of
`lz77Chain.chainWalk`/`lz77Chain.updateHashes` with `[..]!` replaced by
proven-bounds `[..]`, taking a single array-size hypothesis that, once
established, discharges every access inside the loop statically. The `*Guarded`
wrappers establish that hypothesis with one runtime comparison per *outer*
iteration (amortised over the whole inner loop) and fall back to the original
panic-checked function when it cannot be shown — so they share the original's
exact signature and are provably equal to it (`*Guarded_eq` in
`LZ77ChainCorrect`). The iterative matchers call the wrappers; the recursive
reference versions and all their proofs are untouched. -/

/-- Proven-bounds copy of `lz77Chain.chainWalk`: `prev[cand]` is in range because
    the walk guard gives `cand < pos` and `hps : pos ≤ prev.size`. -/
def chainWalkFast (data : ByteArray) (prev : Array Nat) (windowSize pos maxLen : Nat)
    (hpm : pos + maxLen ≤ data.size) (hps : pos ≤ prev.size)
    (cand fuel bestLen bestPos : Nat) : Nat × Nat :=
  if fuel = 0 then (bestLen, bestPos)
  else if hc : cand < pos ∧ pos - cand ≤ windowSize then
    have hcand : cand + maxLen ≤ data.size := by omega
    let ml := lz77Greedy.countMatch data cand pos maxLen hcand hpm
    let (bl, bp) := if ml > bestLen then (ml, cand) else (bestLen, bestPos)
    if bl ≥ maxLen then (bl, bp)
    else chainWalkFast data prev windowSize pos maxLen hpm hps
      (prev[cand]'(by omega)) (fuel - 1) bl bp
  else (bestLen, bestPos)
termination_by fuel
decreasing_by omega

/-- One runtime `pos ≤ prev.size` check guards the whole `chainWalkFast` inner
    loop; the (unreachable, since `prev` is sized to the input) fallback is the
    original panic-checked walk, so this equals `lz77Chain.chainWalk`. -/
@[inline] def chainWalkGuarded (data : ByteArray) (prev : Array Nat)
    (windowSize pos maxLen : Nat) (hpm : pos + maxLen ≤ data.size)
    (cand fuel bestLen bestPos : Nat) : Nat × Nat :=
  if hps : pos ≤ prev.size then
    chainWalkFast data prev windowSize pos maxLen hpm hps cand fuel bestLen bestPos
  else
    lz77Chain.chainWalk data prev windowSize pos maxLen hpm cand fuel bestLen bestPos

/-- Proven-bounds copy of `lz77Chain.updateHashes`: the bucket index `hsh` is
    `< hashSize ≤ hashTable.size`, so `hashTable[hsh]` needs no runtime check. -/
def updateHashesFast (data : ByteArray) (hashSize : Nat)
    (hashTable prev : Array Nat) (pos j matchLen insertCap : Nat)
    (hhs : 0 < hashSize) (hht : hashSize ≤ hashTable.size) : Array Nat × Array Nat :=
  if j < matchLen ∧ j ≤ insertCap then
    if h : pos + j + 2 < data.size then
      let hsh := lz77Greedy.hash3 data (pos + j) hashSize h
      have hb : hsh < hashTable.size := by
        have : hsh < hashSize := Nat.mod_lt _ hhs
        omega
      let head := hashTable[hsh]'hb
      updateHashesFast data hashSize (hashTable.set! hsh (pos + j)) (prev.set! (pos + j) head)
        pos (j + 1) matchLen insertCap hhs (by simpa using hht)
    else
      updateHashesFast data hashSize hashTable prev pos (j + 1) matchLen insertCap hhs hht
  else (hashTable, prev)
termination_by matchLen - j
decreasing_by all_goals omega

/-- One runtime `0 < hashSize ∧ hashSize ≤ hashTable.size` check guards the whole
    `updateHashesFast` insertion loop; the fallback is the original panic-checked
    insertion, so this equals `lz77Chain.updateHashes`. -/
@[inline] def updateHashesGuarded (data : ByteArray) (hashSize : Nat)
    (hashTable prev : Array Nat) (pos j matchLen insertCap : Nat) : Array Nat × Array Nat :=
  if hu : 0 < hashSize ∧ hashSize ≤ hashTable.size then
    updateHashesFast data hashSize hashTable prev pos j matchLen insertCap hu.1 hu.2
  else
    lz77Chain.updateHashes data hashSize hashTable prev pos j matchLen insertCap

/-- Iterative (tail-recursive, `Array`-accumulating) version of `lz77Chain`.
    Same output, but does not overflow the stack on large inputs. Reuses
    `lz77Chain`'s `chainWalk`/`updateHashes` (which accumulate into arrays, not
    tokens) and `lz77GreedyIter.trailing`; only the token-emitting `mainLoop`
    differs (push vs. cons). Proven equal to `lz77Chain` in `LZ77ChainCorrect`. -/
def lz77ChainIter (data : ByteArray) (maxChain : Nat) (windowSize : Nat := 32768)
    (insertCap : Nat := 1000000000) :
    Array LZ77Token :=
  if data.size < 3 then
    lz77GreedyIter.trailing data 0 #[]
  else
    let hashSize := 65536
    mainLoop data windowSize hashSize maxChain insertCap
      (.replicate hashSize data.size) (.replicate data.size data.size) 0 #[]
where
  mainLoop (data : ByteArray) (windowSize hashSize maxChain insertCap : Nat)
      (hashTable prev : Array Nat) (pos : Nat) (acc : Array LZ77Token) :
      Array LZ77Token :=
    if hlt : pos + 2 < data.size then
      let h := lz77Greedy.hash3 data pos hashSize hlt
      let (head, hashTable, prev) := headInsertGuarded hashTable prev h pos
      let maxLen := min 258 (data.size - pos)
      have hmaxLenP : pos + maxLen ≤ data.size := by omega
      let (matchLen, matchPos) :=
        chainWalkGuarded data prev windowSize pos maxLen hmaxLenP head maxChain 0 0
      if hge : matchLen ≥ 3 then
        if hle : pos + matchLen ≤ data.size then
          have : data.size - (pos + matchLen) < data.size - pos := by omega
          let (hashTable, prev) :=
            updateHashesGuarded data hashSize hashTable prev pos 1 matchLen insertCap
          mainLoop data windowSize hashSize maxChain insertCap hashTable prev (pos + matchLen)
            (acc.push (.reference matchLen (pos - matchPos)))
        else
          mainLoop data windowSize hashSize maxChain insertCap hashTable prev (pos + 1)
            (acc.push (.literal (data[pos]'(by omega))))
      else
        mainLoop data windowSize hashSize maxChain insertCap hashTable prev (pos + 1)
          (acc.push (.literal (data[pos]'(by omega))))
    else
      lz77GreedyIter.trailing data pos acc
  termination_by data.size - pos
  decreasing_by all_goals omega

/-- Lazy (one-byte-lookahead, zlib `deflate_slow`-style) variant of `lz77Chain`.
    At each position it finds the best chain match `M` at `pos`; before emitting it
    runs a *second* `chainWalk` at `pos+1` for `M'`. It defers — emits a literal at
    `pos` and takes `M'` (advancing to `pos+1+len M'`) — only when `M'` is **both
    longer and no farther** than `M` (`len M' > len M ∧ dist M' ≤ dist M`); otherwise
    it emits `M` (advancing to `pos+len M`). The distance guard is the key to the
    ratio win: a length-only deferral takes longer-but-farther matches whose extra
    distance bits cost more than they save, which *regresses* large text badly
    (measured: plrabn12/lcet10 up to +22%); guarding on distance keeps only the
    beneficial deferrals (Canterbury levels 4–9: −5.2% vs greedy). It is not a
    global optimum — `lcet10` at the shallow levels 4–5 still loses ~19% to a
    Huffman-distribution effect no *local* deferral rule captures (that needs the
    cost-model parse of #2526 part 2).

    Match-finding stays opaque to correctness — `chainWalk_spec` holds for *any*
    chain state and *any* deferral predicate, so validity is re-established at
    emission exactly as for `lz77Chain`. `pos+1` is intentionally *not* inserted
    before the lookahead walk (you cannot match a position against itself; matches
    zlib, and is correctness-irrelevant). Reuses `lz77Chain`'s `chainWalk`/
    `updateHashes` and `lz77Greedy.trailing`. Equal-quality contracts proven in
    `LZ77ChainLazyCorrect`. -/
def lz77ChainLazy (data : ByteArray) (maxChain : Nat) (windowSize : Nat := 32768)
    (insertCap : Nat := 1000000000) :
    Array LZ77Token :=
  if data.size < 3 then
    (lz77Greedy.trailing data 0).toArray
  else
    let hashSize := 65536
    (mainLoop data windowSize hashSize maxChain
      (.replicate hashSize data.size) (.replicate data.size data.size) 0 insertCap).toArray
where
  mainLoop (data : ByteArray) (windowSize hashSize maxChain : Nat)
      (hashTable prev : Array Nat) (pos insertCap : Nat) : List LZ77Token :=
    if hlt : pos + 2 < data.size then
      let h := lz77Greedy.hash3 data pos hashSize hlt
      let (head, hashTable, prev) := headInsertGuarded hashTable prev h pos
      let maxLen := min 258 (data.size - pos)
      have hmaxLenP : pos + maxLen ≤ data.size := by omega
      let (matchLen, matchPos) :=
        lz77Chain.chainWalk data prev windowSize pos maxLen hmaxLenP head maxChain 0 0
      if hge : matchLen ≥ 3 then
        if hle : pos + matchLen ≤ data.size then
          -- Lazy: probe pos+1 for a longer, no-farther match (distance-guarded deferral)
          if h3lt : pos + 3 < data.size then
            let h2 := lz77Greedy.hash3 data (pos + 1) hashSize (by omega)
            let head2 := headProbeGuarded hashTable h2
            let maxLen2 := min 258 (data.size - (pos + 1))
            have hmaxLen2P : (pos + 1) + maxLen2 ≤ data.size := by omega
            let (matchLen2, matchPos2) :=
              lz77Chain.chainWalk data prev windowSize (pos + 1) maxLen2 hmaxLen2P head2 maxChain 0 0
            if matchLen2 > matchLen ∧ pos + 1 - matchPos2 ≤ pos - matchPos then
              if hle2 : pos + 1 + matchLen2 ≤ data.size then
                -- Longer & no-farther match at pos+1: emit literal at pos + reference at pos+1
                have : data.size - (pos + 1 + matchLen2) < data.size - pos := by omega
                let (hashTable, prev) :=
                  lz77Chain.updateHashes data hashSize hashTable prev pos 1 (matchLen2 + 1) insertCap
                .literal (data[pos]'(by omega)) ::
                  .reference matchLen2 (pos + 1 - matchPos2) ::
                  mainLoop data windowSize hashSize maxChain hashTable prev (pos + 1 + matchLen2) insertCap
              else
                -- matchLen2 spills past data: keep match at pos
                have : data.size - (pos + matchLen) < data.size - pos := by omega
                let (hashTable, prev) :=
                  lz77Chain.updateHashes data hashSize hashTable prev pos 1 matchLen insertCap
                .reference matchLen (pos - matchPos) ::
                  mainLoop data windowSize hashSize maxChain hashTable prev (pos + matchLen) insertCap
            else
              -- No better match at pos+1: keep match at pos
              have : data.size - (pos + matchLen) < data.size - pos := by omega
              let (hashTable, prev) :=
                lz77Chain.updateHashes data hashSize hashTable prev pos 1 matchLen insertCap
              .reference matchLen (pos - matchPos) ::
                mainLoop data windowSize hashSize maxChain hashTable prev (pos + matchLen) insertCap
          else
            -- Near end of data: keep match at pos
            have : data.size - (pos + matchLen) < data.size - pos := by omega
            .reference matchLen (pos - matchPos) ::
              mainLoop data windowSize hashSize maxChain hashTable prev (pos + matchLen) insertCap
        else
          .literal (data[pos]'(by omega)) ::
            mainLoop data windowSize hashSize maxChain hashTable prev (pos + 1) insertCap
      else
        .literal (data[pos]'(by omega)) ::
          mainLoop data windowSize hashSize maxChain hashTable prev (pos + 1) insertCap
    else
      lz77Greedy.trailing data pos
  termination_by data.size - pos
  decreasing_by all_goals omega

/-- Iterative (tail-recursive, `Array`-accumulating) version of `lz77ChainLazy`.
    Same output, no stack overflow on large inputs. Reuses `lz77Chain`'s
    `chainWalk`/`updateHashes` and `lz77GreedyIter.trailing`; only the
    token-emitting `mainLoop` differs (push vs. cons). Proven equal to
    `lz77ChainLazy` in `LZ77ChainLazyCorrect`. -/
def lz77ChainLazyIter (data : ByteArray) (maxChain : Nat) (windowSize : Nat := 32768)
    (insertCap : Nat := 1000000000) :
    Array LZ77Token :=
  if data.size < 3 then
    lz77GreedyIter.trailing data 0 #[]
  else
    let hashSize := 65536
    mainLoop data windowSize hashSize maxChain insertCap
      (.replicate hashSize data.size) (.replicate data.size data.size) 0 #[]
where
  mainLoop (data : ByteArray) (windowSize hashSize maxChain insertCap : Nat)
      (hashTable prev : Array Nat) (pos : Nat) (acc : Array LZ77Token) :
      Array LZ77Token :=
    if hlt : pos + 2 < data.size then
      let h := lz77Greedy.hash3 data pos hashSize hlt
      let (head, hashTable, prev) := headInsertGuarded hashTable prev h pos
      let maxLen := min 258 (data.size - pos)
      have hmaxLenP : pos + maxLen ≤ data.size := by omega
      let (matchLen, matchPos) :=
        chainWalkGuarded data prev windowSize pos maxLen hmaxLenP head maxChain 0 0
      if hge : matchLen ≥ 3 then
        if hle : pos + matchLen ≤ data.size then
          if h3lt : pos + 3 < data.size then
            let h2 := lz77Greedy.hash3 data (pos + 1) hashSize (by omega)
            let head2 := headProbeGuarded hashTable h2
            let maxLen2 := min 258 (data.size - (pos + 1))
            have hmaxLen2P : (pos + 1) + maxLen2 ≤ data.size := by omega
            let (matchLen2, matchPos2) :=
              chainWalkGuarded data prev windowSize (pos + 1) maxLen2 hmaxLen2P head2 maxChain 0 0
            if matchLen2 > matchLen ∧ pos + 1 - matchPos2 ≤ pos - matchPos then
              if hle2 : pos + 1 + matchLen2 ≤ data.size then
                have : data.size - (pos + 1 + matchLen2) < data.size - pos := by omega
                let (hashTable, prev) :=
                  updateHashesGuarded data hashSize hashTable prev pos 1 (matchLen2 + 1) insertCap
                mainLoop data windowSize hashSize maxChain insertCap hashTable prev (pos + 1 + matchLen2)
                  (acc.push (.literal (data[pos]'(by omega))) |>.push
                    (.reference matchLen2 (pos + 1 - matchPos2)))
              else
                have : data.size - (pos + matchLen) < data.size - pos := by omega
                let (hashTable, prev) :=
                  updateHashesGuarded data hashSize hashTable prev pos 1 matchLen insertCap
                mainLoop data windowSize hashSize maxChain insertCap hashTable prev (pos + matchLen)
                  (acc.push (.reference matchLen (pos - matchPos)))
            else
              have : data.size - (pos + matchLen) < data.size - pos := by omega
              let (hashTable, prev) :=
                updateHashesGuarded data hashSize hashTable prev pos 1 matchLen insertCap
              mainLoop data windowSize hashSize maxChain insertCap hashTable prev (pos + matchLen)
                (acc.push (.reference matchLen (pos - matchPos)))
          else
            have : data.size - (pos + matchLen) < data.size - pos := by omega
            mainLoop data windowSize hashSize maxChain insertCap hashTable prev (pos + matchLen)
              (acc.push (.reference matchLen (pos - matchPos)))
        else
          mainLoop data windowSize hashSize maxChain insertCap hashTable prev (pos + 1)
            (acc.push (.literal (data[pos]'(by omega))))
      else
        mainLoop data windowSize hashSize maxChain insertCap hashTable prev (pos + 1)
          (acc.push (.literal (data[pos]'(by omega))))
    else
      lz77GreedyIter.trailing data pos acc
  termination_by data.size - pos
  decreasing_by all_goals omega

/-! ## Packed-token matcher twins (Wave 3b stage A)

`lz77ChainIterP`/`lz77ChainLazyIterP` are copies of the iterative matchers
whose accumulator holds `packTok`-encoded `UInt32`s instead of boxed
`LZ77Token`s. The chain state (`hashTable`/`prev : Array Nat`) is untouched
(the Wave-3a verdict: a `UInt32` chain state measured slower); only the
emission side changes, and each push is literally `packTok` of the token the
boxed loop pushes, so `Zip/Spec/LZ77PackedCorrect.lean` proves them equal to
`(·.map packTok)` of the boxed matchers by lockstep induction. -/

/-- Packed-token form of `lz77GreedyIter.trailing`: pushes
    `packTok (.literal _)` for each remaining byte. -/
def trailingP (data : ByteArray) (pos : Nat) (acc : Array UInt32) : Array UInt32 :=
  if h : pos < data.size then
    trailingP data (pos + 1) (acc.push (packTok (.literal data[pos])))
  else acc
termination_by data.size - pos

/-- Packed-token twin of `lz77ChainIter` (greedy hash-chain matcher):
    identical control flow and chain state, `Array UInt32` accumulator.
    Equal to `(lz77ChainIter ..).map packTok` (`lz77ChainIterP_eq`). -/
def lz77ChainIterP (data : ByteArray) (maxChain : Nat) (windowSize : Nat := 32768)
    (insertCap : Nat := 1000000000) :
    Array UInt32 :=
  if data.size < 3 then
    trailingP data 0 #[]
  else
    let hashSize := 65536
    mainLoop data windowSize hashSize maxChain insertCap
      (.replicate hashSize data.size) (.replicate data.size data.size) 0 #[]
where
  mainLoop (data : ByteArray) (windowSize hashSize maxChain insertCap : Nat)
      (hashTable prev : Array Nat) (pos : Nat) (acc : Array UInt32) :
      Array UInt32 :=
    if hlt : pos + 2 < data.size then
      let h := lz77Greedy.hash3 data pos hashSize hlt
      let (head, hashTable, prev) := headInsertGuarded hashTable prev h pos
      let maxLen := min 258 (data.size - pos)
      have hmaxLenP : pos + maxLen ≤ data.size := by omega
      let (matchLen, matchPos) :=
        chainWalkGuarded data prev windowSize pos maxLen hmaxLenP head maxChain 0 0
      if hge : matchLen ≥ 3 then
        if hle : pos + matchLen ≤ data.size then
          have : data.size - (pos + matchLen) < data.size - pos := by omega
          let (hashTable, prev) :=
            updateHashesGuarded data hashSize hashTable prev pos 1 matchLen insertCap
          mainLoop data windowSize hashSize maxChain insertCap hashTable prev (pos + matchLen)
            (acc.push (packTok (.reference matchLen (pos - matchPos))))
        else
          mainLoop data windowSize hashSize maxChain insertCap hashTable prev (pos + 1)
            (acc.push (packTok (.literal (data[pos]'(by omega)))))
      else
        mainLoop data windowSize hashSize maxChain insertCap hashTable prev (pos + 1)
          (acc.push (packTok (.literal (data[pos]'(by omega)))))
    else
      trailingP data pos acc
  termination_by data.size - pos
  decreasing_by all_goals omega

/-- Packed-token twin of `lz77ChainLazyIter` (lazy one-byte-lookahead matcher):
    identical control flow and chain state, `Array UInt32` accumulator.
    Equal to `(lz77ChainLazyIter ..).map packTok` (`lz77ChainLazyIterP_eq`). -/
def lz77ChainLazyIterP (data : ByteArray) (maxChain : Nat) (windowSize : Nat := 32768)
    (insertCap : Nat := 1000000000) :
    Array UInt32 :=
  if data.size < 3 then
    trailingP data 0 #[]
  else
    let hashSize := 65536
    mainLoop data windowSize hashSize maxChain insertCap
      (.replicate hashSize data.size) (.replicate data.size data.size) 0 #[]
where
  mainLoop (data : ByteArray) (windowSize hashSize maxChain insertCap : Nat)
      (hashTable prev : Array Nat) (pos : Nat) (acc : Array UInt32) :
      Array UInt32 :=
    if hlt : pos + 2 < data.size then
      let h := lz77Greedy.hash3 data pos hashSize hlt
      let (head, hashTable, prev) := headInsertGuarded hashTable prev h pos
      let maxLen := min 258 (data.size - pos)
      have hmaxLenP : pos + maxLen ≤ data.size := by omega
      let (matchLen, matchPos) :=
        chainWalkGuarded data prev windowSize pos maxLen hmaxLenP head maxChain 0 0
      if hge : matchLen ≥ 3 then
        if hle : pos + matchLen ≤ data.size then
          if h3lt : pos + 3 < data.size then
            let h2 := lz77Greedy.hash3 data (pos + 1) hashSize (by omega)
            let head2 := headProbeGuarded hashTable h2
            let maxLen2 := min 258 (data.size - (pos + 1))
            have hmaxLen2P : (pos + 1) + maxLen2 ≤ data.size := by omega
            let (matchLen2, matchPos2) :=
              chainWalkGuarded data prev windowSize (pos + 1) maxLen2 hmaxLen2P head2 maxChain 0 0
            if matchLen2 > matchLen ∧ pos + 1 - matchPos2 ≤ pos - matchPos then
              if hle2 : pos + 1 + matchLen2 ≤ data.size then
                have : data.size - (pos + 1 + matchLen2) < data.size - pos := by omega
                let (hashTable, prev) :=
                  updateHashesGuarded data hashSize hashTable prev pos 1 (matchLen2 + 1) insertCap
                mainLoop data windowSize hashSize maxChain insertCap hashTable prev (pos + 1 + matchLen2)
                  (acc.push (packTok (.literal (data[pos]'(by omega)))) |>.push
                    (packTok (.reference matchLen2 (pos + 1 - matchPos2))))
              else
                have : data.size - (pos + matchLen) < data.size - pos := by omega
                let (hashTable, prev) :=
                  updateHashesGuarded data hashSize hashTable prev pos 1 matchLen insertCap
                mainLoop data windowSize hashSize maxChain insertCap hashTable prev (pos + matchLen)
                  (acc.push (packTok (.reference matchLen (pos - matchPos))))
            else
              have : data.size - (pos + matchLen) < data.size - pos := by omega
              let (hashTable, prev) :=
                updateHashesGuarded data hashSize hashTable prev pos 1 matchLen insertCap
              mainLoop data windowSize hashSize maxChain insertCap hashTable prev (pos + matchLen)
                (acc.push (packTok (.reference matchLen (pos - matchPos))))
          else
            have : data.size - (pos + matchLen) < data.size - pos := by omega
            mainLoop data windowSize hashSize maxChain insertCap hashTable prev (pos + matchLen)
              (acc.push (packTok (.reference matchLen (pos - matchPos))))
        else
          mainLoop data windowSize hashSize maxChain insertCap hashTable prev (pos + 1)
            (acc.push (packTok (.literal (data[pos]'(by omega)))))
      else
        mainLoop data windowSize hashSize maxChain insertCap hashTable prev (pos + 1)
          (acc.push (packTok (.literal (data[pos]'(by omega)))))
    else
      trailingP data pos acc
  termination_by data.size - pos
  decreasing_by all_goals omega

/-- Emit LZ77 tokens as fixed Huffman codes into a BitWriter. -/
def emitTokens (bw : BitWriter) (tokens : Array LZ77Token) (i : Nat) : BitWriter :=
  if h : i < tokens.size then
    match tokens[i] with
    | .literal b =>
      have : b.toNat < fixedLitCodes.size := by
        have := UInt8.toNat_lt b; rw [Deflate.fixedLitCodes_size]; omega
      let (code, len) := fixedLitCodes[b.toNat]
      emitTokens (bw.writeHuffCode code len) tokens (i + 1)
    | .reference length distance =>
      match findLengthCode length with
      | some (idx, extraCount, extraVal) =>
        if hlit : idx + 257 < fixedLitCodes.size then
          let (code, len) := fixedLitCodes[idx + 257]
          let bw := bw.writeHuffCode code len
          let bw := bw.writeBits extraCount extraVal
          match findDistCode distance with
          | some (dIdx, dExtraCount, dExtraVal) =>
            if hdist : dIdx < fixedDistCodes.size then
              let (dCode, dLen) := fixedDistCodes[dIdx]
              let bw := bw.writeHuffCode dCode dLen
              emitTokens (bw.writeBits dExtraCount dExtraVal) tokens (i + 1)
            else emitTokens bw tokens (i + 1)
          | none => emitTokens bw tokens (i + 1)
        else emitTokens bw tokens (i + 1)
      | none => emitTokens bw tokens (i + 1)
  else bw
termination_by tokens.size - i

/-! ## Packed-token fixed-code emission (Wave 3b stage C)

`emitTokensP` walks the `packTok`-encoded `UInt32` stream directly, so the
fixed-code emit path never materializes boxed `LZ77Token`s. The reference
arm lives in the non-recursive helper `emitRefFixedP`, whose field reads
and `findLengthCode`/`findDistCode` matches are the *exact* bit expressions
of `unpackTok`'s reference view; the loop body contains only a plain helper
application. As with `tokenFreqsP` (see the landmine note in
`Zip/Native/DeflateFreqs.lean`), that shape is load-bearing: a match
scrutinee over `findLengthCode` applied to a stuck bit-extracted word in a
well-founded-recursion body sends definition-time `whnf` into
`findTableCode`'s `WellFounded` fix, which does not terminate in practical
time. Do not inline `emitRefFixedP` back into `emitTokensP`.
`Zip/Spec/EmitPackedCorrect.lean` proves
`emitTokensP bw ws i = emitTokens bw (ws.map unpackTok) i`. -/

/-- Emit one packed *reference* token (tag bit set) as fixed Huffman codes:
    decode the length/distance fields with `unpackTok`'s bit expressions and
    write exactly the `writeHuffCode`/`writeBits` sequence of `emitTokens`'s
    reference arm (including its dead-code `else` fallbacks, so the equality
    proof in `Zip/Spec/EmitPackedCorrect.lean` aligns branch-for-branch). -/
@[inline] def emitRefFixedP (bw : BitWriter) (w : UInt32) : BitWriter :=
  match findLengthCode (((w >>> 16) &&& 0x7FFF).toNat) with
  | some (idx, extraCount, extraVal) =>
    if hlit : idx + 257 < fixedLitCodes.size then
      let (code, len) := fixedLitCodes[idx + 257]
      let bw := bw.writeHuffCode code len
      let bw := bw.writeBits extraCount extraVal
      match findDistCode ((w &&& 0xFFFF).toNat) with
      | some (dIdx, dExtraCount, dExtraVal) =>
        if hdist : dIdx < fixedDistCodes.size then
          let (dCode, dLen) := fixedDistCodes[dIdx]
          let bw := bw.writeHuffCode dCode dLen
          bw.writeBits dExtraCount dExtraVal
        else bw
      | none => bw
    else bw
  | none => bw

/-- Packed-token form of `emitTokens`: emit the packed `UInt32` stream as
    fixed Huffman codes. Literals (tag bit clear) read the byte field
    directly; references go through `emitRefFixedP`. Equal to `emitTokens`
    over the boxed view for every word array (`emitTokensP_eq`). -/
def emitTokensP (bw : BitWriter) (tokens : Array UInt32) (i : Nat) : BitWriter :=
  if h : i < tokens.size then
    let w := tokens[i]
    if w &&& ((1 : UInt32) <<< 31) = 0 then
      have : w.toUInt8.toNat < fixedLitCodes.size := by
        have := UInt8.toNat_lt w.toUInt8; rw [Deflate.fixedLitCodes_size]; omega
      let (code, len) := fixedLitCodes[w.toUInt8.toNat]
      emitTokensP (bw.writeHuffCode code len) tokens (i + 1)
    else
      emitTokensP (emitRefFixedP bw w) tokens (i + 1)
  else bw
termination_by tokens.size - i

/-- Write a fixed Huffman DEFLATE block from LZ77 tokens. -/
def deflateFixedBlock (data : ByteArray) (tokens : Array LZ77Token) : ByteArray :=
  let bw := BitWriter.empty
  let bw := bw.writeBits 1 1  -- BFINAL
  let bw := bw.writeBits 2 1  -- BTYPE = 01
  have h256 : 256 < fixedLitCodes.size := by rw [Deflate.fixedLitCodes_size]; omega
  if data.size == 0 then
    let (code, len) := fixedLitCodes[256]
    let bw := bw.writeHuffCode code len
    bw.flush
  else
    let bw := emitTokens bw tokens 0
    let (code, len) := fixedLitCodes[256]
    let bw := bw.writeHuffCode code len
    bw.flush

/-- Packed-token form of `deflateFixedBlock` (Wave 3b stage C): write a
    fixed Huffman DEFLATE block directly from the packed `UInt32` stream —
    same body with `emitTokensP` in place of `emitTokens`. Equal to
    `deflateFixedBlock` over the boxed view (`deflateFixedBlockP_eq` in
    `Zip/Spec/EmitPackedCorrect.lean`). -/
def deflateFixedBlockP (data : ByteArray) (tokens : Array UInt32) : ByteArray :=
  let bw := BitWriter.empty
  let bw := bw.writeBits 1 1  -- BFINAL
  let bw := bw.writeBits 2 1  -- BTYPE = 01
  have h256 : 256 < fixedLitCodes.size := by rw [Deflate.fixedLitCodes_size]; omega
  if data.size == 0 then
    let (code, len) := fixedLitCodes[256]
    let bw := bw.writeHuffCode code len
    bw.flush
  else
    let bw := emitTokensP bw tokens 0
    let (code, len) := fixedLitCodes[256]
    let bw := bw.writeHuffCode code len
    bw.flush

/-- Compress data using fixed Huffman codes and greedy LZ77 (Level 1).
    Produces a single DEFLATE block with BFINAL=1, BTYPE=01. -/
def deflateFixed (data : ByteArray) : ByteArray :=
  Deflate.deflateFixedBlock data (lz77Greedy data)

/-- Compress data using fixed Huffman codes and iterative greedy LZ77.
    Equivalent to `deflateFixed` but does not overflow the stack on large inputs. -/
def deflateFixedIter (data : ByteArray) : ByteArray :=
  deflateFixedBlock data (lz77GreedyIter data)

/-- Simple hash-based lazy LZ77 matcher.
    Like `lz77Greedy`, but checks if position pos+1 has a longer match
    before committing. If so, emits a literal for pos and the longer
    match at pos+1. -/
def lz77Lazy (data : ByteArray) (windowSize : Nat := 32768) :
    Array LZ77Token :=
  if data.size < 3 then
    (trailing data 0).toArray
  else
    let hashSize := 65536
    (mainLoop data windowSize hashSize
      (.replicate hashSize 0) (.replicate hashSize false) 0).toArray
where
  @[inline] hash3 (data : ByteArray) (pos : Nat) (hashSize : Nat)
      (h : pos + 2 < data.size) : Nat :=
    -- Hash arithmetic in `UInt32` (single machine ops) rather than `Nat`
    -- (whose bitwise XOR/shift are slow); `.toNat % hashSize` keeps the exact
    -- same index, so `hash3_eq` stays `rfl` and the `< hashSize` bound holds.
    let a := (data[pos]'(by omega)).toUInt32
    let b := (data[pos + 1]'(by omega)).toUInt32
    let c := (data[pos + 2]'(by omega)).toUInt32
    ((a ^^^ (b <<< 5) ^^^ (c <<< 10)).toNat % hashSize)
  countMatch (data : ByteArray) (p1 p2 maxLen : Nat)
      (h1 : p1 + maxLen ≤ data.size) (h2 : p2 + maxLen ≤ data.size) : Nat :=
    go data p1 p2 0 maxLen h1 h2
  go (data : ByteArray) (p1 p2 i maxLen : Nat)
      (h1 : p1 + maxLen ≤ data.size) (h2 : p2 + maxLen ≤ data.size) : Nat :=
    if hi : i < maxLen then
      if (data[p1 + i]'(by omega)) == (data[p2 + i]'(by omega)) then
        go data p1 p2 (i + 1) maxLen h1 h2
      else i
    else i
  termination_by maxLen - i
  trailing (data : ByteArray) (pos : Nat) : List LZ77Token :=
    if h : pos < data.size then
      .literal (data[pos]'h) :: trailing data (pos + 1)
    else []
  termination_by data.size - pos
  updateHashes (data : ByteArray) (hashSize : Nat)
      (hashTable : Array Nat) (hashValid : Array Bool)
      (pos j matchLen : Nat) : Array Nat × Array Bool :=
    if j < matchLen then
      if h : pos + j + 2 < data.size then
        let hsh := hash3 data (pos + j) hashSize h
        updateHashes data hashSize (hashTable.set! hsh (pos + j))
          (hashValid.set! hsh true) pos (j + 1) matchLen
      else
        updateHashes data hashSize hashTable hashValid pos (j + 1) matchLen
    else
      (hashTable, hashValid)
  termination_by matchLen - j
  mainLoop (data : ByteArray) (windowSize hashSize : Nat)
      (hashTable : Array Nat) (hashValid : Array Bool) (pos : Nat) :
      List LZ77Token :=
    if hlt : pos + 2 < data.size then
      let h := hash3 data pos hashSize hlt
      if hht : h < hashTable.size then
        if hhv : h < hashValid.size then
          let matchPos := hashTable[h]
          let isValid := hashValid[h]
          let hashTable := hashTable.set! h pos
          let hashValid := hashValid.set! h true
          if hcond : isValid ∧ matchPos < pos ∧ pos - matchPos ≤ windowSize then
            have hmp : matchPos < pos := hcond.2.1
            let maxLen := min 258 (data.size - pos)
            have hmaxLenP : pos + maxLen ≤ data.size := by omega
            have hmaxLenM : matchPos + maxLen ≤ data.size := by omega
            let matchLen := countMatch data matchPos pos maxLen hmaxLenM hmaxLenP
            if hge : matchLen ≥ 3 then
              if hle : pos + matchLen ≤ data.size then
                -- Lazy: check pos + 1 for a longer match
                if h3lt : pos + 3 < data.size then
                  let h2 := hash3 data (pos + 1) hashSize (by omega)
                  if hht2 : h2 < hashTable.size then
                    if hhv2 : h2 < hashValid.size then
                      let matchPos2 := hashTable[h2]
                      let isValid2 := hashValid[h2]
                      if hcond2 :
                          isValid2 ∧ matchPos2 < pos + 1 ∧ pos + 1 - matchPos2 ≤ windowSize then
                        have hmp2 : matchPos2 < pos + 1 := hcond2.2.1
                        let maxLen2 := min 258 (data.size - (pos + 1))
                        have hmaxLen2P : (pos + 1) + maxLen2 ≤ data.size := by omega
                        have hmaxLen2M : matchPos2 + maxLen2 ≤ data.size := by omega
                        let matchLen2 :=
                          countMatch data matchPos2 (pos + 1) maxLen2 hmaxLen2M hmaxLen2P
                        if matchLen2 > matchLen then
                          if hle2 : pos + 1 + matchLen2 ≤ data.size then
                            -- Better match at pos+1: emit literal + reference
                            have : data.size - (pos + 1 + matchLen2) < data.size - pos := by omega
                            let (ht, hv) :=
                              updateHashes data hashSize hashTable hashValid pos 1 matchLen2
                            .literal (data[pos]'(by omega)) ::
                              .reference matchLen2 (pos + 1 - matchPos2) ::
                              mainLoop data windowSize hashSize ht hv (pos + 1 + matchLen2)
                          else
                            -- matchLen2 exceeds data: fall back to match at pos
                            have : data.size - (pos + matchLen) < data.size - pos := by omega
                            let (ht, hv) :=
                              updateHashes data hashSize hashTable hashValid pos 1 matchLen
                            .reference matchLen (pos - matchPos) ::
                              mainLoop data windowSize hashSize ht hv (pos + matchLen)
                        else
                          -- Keep match at pos (no better match at pos+1)
                          have : data.size - (pos + matchLen) < data.size - pos := by omega
                          let (ht, hv) :=
                            updateHashes data hashSize hashTable hashValid pos 1 matchLen
                          .reference matchLen (pos - matchPos) ::
                            mainLoop data windowSize hashSize ht hv (pos + matchLen)
                      else
                        -- No valid match at pos+1: keep match at pos
                        have : data.size - (pos + matchLen) < data.size - pos := by omega
                        let (ht, hv) :=
                          updateHashes data hashSize hashTable hashValid pos 1 matchLen
                        .reference matchLen (pos - matchPos) ::
                          mainLoop data windowSize hashSize ht hv (pos + matchLen)
                    else
                      -- h2 out of range for hashValid (dead, preserves the
                      -- `hashValid[h2]! = false` fallthrough): keep match at pos
                      have : data.size - (pos + matchLen) < data.size - pos := by omega
                      let (ht, hv) :=
                        updateHashes data hashSize hashTable hashValid pos 1 matchLen
                      .reference matchLen (pos - matchPos) ::
                        mainLoop data windowSize hashSize ht hv (pos + matchLen)
                  else
                    -- h2 out of range for hashTable (dead, preserves the
                    -- `hashTable[h2]! = 0` + `hashValid[h2]! = false` fallthrough):
                    -- keep match at pos
                    have : data.size - (pos + matchLen) < data.size - pos := by omega
                    let (ht, hv) :=
                      updateHashes data hashSize hashTable hashValid pos 1 matchLen
                    .reference matchLen (pos - matchPos) ::
                      mainLoop data windowSize hashSize ht hv (pos + matchLen)
                else
                  -- Near end of data: keep match at pos
                  have : data.size - (pos + matchLen) < data.size - pos := by omega
                  .reference matchLen (pos - matchPos) ::
                    mainLoop data windowSize hashSize hashTable hashValid (pos + matchLen)
              else
                .literal (data[pos]'(by omega)) ::
                  mainLoop data windowSize hashSize hashTable hashValid (pos + 1)
            else
              .literal (data[pos]'(by omega)) ::
                mainLoop data windowSize hashSize hashTable hashValid (pos + 1)
          else
            .literal (data[pos]'(by omega)) ::
              mainLoop data windowSize hashSize hashTable hashValid (pos + 1)
        else
          .literal (data[pos]'(by omega)) ::
            mainLoop data windowSize hashSize hashTable hashValid (pos + 1)
      else
        .literal (data[pos]'(by omega)) ::
          mainLoop data windowSize hashSize hashTable hashValid (pos + 1)
    else
      trailing data pos
  termination_by data.size - pos
  decreasing_by all_goals omega

/-- Iterative (tail-recursive, Array-accumulating) version of `lz77Lazy`.
    Same output, but does not overflow the stack on large inputs because
    `mainLoop` and `trailing` accumulate into an `Array` parameter instead
    of building a `List` via cons.  The existing `lz77Lazy` is preserved
    unchanged for proofs.

    Reuses `lz77Lazy.hash3`, `lz77Lazy.countMatch`, and `lz77Lazy.updateHashes`
    so that the equivalence proof only needs to handle `mainLoop` and `trailing`. -/
def lz77LazyIter (data : ByteArray) (windowSize : Nat := 32768) :
    Array LZ77Token :=
  if data.size < 3 then
    trailing data 0 #[]
  else
    let hashSize := 65536
    mainLoop data windowSize hashSize
      (.replicate hashSize 0) (.replicate hashSize false) 0 #[]
where
  trailing (data : ByteArray) (pos : Nat) (acc : Array LZ77Token) :
      Array LZ77Token :=
    if h : pos < data.size then
      trailing data (pos + 1) (acc.push (.literal (data[pos]'h)))
    else acc
  termination_by data.size - pos
  mainLoop (data : ByteArray) (windowSize hashSize : Nat)
      (hashTable : Array Nat) (hashValid : Array Bool) (pos : Nat)
      (acc : Array LZ77Token) :
      Array LZ77Token :=
    if hlt : pos + 2 < data.size then
      let hsh := lz77Lazy.hash3 data pos hashSize hlt
      if hht : hsh < hashTable.size then
        if hhv : hsh < hashValid.size then
          let matchPos := hashTable[hsh]
          let isValid := hashValid[hsh]
          let hashTable := hashTable.set! hsh pos
          let hashValid := hashValid.set! hsh true
          if hcond : isValid ∧ matchPos < pos ∧ pos - matchPos ≤ windowSize then
            have hmp : matchPos < pos := hcond.2.1
            let maxLen := min 258 (data.size - pos)
            have hmaxLenP : pos + maxLen ≤ data.size := by omega
            have hmaxLenM : matchPos + maxLen ≤ data.size := by omega
            let matchLen := lz77Lazy.countMatch data matchPos pos maxLen hmaxLenM hmaxLenP
            if hge : matchLen ≥ 3 then
              if hle : pos + matchLen ≤ data.size then
                -- Lazy: check pos + 1 for a longer match
                if h3lt : pos + 3 < data.size then
                  let h2 := lz77Lazy.hash3 data (pos + 1) hashSize (by omega)
                  if hht2 : h2 < hashTable.size then
                    if hhv2 : h2 < hashValid.size then
                      let matchPos2 := hashTable[h2]
                      let isValid2 := hashValid[h2]
                      if hcond2 :
                          isValid2 ∧ matchPos2 < pos + 1 ∧ pos + 1 - matchPos2 ≤ windowSize then
                        have hmp2 : matchPos2 < pos + 1 := hcond2.2.1
                        let maxLen2 := min 258 (data.size - (pos + 1))
                        have hmaxLen2P : (pos + 1) + maxLen2 ≤ data.size := by omega
                        have hmaxLen2M : matchPos2 + maxLen2 ≤ data.size := by omega
                        let matchLen2 :=
                          lz77Lazy.countMatch data matchPos2 (pos + 1) maxLen2 hmaxLen2M hmaxLen2P
                        if matchLen2 > matchLen then
                          if hle2 : pos + 1 + matchLen2 ≤ data.size then
                            -- Better match at pos+1: emit literal + reference
                            have : data.size - (pos + 1 + matchLen2) < data.size - pos := by omega
                            let (ht, hv) := lz77Lazy.updateHashes data hashSize hashTable hashValid pos 1 matchLen2
                            mainLoop data windowSize hashSize ht hv (pos + 1 + matchLen2)
                              (acc.push (.literal (data[pos]'(by omega))) |>.push (.reference matchLen2 (pos + 1 - matchPos2)))
                          else
                            -- matchLen2 exceeds data: fall back to match at pos
                            have : data.size - (pos + matchLen) < data.size - pos := by omega
                            let (ht, hv) := lz77Lazy.updateHashes data hashSize hashTable hashValid pos 1 matchLen
                            mainLoop data windowSize hashSize ht hv (pos + matchLen)
                              (acc.push (.reference matchLen (pos - matchPos)))
                        else
                          -- Keep match at pos (no better match at pos+1)
                          have : data.size - (pos + matchLen) < data.size - pos := by omega
                          let (ht, hv) := lz77Lazy.updateHashes data hashSize hashTable hashValid pos 1 matchLen
                          mainLoop data windowSize hashSize ht hv (pos + matchLen)
                            (acc.push (.reference matchLen (pos - matchPos)))
                      else
                        -- No valid match at pos+1: keep match at pos
                        have : data.size - (pos + matchLen) < data.size - pos := by omega
                        let (ht, hv) := lz77Lazy.updateHashes data hashSize hashTable hashValid pos 1 matchLen
                        mainLoop data windowSize hashSize ht hv (pos + matchLen)
                          (acc.push (.reference matchLen (pos - matchPos)))
                    else
                      -- hashValid guard failed at h2: keep match at pos
                      have : data.size - (pos + matchLen) < data.size - pos := by omega
                      mainLoop data windowSize hashSize hashTable hashValid (pos + matchLen)
                        (acc.push (.reference matchLen (pos - matchPos)))
                  else
                    -- hashTable guard failed at h2: keep match at pos
                    have : data.size - (pos + matchLen) < data.size - pos := by omega
                    mainLoop data windowSize hashSize hashTable hashValid (pos + matchLen)
                      (acc.push (.reference matchLen (pos - matchPos)))
                else
                  -- Near end of data: keep match at pos
                  have : data.size - (pos + matchLen) < data.size - pos := by omega
                  mainLoop data windowSize hashSize hashTable hashValid (pos + matchLen)
                    (acc.push (.reference matchLen (pos - matchPos)))
              else
                mainLoop data windowSize hashSize hashTable hashValid (pos + 1)
                  (acc.push (.literal (data[pos]'(by omega))))
            else
              mainLoop data windowSize hashSize hashTable hashValid (pos + 1)
                (acc.push (.literal (data[pos]'(by omega))))
          else
            mainLoop data windowSize hashSize hashTable hashValid (pos + 1)
              (acc.push (.literal (data[pos]'(by omega))))
        else
          mainLoop data windowSize hashSize hashTable hashValid (pos + 1)
            (acc.push (.literal (data[pos]'(by omega))))
      else
        mainLoop data windowSize hashSize hashTable hashValid (pos + 1)
          (acc.push (.literal (data[pos]'(by omega))))
    else
      trailing data pos acc
  termination_by data.size - pos
  decreasing_by all_goals omega

/-- Compress data using fixed Huffman codes and lazy LZ77 (Level 2).
    Produces a single DEFLATE block with BFINAL=1, BTYPE=01. -/
def deflateLazy (data : ByteArray) : ByteArray :=
  Deflate.deflateFixedBlock data (lz77Lazy data)

/-- Compress data using fixed Huffman codes and iterative lazy LZ77.
    Equivalent to `deflateLazy` but does not overflow the stack on large inputs. -/
def deflateLazyIter (data : ByteArray) : ByteArray :=
  deflateFixedBlock data (lz77LazyIter data)

end Zip.Native.Deflate
