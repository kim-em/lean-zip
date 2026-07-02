import Zip.Native.BitWriter
import Zip.Native.Inflate
import Zip.Native.Wide
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

/-! ## Dense length/distance code tables (Wave 5.0, packed #2623)

`findLengthCode`/`findDistCode` are linear searches through the RFC 1951
base tables, run once or twice per reference token by the frequency pass
and both packed emitters — measured at ~14% of level-1 attributable
samples (track-d W5.P1). `lenCodeWordTab`/`distCodeWordTab` precompute
every answer into dense tables indexed by the value itself (length 0–258,
distance 0–32768).

The original dense tables (Wave 5.0) stored a boxed
`Option (Nat × Nat × UInt32)` per entry, so each lookup was a pointer
chase (`fget` → `obj_tag` → two `ctor_get`s + reference-count traffic).
#2623 packs the `(idx, extraBits, extraVal)` triple into one `UInt32`
(`packCode`: idx bits 0–7 (`< 29`), extraBits bits 8–15 (`≤ 13`),
extraVal bits 16–31 — length extra `< 2^5`, distance extra `< 2^13`, both
well within 16 bits) stored in an `Array UInt32`, so a lookup is one
array read + a `UInt32` unbox + a couple of masks, with **no** boxed
chase. The field accessors `codeIdx`/`codeExtra`/`codeVal` recover the
triple. `findLengthCode`/`findDistCode` always succeed
(`findLengthCode_isSome`/`findDistCode_isSome`), so the in-range table
never holds `none`; `packCode none = 0` only covers the unreachable
out-of-range fallback.

`lenCodeWord`/`distCodeWord` read the packed table for in-range values
and pack the linear-search result otherwise; they are proven **equal** to
`packCode ∘ find*Code` (`lenCodeWord_eq`/`distCodeWord_eq`), the only
content fact being `getElem`-of-`map`-of-`range`, never an evaluation of
the table. The hot consumers (`bumpRef*FreqP`, `emitRefFixedP`,
`emitRefWithCodesP`) read the packed word and bit-extract; the boxed
reference paths stay on the linear search (they are the spec subjects).
Caution (WF landmine, see `Zip/Native/DeflateFreqs.lean`): never let
`whnf`/`decide` evaluate the table terms — the builder applies
`findLengthCode` (a `WellFounded` fix) 259/32769 times at module
initialization. -/

/-- `findTableCode.go` never fails when started in range. -/
private theorem findTableCode_go_isSome {baseTable : Array UInt16} {extraTable : Array UInt8}
    {value i : Nat} {hsize : baseTable.size ≤ extraTable.size} (hi : i < baseTable.size) :
    (findTableCode.go baseTable extraTable value i hsize).isSome := by
  unfold findTableCode.go
  split
  · split
    · simp
    · exact findTableCode_go_isSome (by omega)
  · simp only [hi, ↓reduceDIte, Option.isSome_some]
termination_by baseTable.size - i

/-- The fields `findTableCode.go` returns: `extraN` is the extra-table entry
    at the returned index and `extraV` the offset of `value` past its base. -/
theorem findTableCode_go_fields {baseTable : Array UInt16} {extraTable : Array UInt8}
    {value i idx extraN : Nat} {extraV : UInt32} {hsize : baseTable.size ≤ extraTable.size}
    (h : findTableCode.go baseTable extraTable value i hsize = some (idx, extraN, extraV)) :
    extraN = (extraTable[idx]!).toNat ∧
    extraV = (value - (baseTable[idx]!).toNat).toUInt32 := by
  unfold findTableCode.go at h
  split at h
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h
      subst h1
      rw [getElem!_pos extraTable i (by omega), getElem!_pos baseTable i (by omega)]
      exact ⟨h2.symm, h3.symm⟩
    · exact findTableCode_go_fields h
  · split at h
    · rename_i h2lt
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h
      subst h1
      rw [getElem!_pos extraTable i (by omega), getElem!_pos baseTable i h2lt]
      exact ⟨h2.symm, h3.symm⟩
    · exact nomatch h
termination_by baseTable.size - i

/-- `findLengthCode` always succeeds (the base table is non-empty and the
    search is clamped, RFC 1951 §3.2.5). -/
theorem findLengthCode_isSome (len : Nat) : (findLengthCode len).isSome :=
  findTableCode_go_isSome (by rw [Inflate.lengthBase_size]; omega)

/-- `findDistCode` always succeeds. -/
theorem findDistCode_isSome (dist : Nat) : (findDistCode dist).isSome :=
  findTableCode_go_isSome (by rw [Inflate.distBase_size]; omega)

/-- Pack a `(idx, extraBits, extraVal)` triple into one `UInt32`:
    `idx | extraBits <<< 8 | extraVal <<< 16`. `none` (unreachable in range)
    packs to `0`. -/
@[inline] def packCode : Option (Nat × Nat × UInt32) → UInt32
  | none => 0
  | some (idx, extra, val) => idx.toUInt32 ||| (extra.toUInt32 <<< 8) ||| (val <<< 16)

/-- Code-index field of a packed word (bits 0–7). -/
@[inline] def codeIdx (w : UInt32) : Nat := (w &&& 0xFF).toNat
/-- Extra-bits-count field of a packed word (bits 8–15). -/
@[inline] def codeExtra (w : UInt32) : Nat := ((w >>> 8) &&& 0xFF).toNat
/-- Extra-bits-value field of a packed word (bits 16–31). -/
@[inline] def codeVal (w : UInt32) : UInt32 := w >>> 16

/-- Packed length-code table: entry `len` (0–258) is `packCode (findLengthCode len)`. -/
def lenCodeWordTab : Array UInt32 :=
  (Array.range 259).map (fun len => packCode (findLengthCode len))

/-- Packed distance-code table: entry `dist` (0–32768) is `packCode (findDistCode dist)`. -/
def distCodeWordTab : Array UInt32 :=
  (Array.range 32769).map (fun dist => packCode (findDistCode dist))

@[simp] theorem lenCodeWordTab_size : lenCodeWordTab.size = 259 := by
  simp only [lenCodeWordTab, Array.size_map, Array.size_range]

@[simp] theorem distCodeWordTab_size : distCodeWordTab.size = 32769 := by
  simp only [distCodeWordTab, Array.size_map, Array.size_range]

/-- Table-backed packed length code: one `Array UInt32` read for lengths
    0–258, the packed linear search beyond. -/
@[inline] def lenCodeWord (length : Nat) : UInt32 :=
  if h : length < 259 then lenCodeWordTab[length]'(lenCodeWordTab_size ▸ h)
  else packCode (findLengthCode length)

/-- Table-backed packed distance code: one `Array UInt32` read for distances
    0–32768, the packed linear search beyond. -/
@[inline] def distCodeWord (dist : Nat) : UInt32 :=
  if h : dist < 32769 then distCodeWordTab[dist]'(distCodeWordTab_size ▸ h)
  else packCode (findDistCode dist)

theorem lenCodeWord_eq (length : Nat) :
    lenCodeWord length = packCode (findLengthCode length) := by
  unfold lenCodeWord
  split
  · simp only [lenCodeWordTab, Array.getElem_map, Array.getElem_range]
  · rfl

theorem distCodeWord_eq (dist : Nat) :
    distCodeWord dist = packCode (findDistCode dist) := by
  unfold distCodeWord
  split
  · simp only [distCodeWordTab, Array.getElem_map, Array.getElem_range]
  · rfl

/-- `codeIdx` recovers the index from a packed `some` triple (`idx < 256`). -/
theorem codeIdx_packCode (idx extra : Nat) (val : UInt32)
    (hidx : idx < 256) : codeIdx (packCode (some (idx, extra, val))) = idx := by
  simp only [codeIdx, packCode]
  have hi : idx.toUInt32.toNat = idx := by simp [Nat.toUInt32]; omega
  have hil : idx.toUInt32 < 256 := by rw [UInt32.lt_iff_toNat_lt, hi]; exact hidx
  generalize idx.toUInt32 = i at hi hil ⊢
  generalize extra.toUInt32 = e
  rw [← hi]; congr 1
  bv_decide

/-- `codeExtra` recovers the extra-bit count (`extra < 256`, `idx < 256`). -/
theorem codeExtra_packCode (idx extra : Nat) (val : UInt32)
    (hidx : idx < 256) (hextra : extra < 256) :
    codeExtra (packCode (some (idx, extra, val))) = extra := by
  simp only [codeExtra, packCode]
  have hi : idx.toUInt32.toNat = idx := by simp [Nat.toUInt32]; omega
  have he : extra.toUInt32.toNat = extra := by simp [Nat.toUInt32]; omega
  have hil : idx.toUInt32 < 256 := by rw [UInt32.lt_iff_toNat_lt, hi]; exact hidx
  have hel : extra.toUInt32 < 256 := by rw [UInt32.lt_iff_toNat_lt, he]; exact hextra
  generalize idx.toUInt32 = i at hil ⊢
  generalize extra.toUInt32 = e at he hel ⊢
  rw [← he]; congr 1
  bv_decide

/-- `codeVal` recovers the extra-bit value (`val < 2^16`, `extra < 256`, `idx < 256`). -/
theorem codeVal_packCode (idx extra : Nat) (val : UInt32)
    (hidx : idx < 256) (hextra : extra < 256) (hval : val < 65536) :
    codeVal (packCode (some (idx, extra, val))) = val := by
  simp only [codeVal, packCode]
  have hi : idx.toUInt32.toNat = idx := by simp [Nat.toUInt32]; omega
  have he : extra.toUInt32.toNat = extra := by simp [Nat.toUInt32]; omega
  have hil : idx.toUInt32 < 256 := by rw [UInt32.lt_iff_toNat_lt, hi]; exact hidx
  have hel : extra.toUInt32 < 256 := by rw [UInt32.lt_iff_toNat_lt, he]; exact hextra
  generalize idx.toUInt32 = i at hil ⊢
  generalize extra.toUInt32 = e at hel ⊢
  bv_decide

/-! ## USize-addressability helpers (Wave 7 P1a)

The matcher's `countMatch` byte-compare loop runs in `USize` (one machine
word add + `ByteArray.uget`, no boxed-`Nat` arithmetic or reference-count
traffic per byte — see `lz77Greedy.goU`). These two lemmas bridge `USize`
indexing back to `Nat` `getElem` so the fast loop is proven equal to the
original `Nat` loop (`goU_eq`). -/

/-- A `Nat` below `USize.size` round-trips through `USize` unchanged. -/
theorem toUSize_toNat_of_lt {n : Nat} (h : n < USize.size) : n.toUSize.toNat = n := by
  simp only [Nat.toUSize]; exact Nat.mod_eq_of_lt h

/-- `ByteArray.uget` at `i` is `getElem` at `i.toNat` (definitional). -/
theorem uget_eq_getElem (data : ByteArray) (i : USize) (h : i.toNat < data.size) :
    data.uget i h = data[i.toNat]'h := rfl

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
    -- When the four hash bytes are in bounds and the buffer is `USize`-
    -- addressable, read them as one wide load (`ugetUInt32LE`, #2706); its model
    -- is exactly the `a ||| b<<<8 ||| c<<<16 ||| d<<<24` recombination, so the
    -- hash value is identical and all three `hash3` variants stay defeq.
    let word :=
      if h4 : pos + 4 ≤ data.size then
        if hsz : data.size.toUSize.toNat = data.size then
          ByteArray.ugetUInt32LE data pos.toUSize (by
            have hds : data.size < USize.size := by
              rw [← hsz]; exact USize.toNat_lt_two_pow_numBits _
            rw [toUSize_toNat_of_lt (show pos < USize.size by omega)]; omega)
        else
          let a := (data[pos]'(by omega)).toUInt32
          let b := (data[pos + 1]'(by omega)).toUInt32
          let c := (data[pos + 2]'(by omega)).toUInt32
          let d := (data[pos + 3]'(by omega)).toUInt32
          a ||| (b <<< 8) ||| (c <<< 16) ||| (d <<< 24)
      else
        let a := (data[pos]'(by omega)).toUInt32
        let b := (data[pos + 1]'(by omega)).toUInt32
        let c := (data[pos + 2]'(by omega)).toUInt32
        a ||| (b <<< 8) ||| (c <<< 16)
    (((word * 2654435761) >>> 16).toNat % hashSize)
  countMatch (data : ByteArray) (p1 p2 maxLen : Nat)
      (h1 : p1 + maxLen ≤ data.size) (h2 : p2 + maxLen ≤ data.size) : Nat :=
    -- P1a: when the buffer is `USize`-addressable (always true at runtime; the
    -- check is one `USize` round-trip, no bignum), run the unboxed `USize` loop
    -- `goU` — proven equal to the `Nat` `go` by `goU_eq`. Else fall back to `go`.
    if hg : data.size.toUSize.toNat = data.size then
      have hsz : data.size < USize.size := by
        rw [← hg]; exact USize.toNat_lt_two_pow_numBits _
      (goU data p1.toUSize p2.toUSize 0 maxLen.toUSize hsz
        (by rw [toUSize_toNat_of_lt (by omega), toUSize_toNat_of_lt (by omega)]; omega)
        (by rw [toUSize_toNat_of_lt (by omega), toUSize_toNat_of_lt (by omega)]; omega)).toNat
    else go data p1 p2 0 maxLen h1 h2
  go (data : ByteArray) (p1 p2 i maxLen : Nat)
      (h1 : p1 + maxLen ≤ data.size) (h2 : p2 + maxLen ≤ data.size) : Nat :=
    if hi : i < maxLen then
      if (data[p1 + i]'(by omega)) == (data[p2 + i]'(by omega)) then
        go data p1 p2 (i + 1) maxLen h1 h2
      else i
    else i
  termination_by maxLen - i
  goU (data : ByteArray) (p1 p2 i maxLen : USize)
      (hsz : data.size < USize.size)
      (h1 : p1.toNat + maxLen.toNat ≤ data.size)
      (h2 : p2.toNat + maxLen.toNat ≤ data.size) : USize :=
    if hlt : i < maxLen then
      have hUS : USize.size = 2 ^ System.Platform.numBits := rfl
      have him : i.toNat < maxLen.toNat := USize.lt_iff_toNat_lt.mp hlt
      have e1 : (p1 + i).toNat = p1.toNat + i.toNat := by
        rw [USize.toNat_add]; apply Nat.mod_eq_of_lt; omega
      have e2 : (p2 + i).toNat = p2.toNat + i.toNat := by
        rw [USize.toNat_add]; apply Nat.mod_eq_of_lt; omega
      have hb1 : (p1 + i).toNat < data.size := by omega
      have hb2 : (p2 + i).toNat < data.size := by omega
      if data.uget (p1 + i) hb1 == data.uget (p2 + i) hb2 then
        goU data p1 p2 (i + 1) maxLen hsz h1 h2
      else i
    else i
  termination_by maxLen.toNat - i.toNat
  decreasing_by
    have hUS : USize.size = 2 ^ System.Platform.numBits := rfl
    have him : i.toNat < maxLen.toNat := USize.lt_iff_toNat_lt.mp hlt
    have e : (i + 1).toNat = i.toNat + 1 := by
      rw [USize.toNat_add, USize.toNat_one]; apply Nat.mod_eq_of_lt; omega
    omega
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
    -- When the four hash bytes are in bounds and the buffer is `USize`-
    -- addressable, read them as one wide load (`ugetUInt32LE`, #2706); its model
    -- is exactly the `a ||| b<<<8 ||| c<<<16 ||| d<<<24` recombination, so the
    -- hash value is identical and all three `hash3` variants stay defeq.
    let word :=
      if h4 : pos + 4 ≤ data.size then
        if hsz : data.size.toUSize.toNat = data.size then
          ByteArray.ugetUInt32LE data pos.toUSize (by
            have hds : data.size < USize.size := by
              rw [← hsz]; exact USize.toNat_lt_two_pow_numBits _
            rw [toUSize_toNat_of_lt (show pos < USize.size by omega)]; omega)
        else
          let a := (data[pos]'(by omega)).toUInt32
          let b := (data[pos + 1]'(by omega)).toUInt32
          let c := (data[pos + 2]'(by omega)).toUInt32
          let d := (data[pos + 3]'(by omega)).toUInt32
          a ||| (b <<< 8) ||| (c <<< 16) ||| (d <<< 24)
      else
        let a := (data[pos]'(by omega)).toUInt32
        let b := (data[pos + 1]'(by omega)).toUInt32
        let c := (data[pos + 2]'(by omega)).toUInt32
        a ||| (b <<< 8) ||| (c <<< 16)
    (((word * 2654435761) >>> 16).toNat % hashSize)
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
    `prev[pos &&& 0x7FFF]` (the circular slot) to the old head. The single guard
    discharges all three accesses
    statically; the fallback keeps the original panic-checked operations and is
    dead in practice — `hashTable`/`prev` sizes are fixed at allocation.
    Provably equal to the panic-checked sequence (`headInsertGuarded_eq` in
    `LZ77ChainCorrect`). Superseded in the mainLoops by `headProbeGuarded` +
    two `guardedSet`s (Wave 5 de-boxing — this tuple return allocated a heap
    constructor per position); kept with its `_eq` lemma. -/
@[inline] def headInsertGuarded (hashTable : Array Nat) (prev : Array Nat) (h pos : Nat) :
    Nat × Array Nat × Array Nat :=
  if hg : h < hashTable.size ∧ (pos &&& 0x7FFF) < prev.size then
    let head := hashTable[h]'hg.1
    (head, hashTable.set h pos hg.1, prev.set (pos &&& 0x7FFF) head hg.2)
  else
    let head := hashTable[h]!
    (head, hashTable.set! h pos, prev.set! (pos &&& 0x7FFF) head)

/-- Single guarded chain-head probe (for the lazy matcher's lookahead position,
    which reads a bucket head without inserting): one runtime bounds check,
    panic-checked fallback (dead in practice). Provably equal to `hashTable[h]!`
    (`headProbeGuarded_eq` in `LZ77ChainCorrect`). -/
@[inline] def headProbeGuarded (hashTable : Array Nat) (h : Nat) : Nat :=
  if hb : h < hashTable.size then hashTable[h]'hb else hashTable[h]!

/-- Single guarded array write (Wave 5 de-boxing): one runtime bounds check,
    panic-checked fallback (dead in practice — the matcher arrays have fixed
    size). Provably equal to `a.set! i v` (`guardedSet_eq` in
    `LZ77ChainCorrect`). The mainLoops do their per-position head insertion as
    `headProbeGuarded` + two `guardedSet`s — three single-value steps in place
    of `headInsertGuarded`'s tuple, so nothing is heap-allocated per position. -/
@[inline] def guardedSet {α : Type} (a : Array α) (i : Nat) (v : α) : Array α :=
  if h : i < a.size then a.set i v h else a.set! i v

/-- The circular `prev`-buffer window: a fixed 32768-entry (= 32 KiB DEFLATE
    window) ring of absolute positions, indexed by the low 15 bits of a
    position (`pos &&& 0x7FFF`, zlib's scheme). Memory is O(window) not
    O(filesize). With `windowSize ≤ 32768` the in-window guard
    `pos - cand ≤ windowSize` discards any candidate a stale slot could surface,
    and the one aliasing pair inside the window (`pos` and `pos - 32768`) only
    perturbs the heuristic, never validity — the `prev` contents never enter
    the proof (see `lz77Chain`). The ring stores absolute positions as `Nat`
    (small values stay inline-unboxed, so no boxing or conversion in the hot
    walk); only the shrink from O(filesize) to a window-sized ring matters for
    speed (it fits L2), which is why this is a `Nat` ring rather than a de-boxed
    `UInt32` one (the `UInt32` conversions measured as a net tax). -/
def chainWinSize : Nat := 32768

/-- A circular `prev`-buffer index `n &&& 0x7FFF` is always `< 32768`, so a
    `chainWinSize`-entry buffer indexes every masked position in bounds. -/
theorem winMask_lt (n : Nat) : (n &&& 0x7FFF) < chainWinSize := by
  have := @Nat.and_le_right n 0x7FFF
  unfold chainWinSize; omega

/-- Greedy LZ77 with bounded-depth hash chains: at each position, walk the
    `prev` chain from the bucket head up to `maxChain` candidates and keep the
    longest in-window match. This finds far longer matches than the single-probe
    `lz77Greedy`/`lz77Lazy` (it reaches C-reference ratio on text).

    The chain is only a *heuristic for finding* candidates — validity is
    re-established at the moment of emission by `countMatch` (verifies the bytes)
    plus the explicit `matchPos < pos` / `pos - matchPos ≤ windowSize` guards, so
    the `prev`/`hashTable` array contents never enter the correctness proof.
    `prev` is a fixed `chainWinSize` (32768 = 32 KiB window) circular buffer of
    de-boxed `UInt32` absolute positions, indexed by `pos &&& 0x7FFF` (zlib's
    scheme): memory is O(window) not O(filesize) and the buffer fits L2. Buckets
    and `prev` are initialised to the sentinel `data.size` (≥ every real
    position), so an unset chain link fails the `cand < pos` guard and stops the
    walk — no separate validity bitmap needed. Circular reuse stays sound: for
    every candidate strictly inside the window (`pos - cand < 32768`) the slot
    `cand &&& 0x7FFF` differs from `pos`'s own slot and from every other
    in-window position's, so the link is exactly the full-size buffer's link;
    a *stale* slot can only hold a position older than the window, discarded by
    `pos - cand ≤ windowSize`; and at the exact boundary `cand = pos - 32768`
    the slot was just overwritten by `pos`'s own insertion, so the read may
    revisit the current bucket head or form a short cycle — harmless, because
    the walk is fuel-bounded and `countMatch` + the window guard re-verify every
    emitted match. Reuses `lz77Greedy`'s `hash3`/`countMatch`/`trailing` helpers
    (and their proofs). -/
def lz77Chain (data : ByteArray) (maxChain : Nat) (windowSize : Nat := 32768)
    (insertCap : Nat := 1000000000) :
    Array LZ77Token :=
  if data.size < 3 then
    (lz77Greedy.trailing data 0).toArray
  else
    let hashSize := 65536
    (mainLoop data windowSize hashSize maxChain
      (.replicate hashSize data.size) (.replicate (min chainWinSize data.size) data.size) 0 insertCap).toArray
where
  /-- Walk the `prev` chain up to `fuel` steps from `cand`, keeping the longest
      in-window match `(bestLen, bestPos)`. Stops at the first out-of-window or
      out-of-range link (`cand ≥ pos`, incl. the `data.size` sentinel). `prev`
      is the fixed-size circular ring indexed by `cand &&& 0x7FFF`; its contents
      are a pure heuristic, so the windowing never enters the validity proof. -/
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
      else chainWalk data prev windowSize pos maxLen hpm prev[cand &&& 0x7FFF]! (fuel - 1) bl bp
    else (bestLen, bestPos)
  termination_by fuel
  decreasing_by omega
  /-- Insert positions `pos+1 .. pos+min(matchLen-1, insertCap)` into the chains so
      later matches can reach them: `prev[p] := head[bucket]`, then `head[bucket] := p`.
      `insertCap` bounds the interior insertions per match — a small cap (fast levels)
      defers most of this work for speed at a ratio cost; a large cap inserts every
      position (best ratio). The chain is a heuristic, so any cap stays correct. -/
  updateHashes (data : ByteArray) (hashSize : Nat)
      (hashTable : Array Nat) (prev : Array Nat) (pos j matchLen insertCap : Nat) :
      Array Nat × Array Nat :=
    if j < matchLen ∧ j ≤ insertCap then
      if h : pos + j + 2 < data.size then
        let hsh := lz77Greedy.hash3 data (pos + j) hashSize h
        let head := hashTable[hsh]!
        updateHashes data hashSize (hashTable.set! hsh (pos + j)) (prev.set! ((pos + j) &&& 0x7FFF) head)
          pos (j + 1) matchLen insertCap
      else
        updateHashes data hashSize hashTable prev pos (j + 1) matchLen insertCap
    else (hashTable, prev)
  termination_by matchLen - j
  decreasing_by all_goals omega
  mainLoop (data : ByteArray) (windowSize hashSize maxChain : Nat)
      (hashTable : Array Nat) (prev : Array Nat) (pos insertCap : Nat) : List LZ77Token :=
    if hlt : pos + 2 < data.size then
      let h := lz77Greedy.hash3 data pos hashSize hlt
      let head := headProbeGuarded hashTable h
      let hashTable := guardedSet hashTable h pos
      let prev := guardedSet prev (pos &&& 0x7FFF) head
      let maxLen := min 258 (data.size - pos)
      have hmaxLenP : pos + maxLen ≤ data.size := by omega
      let m := chainWalk data prev windowSize pos maxLen hmaxLenP head maxChain 0 0
      let matchLen := m.1
      let matchPos := m.2
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
`LZ77ChainCorrect`). The recursive reference versions and all their proofs are
untouched. Wave 5 de-boxing: the iterative matchers call
`chainWalkGuardedPacked` (the same walk with the result pair packed into one
small `Nat`) instead of `chainWalkGuarded`, which stays as the proof bridge. -/

/-- Proven-bounds copy of `lz77Chain.chainWalk`: the circular read
    `prev[cand &&& 0x7FFF]` is in range because the mask gives
    `cand &&& 0x7FFF < chainWinSize` (`winMask_lt`) and `hps : min chainWinSize data.size ≤ prev.size`. -/
def chainWalkFast (data : ByteArray) (prev : Array Nat) (windowSize pos maxLen : Nat)
    (hpm : pos + maxLen ≤ data.size) (hps : min chainWinSize data.size ≤ prev.size)
    (cand fuel bestLen bestPos : Nat) : Nat × Nat :=
  if fuel = 0 then (bestLen, bestPos)
  else if hc : cand < pos ∧ pos - cand ≤ windowSize then
    have hcand : cand + maxLen ≤ data.size := by omega
    let ml := lz77Greedy.countMatch data cand pos maxLen hcand hpm
    let (bl, bp) := if ml > bestLen then (ml, cand) else (bestLen, bestPos)
    if bl ≥ maxLen then (bl, bp)
    else chainWalkFast data prev windowSize pos maxLen hpm hps
      (prev[cand &&& 0x7FFF]'(by have := winMask_lt cand; have := Nat.and_le_left (n := cand) (m := 0x7FFF); omega)) (fuel - 1) bl bp
  else (bestLen, bestPos)
termination_by fuel
decreasing_by omega

/-- One runtime `min chainWinSize data.size ≤ prev.size` check guards the whole `chainWalkFast`
    inner loop; the (unreachable, since `prev` is the fixed 32768-entry ring)
    fallback is the original panic-checked walk, so this equals `lz77Chain.chainWalk`. -/
@[inline] def chainWalkGuarded (data : ByteArray) (prev : Array Nat)
    (windowSize pos maxLen : Nat) (hpm : pos + maxLen ≤ data.size)
    (cand fuel bestLen bestPos : Nat) : Nat × Nat :=
  if hps : min chainWinSize data.size ≤ prev.size then
    chainWalkFast data prev windowSize pos maxLen hpm hps cand fuel bestLen bestPos
  else
    lz77Chain.chainWalk data prev windowSize pos maxLen hpm cand fuel bestLen bestPos

/-- Packed-result copy of `chainWalkFast` (Wave 5 de-boxing): the identical
    walk, but the `(bestLen, bestPos)` accumulator is carried and returned as
    the single small `Nat` `bestPos * 512 + bestLen`, so the per-position hot
    call allocates no pair constructor (and no per-step `(bl, bp)` pair
    either). `bestLen` never exceeds `maxLen`, which every call site clamps to
    `min 258 _ < 512`, so the call sites decode exactly with `% 512` / `/ 512`
    (`chainWalkGuardedPacked_mod`/`_div` in `LZ77ChainCorrect`, via the
    lockstep equality `chainWalkPacked_eq`). -/
def chainWalkPacked (data : ByteArray) (prev : Array Nat) (windowSize pos maxLen : Nat)
    (hpm : pos + maxLen ≤ data.size) (hps : min chainWinSize data.size ≤ prev.size)
    (cand fuel bestLen bestPos : Nat) : Nat :=
  if fuel = 0 then bestPos * 512 + bestLen
  else if hc : cand < pos ∧ pos - cand ≤ windowSize then
    have hcand : cand + maxLen ≤ data.size := by omega
    -- Match prefilter (zlib `scan_end`): a candidate can only *beat* the current
    -- best length if its byte at offset `bestLen` matches the one at `pos`;
    -- otherwise `countMatch ≤ bestLen` and the update test `ml > bestLen` fails,
    -- so the full compare is wasted. Skipping it is output-preserving.
    let skip : Bool := if hbl : bestLen < maxLen then
        data[cand + bestLen]'(by omega) != data[pos + bestLen]'(by omega)
      else false
    if skip then
      chainWalkPacked data prev windowSize pos maxLen hpm hps
        (prev[cand &&& 0x7FFF]'(by have := winMask_lt cand; have := Nat.and_le_left (n := cand) (m := 0x7FFF); omega)) (fuel - 1) bestLen bestPos
    else
      let ml := lz77Greedy.countMatch data cand pos maxLen hcand hpm
      let bl := if ml > bestLen then ml else bestLen
      let bp := if ml > bestLen then cand else bestPos
      if bl ≥ maxLen then bp * 512 + bl
      else chainWalkPacked data prev windowSize pos maxLen hpm hps
        (prev[cand &&& 0x7FFF]'(by have := winMask_lt cand; have := Nat.and_le_left (n := cand) (m := 0x7FFF); omega)) (fuel - 1) bl bp
  else bestPos * 512 + bestLen
termination_by fuel
decreasing_by all_goals omega

/-- One runtime `min chainWinSize data.size ≤ prev.size` check guards the whole `chainWalkPacked`
    inner loop; the (unreachable) fallback packs the reference walk's pair, so
    this equals `bestPos * 512 + bestLen` of `lz77Chain.chainWalk`
    (`chainWalkGuardedPacked_eq`). -/
@[inline] def chainWalkGuardedPacked (data : ByteArray) (prev : Array Nat)
    (windowSize pos maxLen : Nat) (hpm : pos + maxLen ≤ data.size)
    (cand fuel bestLen bestPos : Nat) : Nat :=
  if hps : min chainWinSize data.size ≤ prev.size then
    chainWalkPacked data prev windowSize pos maxLen hpm hps cand fuel bestLen bestPos
  else
    let p := lz77Chain.chainWalk data prev windowSize pos maxLen hpm cand fuel bestLen bestPos
    p.2 * 512 + p.1

/-- Proven-bounds copy of `lz77Chain.updateHashes`: the bucket index `hsh` is
    `< hashSize ≤ hashTable.size`, so `hashTable[hsh]` needs no runtime check. -/
def updateHashesFast (data : ByteArray) (hashSize : Nat)
    (hashTable : Array Nat) (prev : Array Nat) (pos j matchLen insertCap : Nat)
    (hhs : 0 < hashSize) (hht : hashSize ≤ hashTable.size) : Array Nat × Array Nat :=
  if j < matchLen ∧ j ≤ insertCap then
    if h : pos + j + 2 < data.size then
      let hsh := lz77Greedy.hash3 data (pos + j) hashSize h
      have hb : hsh < hashTable.size := by
        have : hsh < hashSize := Nat.mod_lt _ hhs
        omega
      let head := hashTable[hsh]'hb
      updateHashesFast data hashSize (hashTable.set! hsh (pos + j)) (prev.set! ((pos + j) &&& 0x7FFF) head)
        pos (j + 1) matchLen insertCap hhs (by simpa using hht)
    else
      updateHashesFast data hashSize hashTable prev pos (j + 1) matchLen insertCap hhs hht
  else (hashTable, prev)
termination_by matchLen - j
decreasing_by all_goals omega

/-- `updateHashesFast` with the two hot per-insertion writes done via the
    proven-bounds `Array.set` (no panic-bounds branch) instead of `set!`. The
    bucket index `hsh < hashTable.size` (`hb`) and the chain mask `(pos+j) &&&
    0x7FFF < chainWinSize ≤ prev.size` (`winMask_lt`/`Nat.and_le_left` + `hpv`)
    are proven, so the bounds checks `set!` performs are wasted work. Proven
    equal to `updateHashesFast` (`updateHashesFastU_eq`); the `min chainWinSize
    data.size ≤ prev.size` guard is the same one `chainWalkGuardedPacked` carries
    — always true for the production chain arrays (`prev` is the fixed
    `min chainWinSize data.size`-entry ring), so it is a defensive guard, not
    hot-path branching — established once per call by `updateHashesGuarded`. -/
def updateHashesFastU (data : ByteArray) (hashSize : Nat)
    (hashTable : Array Nat) (prev : Array Nat) (pos j matchLen insertCap : Nat)
    (hhs : 0 < hashSize) (hht : hashSize ≤ hashTable.size)
    (hpv : min chainWinSize data.size ≤ prev.size) : Array Nat × Array Nat :=
  if j < matchLen ∧ j ≤ insertCap then
    if h : pos + j + 2 < data.size then
      let hsh := lz77Greedy.hash3 data (pos + j) hashSize h
      have hb : hsh < hashTable.size := by
        have : hsh < hashSize := Nat.mod_lt _ hhs
        omega
      have hmask : ((pos + j) &&& 0x7FFF) < prev.size := by
        -- `h1`: mask `< chainWinSize` (covers `chainWinSize ≤ data.size`). `h2`:
        -- mask `≤ pos+j < data.size` (covers the small-data `data.size <
        -- chainWinSize` side). Together: mask `< min chainWinSize data.size ≤
        -- prev.size`, even when `prev.size` is exactly that minimum.
        have h1 := winMask_lt (pos + j)
        have h2 := Nat.and_le_left (n := pos + j) (m := 0x7FFF)
        simp only [chainWinSize] at h1 hpv; omega
      let head := hashTable[hsh]'hb
      updateHashesFastU data hashSize
        (hashTable.set hsh (pos + j) hb)
        (prev.set ((pos + j) &&& 0x7FFF) head hmask)
        pos (j + 1) matchLen insertCap hhs
        (by rw [Array.size_set]; exact hht) (by rw [Array.size_set]; exact hpv)
    else
      updateHashesFastU data hashSize hashTable prev pos (j + 1) matchLen insertCap hhs hht hpv
  else (hashTable, prev)
termination_by matchLen - j
decreasing_by all_goals omega

/-- One runtime `0 < hashSize ∧ hashSize ≤ hashTable.size` check guards the whole
    `updateHashesFast` insertion loop; the fallback is the original panic-checked
    insertion, so this equals `lz77Chain.updateHashes`. The extra
    `min chainWinSize data.size ≤ prev.size` check unlocks the proven-bounds-`set`
    walk (`updateHashesFastU`); both other branches fall back to the `set!` walk
    (`updateHashesFast`) / the reference insertion. -/
@[inline] def updateHashesGuarded (data : ByteArray) (hashSize : Nat)
    (hashTable : Array Nat) (prev : Array Nat) (pos j matchLen insertCap : Nat) :
    Array Nat × Array Nat :=
  if hu : 0 < hashSize ∧ hashSize ≤ hashTable.size then
    if hpv : min chainWinSize data.size ≤ prev.size then
      updateHashesFastU data hashSize hashTable prev pos j matchLen insertCap hu.1 hu.2 hpv
    else
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
      (.replicate hashSize data.size) (.replicate (min chainWinSize data.size) data.size) 0 #[]
where
  mainLoop (data : ByteArray) (windowSize hashSize maxChain insertCap : Nat)
      (hashTable : Array Nat) (prev : Array Nat) (pos : Nat) (acc : Array LZ77Token) :
      Array LZ77Token :=
    if hlt : pos + 2 < data.size then
      let h := lz77Greedy.hash3 data pos hashSize hlt
      let head := headProbeGuarded hashTable h
      let hashTable := guardedSet hashTable h pos
      let prev := guardedSet prev (pos &&& 0x7FFF) head
      let maxLen := min 258 (data.size - pos)
      have hmaxLenP : pos + maxLen ≤ data.size := by omega
      let r := chainWalkGuardedPacked data prev windowSize pos maxLen hmaxLenP head maxChain 0 0
      let matchLen := r % 512
      let matchPos := r / 512
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
    (insertCap : Nat := 1000000000) (goodMatch : Nat := 259) :
    Array LZ77Token :=
  if data.size < 3 then
    (lz77Greedy.trailing data 0).toArray
  else
    let hashSize := 65536
    (mainLoop data windowSize hashSize maxChain
      (.replicate hashSize data.size) (.replicate (min chainWinSize data.size) data.size) 0 insertCap goodMatch).toArray
where
  mainLoop (data : ByteArray) (windowSize hashSize maxChain : Nat)
      (hashTable : Array Nat) (prev : Array Nat) (pos insertCap goodMatch : Nat) : List LZ77Token :=
    if hlt : pos + 2 < data.size then
      let h := lz77Greedy.hash3 data pos hashSize hlt
      let head := headProbeGuarded hashTable h
      let hashTable := guardedSet hashTable h pos
      let prev := guardedSet prev (pos &&& 0x7FFF) head
      let maxLen := min 258 (data.size - pos)
      have hmaxLenP : pos + maxLen ≤ data.size := by omega
      let m := lz77Chain.chainWalk data prev windowSize pos maxLen hmaxLenP head maxChain 0 0
      let matchLen := m.1
      let matchPos := m.2
      if hge : matchLen ≥ 3 then
        if hle : pos + matchLen ≤ data.size then
          -- Lazy: probe pos+1 for a longer, no-farther match (distance-guarded deferral)
          if h3lt : pos + 3 < data.size then
            -- Lazy gate (zlib `good_match`): probe pos+1 only when the first match is
            -- short. `goodMatch = 259` (> 258) restores the ungated lazy matcher.
            if matchLen < goodMatch then
              let h2 := lz77Greedy.hash3 data (pos + 1) hashSize (by omega)
              let head2 := headProbeGuarded hashTable h2
              let maxLen2 := min 258 (data.size - (pos + 1))
              have hmaxLen2P : (pos + 1) + maxLen2 ≤ data.size := by omega
              let m2 :=
                lz77Chain.chainWalk data prev windowSize (pos + 1) maxLen2 hmaxLen2P head2 maxChain 0 0
              let matchLen2 := m2.1
              let matchPos2 := m2.2
              if matchLen2 > matchLen ∧ pos + 1 - matchPos2 ≤ pos - matchPos then
                if hle2 : pos + 1 + matchLen2 ≤ data.size then
                  -- Longer & no-farther match at pos+1: emit literal at pos + reference at pos+1
                  have : data.size - (pos + 1 + matchLen2) < data.size - pos := by omega
                  let (hashTable, prev) :=
                    lz77Chain.updateHashes data hashSize hashTable prev pos 1 (matchLen2 + 1) insertCap
                  .literal (data[pos]'(by omega)) ::
                    .reference matchLen2 (pos + 1 - matchPos2) ::
                    mainLoop data windowSize hashSize maxChain hashTable prev (pos + 1 + matchLen2) insertCap goodMatch
                else
                  -- matchLen2 spills past data: keep match at pos
                  have : data.size - (pos + matchLen) < data.size - pos := by omega
                  let (hashTable, prev) :=
                    lz77Chain.updateHashes data hashSize hashTable prev pos 1 matchLen insertCap
                  .reference matchLen (pos - matchPos) ::
                    mainLoop data windowSize hashSize maxChain hashTable prev (pos + matchLen) insertCap goodMatch
              else
                -- No better match at pos+1: keep match at pos
                have : data.size - (pos + matchLen) < data.size - pos := by omega
                let (hashTable, prev) :=
                  lz77Chain.updateHashes data hashSize hashTable prev pos 1 matchLen insertCap
                .reference matchLen (pos - matchPos) ::
                  mainLoop data windowSize hashSize maxChain hashTable prev (pos + matchLen) insertCap goodMatch
            else
              -- Gated: long first match, skip the lookahead; still insert interior hashes.
              have : data.size - (pos + matchLen) < data.size - pos := by omega
              let (hashTable, prev) :=
                lz77Chain.updateHashes data hashSize hashTable prev pos 1 matchLen insertCap
              .reference matchLen (pos - matchPos) ::
                mainLoop data windowSize hashSize maxChain hashTable prev (pos + matchLen) insertCap goodMatch
          else
            -- Near end of data: keep match at pos
            have : data.size - (pos + matchLen) < data.size - pos := by omega
            .reference matchLen (pos - matchPos) ::
              mainLoop data windowSize hashSize maxChain hashTable prev (pos + matchLen) insertCap goodMatch
        else
          .literal (data[pos]'(by omega)) ::
            mainLoop data windowSize hashSize maxChain hashTable prev (pos + 1) insertCap goodMatch
      else
        .literal (data[pos]'(by omega)) ::
          mainLoop data windowSize hashSize maxChain hashTable prev (pos + 1) insertCap goodMatch
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
    (insertCap : Nat := 1000000000) (goodMatch : Nat := 259) :
    Array LZ77Token :=
  if data.size < 3 then
    lz77GreedyIter.trailing data 0 #[]
  else
    let hashSize := 65536
    mainLoop data windowSize hashSize maxChain insertCap goodMatch
      (.replicate hashSize data.size) (.replicate (min chainWinSize data.size) data.size) 0 #[]
where
  mainLoop (data : ByteArray) (windowSize hashSize maxChain insertCap goodMatch : Nat)
      (hashTable : Array Nat) (prev : Array Nat) (pos : Nat) (acc : Array LZ77Token) :
      Array LZ77Token :=
    if hlt : pos + 2 < data.size then
      let h := lz77Greedy.hash3 data pos hashSize hlt
      let head := headProbeGuarded hashTable h
      let hashTable := guardedSet hashTable h pos
      let prev := guardedSet prev (pos &&& 0x7FFF) head
      let maxLen := min 258 (data.size - pos)
      have hmaxLenP : pos + maxLen ≤ data.size := by omega
      let r := chainWalkGuardedPacked data prev windowSize pos maxLen hmaxLenP head maxChain 0 0
      let matchLen := r % 512
      let matchPos := r / 512
      if hge : matchLen ≥ 3 then
        if hle : pos + matchLen ≤ data.size then
          if h3lt : pos + 3 < data.size then
            -- Lazy gate (zlib `good_match`): probe pos+1 only when the first match is
            -- short. `goodMatch = 259` (> 258) restores the ungated lazy matcher.
            if matchLen < goodMatch then
              let h2 := lz77Greedy.hash3 data (pos + 1) hashSize (by omega)
              let head2 := headProbeGuarded hashTable h2
              let maxLen2 := min 258 (data.size - (pos + 1))
              have hmaxLen2P : (pos + 1) + maxLen2 ≤ data.size := by omega
              let r2 :=
                chainWalkGuardedPacked data prev windowSize (pos + 1) maxLen2 hmaxLen2P head2 maxChain 0 0
              let matchLen2 := r2 % 512
              let matchPos2 := r2 / 512
              if matchLen2 > matchLen ∧ pos + 1 - matchPos2 ≤ pos - matchPos then
                if hle2 : pos + 1 + matchLen2 ≤ data.size then
                  have : data.size - (pos + 1 + matchLen2) < data.size - pos := by omega
                  let (hashTable, prev) :=
                    updateHashesGuarded data hashSize hashTable prev pos 1 (matchLen2 + 1) insertCap
                  mainLoop data windowSize hashSize maxChain insertCap goodMatch hashTable prev (pos + 1 + matchLen2)
                    (acc.push (.literal (data[pos]'(by omega))) |>.push
                      (.reference matchLen2 (pos + 1 - matchPos2)))
                else
                  have : data.size - (pos + matchLen) < data.size - pos := by omega
                  let (hashTable, prev) :=
                    updateHashesGuarded data hashSize hashTable prev pos 1 matchLen insertCap
                  mainLoop data windowSize hashSize maxChain insertCap goodMatch hashTable prev (pos + matchLen)
                    (acc.push (.reference matchLen (pos - matchPos)))
              else
                have : data.size - (pos + matchLen) < data.size - pos := by omega
                let (hashTable, prev) :=
                  updateHashesGuarded data hashSize hashTable prev pos 1 matchLen insertCap
                mainLoop data windowSize hashSize maxChain insertCap goodMatch hashTable prev (pos + matchLen)
                  (acc.push (.reference matchLen (pos - matchPos)))
            else
              -- Gated: long first match, skip the lookahead; still insert interior hashes.
              have : data.size - (pos + matchLen) < data.size - pos := by omega
              let (hashTable, prev) :=
                updateHashesGuarded data hashSize hashTable prev pos 1 matchLen insertCap
              mainLoop data windowSize hashSize maxChain insertCap goodMatch hashTable prev (pos + matchLen)
                (acc.push (.reference matchLen (pos - matchPos)))
          else
            have : data.size - (pos + matchLen) < data.size - pos := by omega
            mainLoop data windowSize hashSize maxChain insertCap goodMatch hashTable prev (pos + matchLen)
              (acc.push (.reference matchLen (pos - matchPos)))
        else
          mainLoop data windowSize hashSize maxChain insertCap goodMatch hashTable prev (pos + 1)
            (acc.push (.literal (data[pos]'(by omega))))
      else
        mainLoop data windowSize hashSize maxChain insertCap goodMatch hashTable prev (pos + 1)
          (acc.push (.literal (data[pos]'(by omega))))
    else
      lz77GreedyIter.trailing data pos acc
  termination_by data.size - pos
  decreasing_by all_goals omega

/-! ## Packed-token matcher twins (Wave 3b stage A)

`lz77ChainIterP`/`lz77ChainLazyIterP` are copies of the iterative matchers
whose accumulator holds `packTok`-encoded `UInt32`s instead of boxed
`LZ77Token`s. The chain state (`hashTable`/`prev : Array Nat`)
is identical to the boxed-token twins; only the
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
      (.replicate hashSize data.size) (.replicate (min chainWinSize data.size) data.size) 0
      (Array.emptyWithCapacity data.size)
where
  mainLoop (data : ByteArray) (windowSize hashSize maxChain insertCap : Nat)
      (hashTable : Array Nat) (prev : Array Nat) (pos : Nat) (acc : Array UInt32) :
      Array UInt32 :=
    if hlt : pos + 2 < data.size then
      let h := lz77Greedy.hash3 data pos hashSize hlt
      let head := headProbeGuarded hashTable h
      let hashTable := guardedSet hashTable h pos
      let prev := guardedSet prev (pos &&& 0x7FFF) head
      let maxLen := min 258 (data.size - pos)
      have hmaxLenP : pos + maxLen ≤ data.size := by omega
      let r := chainWalkGuardedPacked data prev windowSize pos maxLen hmaxLenP head maxChain 0 0
      let matchLen := r % 512
      let matchPos := r / 512
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
    (insertCap : Nat := 1000000000) (goodMatch : Nat := 259) :
    Array UInt32 :=
  if data.size < 3 then
    trailingP data 0 #[]
  else
    let hashSize := 65536
    mainLoop data windowSize hashSize maxChain insertCap goodMatch
      (.replicate hashSize data.size) (.replicate (min chainWinSize data.size) data.size) 0
      (Array.emptyWithCapacity data.size)
where
  mainLoop (data : ByteArray) (windowSize hashSize maxChain insertCap goodMatch : Nat)
      (hashTable : Array Nat) (prev : Array Nat) (pos : Nat) (acc : Array UInt32) :
      Array UInt32 :=
    if hlt : pos + 2 < data.size then
      let h := lz77Greedy.hash3 data pos hashSize hlt
      let head := headProbeGuarded hashTable h
      let hashTable := guardedSet hashTable h pos
      let prev := guardedSet prev (pos &&& 0x7FFF) head
      let maxLen := min 258 (data.size - pos)
      have hmaxLenP : pos + maxLen ≤ data.size := by omega
      let r := chainWalkGuardedPacked data prev windowSize pos maxLen hmaxLenP head maxChain 0 0
      let matchLen := r % 512
      let matchPos := r / 512
      if hge : matchLen ≥ 3 then
        if hle : pos + matchLen ≤ data.size then
          if h3lt : pos + 3 < data.size then
            -- Lazy gate (zlib `good_match`): only run the second `pos+1` chain walk
            -- when the first match is short (`matchLen < goodMatch`). A long first
            -- match is rarely improved by deferring, so skipping the lookahead trades
            -- a negligible amount of ratio for half the lazy walk. `goodMatch = 259`
            -- (> max match 258) restores the ungated matcher exactly.
            if matchLen < goodMatch then
              let h2 := lz77Greedy.hash3 data (pos + 1) hashSize (by omega)
              let head2 := headProbeGuarded hashTable h2
              let maxLen2 := min 258 (data.size - (pos + 1))
              have hmaxLen2P : (pos + 1) + maxLen2 ≤ data.size := by omega
              let r2 :=
                chainWalkGuardedPacked data prev windowSize (pos + 1) maxLen2 hmaxLen2P head2 maxChain 0 0
              let matchLen2 := r2 % 512
              let matchPos2 := r2 / 512
              if matchLen2 > matchLen ∧ pos + 1 - matchPos2 ≤ pos - matchPos then
                if hle2 : pos + 1 + matchLen2 ≤ data.size then
                  have : data.size - (pos + 1 + matchLen2) < data.size - pos := by omega
                  let (hashTable, prev) :=
                    updateHashesGuarded data hashSize hashTable prev pos 1 (matchLen2 + 1) insertCap
                  mainLoop data windowSize hashSize maxChain insertCap goodMatch hashTable prev (pos + 1 + matchLen2)
                    (acc.push (packTok (.literal (data[pos]'(by omega)))) |>.push
                      (packTok (.reference matchLen2 (pos + 1 - matchPos2))))
                else
                  have : data.size - (pos + matchLen) < data.size - pos := by omega
                  let (hashTable, prev) :=
                    updateHashesGuarded data hashSize hashTable prev pos 1 matchLen insertCap
                  mainLoop data windowSize hashSize maxChain insertCap goodMatch hashTable prev (pos + matchLen)
                    (acc.push (packTok (.reference matchLen (pos - matchPos))))
              else
                have : data.size - (pos + matchLen) < data.size - pos := by omega
                let (hashTable, prev) :=
                  updateHashesGuarded data hashSize hashTable prev pos 1 matchLen insertCap
                mainLoop data windowSize hashSize maxChain insertCap goodMatch hashTable prev (pos + matchLen)
                  (acc.push (packTok (.reference matchLen (pos - matchPos))))
            else
              -- Gated: first match already long; skip the lookahead, but still insert
              -- interior hashes for the match (mid-buffer) then emit it.
              have : data.size - (pos + matchLen) < data.size - pos := by omega
              let (hashTable, prev) :=
                updateHashesGuarded data hashSize hashTable prev pos 1 matchLen insertCap
              mainLoop data windowSize hashSize maxChain insertCap goodMatch hashTable prev (pos + matchLen)
                (acc.push (packTok (.reference matchLen (pos - matchPos))))
          else
            have : data.size - (pos + matchLen) < data.size - pos := by omega
            mainLoop data windowSize hashSize maxChain insertCap goodMatch hashTable prev (pos + matchLen)
              (acc.push (packTok (.reference matchLen (pos - matchPos))))
        else
          mainLoop data windowSize hashSize maxChain insertCap goodMatch hashTable prev (pos + 1)
            (acc.push (packTok (.literal (data[pos]'(by omega)))))
      else
        mainLoop data windowSize hashSize maxChain insertCap goodMatch hashTable prev (pos + 1)
          (acc.push (packTok (.literal (data[pos]'(by omega)))))
    else
      trailingP data pos acc
  termination_by data.size - pos
  decreasing_by all_goals omega

/-! ## Chainless 2-way-bucket L1 matcher (libdeflate `ht_matchfinder` style)

For the fast (level ≤ 1) corner, `htMatch` drops the hash *chain* entirely
(the chain walk + interior-insertion loop were ~47% of L1 cycles, #2738) in
favour of libdeflate's `ht_matchfinder` scheme: a single hash table with
**two positions per bucket** (`tbl[2*h]` = most-recent, `tbl[2*h+1]` =
second-most-recent), **minimum match length 4** (skips the marginal length-3
matches), and an early-out once a probe reaches **`niceLen = 32`**. Per
position it does at most two bounded `countMatch` probes and one bucket
rotation (`lru := mru; mru := pos`) — no `prev` array, no fuel loop, no
per-match interior insertion.

Like the chain, the table is a pure *heuristic for finding* candidates:
validity is re-established at emission by `countMatch` + the explicit
`cand < pos` / `pos - cand ≤ windowSize` window guards (in `htBest`), so the
table contents never enter the correctness proof. Buckets are initialised to
the sentinel `data.size` (≥ every real position), so an unset slot fails the
`cand < pos` guard and contributes no match. `htMatch` (recursive, for
proofs), `htMatchIter` (iterative boxed, `htMatchIter_eq_htMatch`) and
`htMatchIterP` (packed, `htMatchIterP_eq`) are the greedy-matcher triple;
correctness lives in `Zip/Spec/HtMatchCorrect.lean`. -/

/-- Consider one candidate position `cand` against the running best match
    `(bestLen, bestPos)`: when `cand` is a valid in-window backward position,
    count its match length against `pos` and keep it if strictly longer. The
    table is a heuristic, so this only ever refines the best toward a
    `countMatch`-verified real match (`htBest_spec`). -/
@[inline] def htBest (data : ByteArray) (windowSize pos maxLen : Nat)
    (hpm : pos + maxLen ≤ data.size) (cand bestLen bestPos : Nat) : Nat × Nat :=
  if hc : cand < pos ∧ pos - cand ≤ windowSize then
    have hcand : cand + maxLen ≤ data.size := by omega
    let ml := lz77Greedy.countMatch data cand pos maxLen hcand hpm
    if ml > bestLen then (ml, cand) else (bestLen, bestPos)
  else (bestLen, bestPos)

/-- Probe the two bucket entries `c0` (most-recent) then `c1`, keeping the
    longer match; the `niceLen` early-out skips the second probe once the first
    already reaches a "good enough" length. Returns `(bestLen, bestPos)` with
    `bestLen = 0` when neither entry yields a match (`htProbe_spec`). -/
@[inline] def htProbe (data : ByteArray) (windowSize pos maxLen niceLen : Nat)
    (hpm : pos + maxLen ≤ data.size) (c0 c1 : Nat) : Nat × Nat :=
  let r0 := htBest data windowSize pos maxLen hpm c0 0 0
  if r0.1 ≥ niceLen then r0
  else htBest data windowSize pos maxLen hpm c1 r0.1 r0.2

/-- Recursive reference form of the chainless 2-way-bucket matcher (proofs
    only; `htMatchIter`/`htMatchIterP` are the stack-safe runtime twins).
    `hashSize` is the number of buckets, so the table holds `2 * hashSize`
    positions. -/
def htMatch (data : ByteArray) (windowSize : Nat := 32768) : Array LZ77Token :=
  if data.size < 3 then
    (lz77Greedy.trailing data 0).toArray
  else
    (mainLoop data windowSize 32768 32 (.replicate (2 * 32768) data.size) 0).toArray
where
  mainLoop (data : ByteArray) (windowSize hashSize niceLen : Nat)
      (tbl : Array Nat) (pos : Nat) : List LZ77Token :=
    if hlt : pos + 2 < data.size then
      let h := lz77Greedy.hash3 data pos hashSize hlt
      let c0 := tbl[2 * h]!
      let c1 := tbl[2 * h + 1]!
      let tbl := tbl.set! (2 * h + 1) c0
      let tbl := tbl.set! (2 * h) pos
      let maxLen := min 258 (data.size - pos)
      have hmaxLenP : pos + maxLen ≤ data.size := by omega
      let m := htProbe data windowSize pos maxLen niceLen hmaxLenP c0 c1
      let matchLen := m.1
      let matchPos := m.2
      if hge : matchLen ≥ 4 then
        if hle : pos + matchLen ≤ data.size then
          have : data.size - (pos + matchLen) < data.size - pos := by omega
          .reference matchLen (pos - matchPos) ::
            mainLoop data windowSize hashSize niceLen tbl (pos + matchLen)
        else
          .literal (data[pos]'(by omega)) ::
            mainLoop data windowSize hashSize niceLen tbl (pos + 1)
      else
        .literal (data[pos]'(by omega)) ::
          mainLoop data windowSize hashSize niceLen tbl (pos + 1)
    else
      lz77Greedy.trailing data pos
  termination_by data.size - pos
  decreasing_by all_goals omega

/-- Iterative (tail-recursive, `Array`-accumulating) form of `htMatch`: same
    output, stack-safe on large inputs. The hot per-position table reads/writes
    go through `headProbeGuarded`/`guardedSet` (one runtime bounds check each,
    provably equal to the panic-checked ops), so `htMatchIter_eq_htMatch`
    rewrites them back and proceeds by the accumulator induction. -/
def htMatchIter (data : ByteArray) (windowSize : Nat := 32768) : Array LZ77Token :=
  if data.size < 3 then
    lz77GreedyIter.trailing data 0 #[]
  else
    mainLoop data windowSize 32768 32 (.replicate (2 * 32768) data.size) 0 #[]
where
  mainLoop (data : ByteArray) (windowSize hashSize niceLen : Nat)
      (tbl : Array Nat) (pos : Nat) (acc : Array LZ77Token) : Array LZ77Token :=
    if hlt : pos + 2 < data.size then
      let h := lz77Greedy.hash3 data pos hashSize hlt
      let c0 := headProbeGuarded tbl (2 * h)
      let c1 := headProbeGuarded tbl (2 * h + 1)
      let tbl := guardedSet tbl (2 * h + 1) c0
      let tbl := guardedSet tbl (2 * h) pos
      let maxLen := min 258 (data.size - pos)
      have hmaxLenP : pos + maxLen ≤ data.size := by omega
      let m := htProbe data windowSize pos maxLen niceLen hmaxLenP c0 c1
      let matchLen := m.1
      let matchPos := m.2
      if hge : matchLen ≥ 4 then
        if hle : pos + matchLen ≤ data.size then
          have : data.size - (pos + matchLen) < data.size - pos := by omega
          mainLoop data windowSize hashSize niceLen tbl (pos + matchLen)
            (acc.push (.reference matchLen (pos - matchPos)))
        else
          mainLoop data windowSize hashSize niceLen tbl (pos + 1)
            (acc.push (.literal (data[pos]'(by omega))))
      else
        mainLoop data windowSize hashSize niceLen tbl (pos + 1)
          (acc.push (.literal (data[pos]'(by omega))))
    else
      lz77GreedyIter.trailing data pos acc
  termination_by data.size - pos
  decreasing_by all_goals omega

/-- Packed-token twin of `htMatchIter` (`Array UInt32` accumulator, `packTok`
    at each push): identical control flow and table state. Equal to
    `(htMatchIter ..).map packTok` (`htMatchIterP_eq`). -/
def htMatchIterP (data : ByteArray) (windowSize : Nat := 32768) : Array UInt32 :=
  if data.size < 3 then
    trailingP data 0 #[]
  else
    mainLoop data windowSize 32768 32 (.replicate (2 * 32768) data.size) 0
      (Array.emptyWithCapacity data.size)
where
  mainLoop (data : ByteArray) (windowSize hashSize niceLen : Nat)
      (tbl : Array Nat) (pos : Nat) (acc : Array UInt32) : Array UInt32 :=
    if hlt : pos + 2 < data.size then
      let h := lz77Greedy.hash3 data pos hashSize hlt
      let c0 := headProbeGuarded tbl (2 * h)
      let c1 := headProbeGuarded tbl (2 * h + 1)
      let tbl := guardedSet tbl (2 * h + 1) c0
      let tbl := guardedSet tbl (2 * h) pos
      let maxLen := min 258 (data.size - pos)
      have hmaxLenP : pos + maxLen ≤ data.size := by omega
      let m := htProbe data windowSize pos maxLen niceLen hmaxLenP c0 c1
      let matchLen := m.1
      let matchPos := m.2
      if hge : matchLen ≥ 4 then
        if hle : pos + matchLen ≤ data.size then
          have : data.size - (pos + matchLen) < data.size - pos := by omega
          mainLoop data windowSize hashSize niceLen tbl (pos + matchLen)
            (acc.push (packTok (.reference matchLen (pos - matchPos))))
        else
          mainLoop data windowSize hashSize niceLen tbl (pos + 1)
            (acc.push (packTok (.literal (data[pos]'(by omega)))))
      else
        mainLoop data windowSize hashSize niceLen tbl (pos + 1)
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
  let lw := lenCodeWord (((w >>> 16) &&& 0x7FFF).toNat)
  let idx := codeIdx lw
  if hlit : idx + 257 < fixedLitCodes.size then
    let (code, len) := fixedLitCodes[idx + 257]
    let bw := bw.writeHuffCode code len
    let bw := bw.writeBits (codeExtra lw) (codeVal lw)
    let dw := distCodeWord ((w &&& 0xFFFF).toNat)
    let dIdx := codeIdx dw
    if hdist : dIdx < fixedDistCodes.size then
      let (dCode, dLen) := fixedDistCodes[dIdx]
      let bw := bw.writeHuffCode dCode dLen
      bw.writeBits (codeExtra dw) (codeVal dw)
    else bw
  else bw

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
    -- When the four hash bytes are in bounds and the buffer is `USize`-
    -- addressable, read them as one wide load (`ugetUInt32LE`, #2706); its model
    -- is exactly the `a ||| b<<<8 ||| c<<<16 ||| d<<<24` recombination, so the
    -- hash value is identical and all three `hash3` variants stay defeq.
    let word :=
      if h4 : pos + 4 ≤ data.size then
        if hsz : data.size.toUSize.toNat = data.size then
          ByteArray.ugetUInt32LE data pos.toUSize (by
            have hds : data.size < USize.size := by
              rw [← hsz]; exact USize.toNat_lt_two_pow_numBits _
            rw [toUSize_toNat_of_lt (show pos < USize.size by omega)]; omega)
        else
          let a := (data[pos]'(by omega)).toUInt32
          let b := (data[pos + 1]'(by omega)).toUInt32
          let c := (data[pos + 2]'(by omega)).toUInt32
          let d := (data[pos + 3]'(by omega)).toUInt32
          a ||| (b <<< 8) ||| (c <<< 16) ||| (d <<< 24)
      else
        let a := (data[pos]'(by omega)).toUInt32
        let b := (data[pos + 1]'(by omega)).toUInt32
        let c := (data[pos + 2]'(by omega)).toUInt32
        a ||| (b <<< 8) ||| (c <<< 16)
    (((word * 2654435761) >>> 16).toNat % hashSize)
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
