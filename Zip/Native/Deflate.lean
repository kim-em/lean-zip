import Zip.Native.BitWriter
import Zip.Native.Inflate
import Zip.Native.Wide
import Zip.Native.TokenArray
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
    -- check is one `USize` round-trip, no bignum), run the unboxed word-at-a-time
    -- loop `goUW` — proven equal to the `Nat` `go` (`goUW_eq`, which reuses the
    -- byte loop's `goU_eq` for its fallback branches). Else fall back to `go`.
    if hg : data.size.toUSize.toNat = data.size then
      have hsz : data.size < USize.size := by
        rw [← hg]; exact USize.toNat_lt_two_pow_numBits _
      (goUW data p1.toUSize p2.toUSize 0 maxLen.toUSize hsz
        (by rw [toUSize_toNat_of_lt (by omega), toUSize_toNat_of_lt (by omega)]; omega)
        (by rw [toUSize_toNat_of_lt (by omega), toUSize_toNat_of_lt (by omega)]; omega)
        (by simp)).toNat
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
  goUW (data : ByteArray) (p1 p2 i maxLen : USize)
      (hsz : data.size < USize.size)
      (h1 : p1.toNat + maxLen.toNat ≤ data.size)
      (h2 : p2.toNat + maxLen.toNat ≤ data.size)
      (hile : i.toNat ≤ maxLen.toNat) : USize :=
    -- Word-at-a-time match extension (libdeflate `matchfinder_common.h`): while a
    -- full 8-byte window fits (`i + 8 ≤ maxLen`, computed as `8 ≤ maxLen - i` to
    -- avoid `USize` overflow), load both 8-byte words and compare them in one op.
    -- On a full-word match, advance 8; otherwise hand off to the per-byte loop
    -- `goU`, which pinpoints the first mismatch within the window (and the same
    -- `goU` finishes the < 8-byte tail). Proven equal to `go` by `goUW_eq`.
    if h8 : (8 : USize) ≤ maxLen - i then
      have hUS : USize.size = 2 ^ System.Platform.numBits := rfl
      have h8v : (8 : USize).toNat = 8 := by
        rw [USize.toNat_ofNat]
        exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (show 8 < 2 ^ 32 by omega) USize.le_size)
      have h8n : i.toNat + 8 ≤ maxLen.toNat := by
        have h := USize.le_iff_toNat_le.mp h8
        rw [USize.toNat_sub_of_le maxLen i hile, h8v] at h; omega
      have e1 : (p1 + i).toNat = p1.toNat + i.toNat := by
        rw [USize.toNat_add]; apply Nat.mod_eq_of_lt; omega
      have e2 : (p2 + i).toNat = p2.toNat + i.toNat := by
        rw [USize.toNat_add]; apply Nat.mod_eq_of_lt; omega
      have hw1 : (p1 + i).toNat + 8 ≤ data.size := by omega
      have hw2 : (p2 + i).toNat + 8 ≤ data.size := by omega
      let w1 := data.ugetUInt64LE (p1 + i) hw1
      let w2 := data.ugetUInt64LE (p2 + i) hw2
      if w1 == w2 then
        have hile' : (i + 8).toNat ≤ maxLen.toNat := by
          rw [USize.toNat_add, h8v, Nat.mod_eq_of_lt (by omega)]; omega
        goUW data p1 p2 (i + 8) maxLen hsz h1 h2 hile'
      else
        -- Word mismatch: the first differing byte is at
        -- `ctz (w1 XOR w2) >>> 3` within `[i, i+8)` (libdeflate
        -- `matchfinder_common.h`). Return `i + that offset` directly — no
        -- re-scan of the array. Proven equal to the byte loop in `goUW_eq`.
        i + (UInt64.ctz (w1 ^^^ w2) >>> 3).toUSize
    else
      goU data p1 p2 i maxLen hsz h1 h2
  termination_by maxLen.toNat - i.toNat
  decreasing_by
    have hUS : USize.size = 2 ^ System.Platform.numBits := rfl
    have h8v : (8 : USize).toNat = 8 := by
      rw [USize.toNat_ofNat]
      exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (show 8 < 2 ^ 32 by omega) USize.le_size)
    -- `_h8n` (`i + 8 ≤ maxLen`) is consumed by the `omega`s below but never
    -- named, so it carries an underscore to sidestep the unused-variable linter.
    have _h8n : i.toNat + 8 ≤ maxLen.toNat := by
      have h := USize.le_iff_toNat_le.mp h8
      rw [USize.toNat_sub_of_le maxLen i hile, h8v] at h; omega
    have e : (i + 8).toNat = i.toNat + 8 := by
      rw [USize.toNat_add, h8v, Nat.mod_eq_of_lt (by omega)]
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

/-! ## Hash3 singleton table (#2742, libdeflate `hc_matchfinder.h`)

The L9/L10 candidate-cache build (`buildCache` in `DeflateParse.lean`) keys
its chains on the **4-byte** hash (`lz77Greedy.hash3`), so every chain
candidate can extend to length ≥ 4 — but the ratio-maximising DP must also
see length-3 candidates (plain hash4 chains cost x-ray +7.4% /
ooffice +3.5% at L9, the #2620 note). Those come from a chain-less
**singleton** table split by role: `hash3Single` hashes only 3 bytes into a
15-bit table holding the most recent position per bucket, and `hash3Probe`
verifies that candidate before use. Pure heuristic state — the probe
re-verifies the bytes and the window, the cache is opaque to correctness,
and emission re-verifies everything again.

The L1–L8 chain matchers deliberately do **not** probe the singleton: the
measured trade there (#2742) was −15–20% matcher speed at L1–L5 (−6% at
L6–L8) for at best −0.17% geomean ratio even with a zlib-style `TOO_FAR`
cap on the seed distance — inside the adjacent levels' mixing curve, so the
per-position singleton touch does not pay outside the cache build, whose
walk is orders of magnitude deeper per position. -/

/-- 15-bit multiplicative hash of the 3 bytes at `pos` (libdeflate's `hash3`):
    the singleton-table bucket index. Always `< 32768` (a `UInt32 >>> 17` has
    15 bits), so the `guardedSet`/`headProbeGuarded` bounds checks on the
    32768-entry table never fail. The word load mirrors `lz77Greedy.hash3`'s
    (same wide-load/fallback split) so the two per-position loads in
    `buildCache` are common-subexpression candidates; the `&&& 0xFFFFFF` mask
    makes the bucket independent of which load path ran (byte 3 never
    enters), which the singleton's hit rate relies on. -/
@[inline] def hash3Single (data : ByteArray) (pos : Nat) (h : pos + 2 < data.size) : Nat :=
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
  ((((word &&& 0xFFFFFF) * 2654435761)) >>> 17).toNat

/-- Probe result of the hash3 singleton, packed as the single small `Nat`
    `bestPos * 512 + bestLen` (the `chainWalkGuardedPacked` encoding; the
    caller decodes with `% 512` / `/ 512`). Returns `cand3 * 512 + 3` when
    `cand3` is a live in-window position whose three bytes equal those at
    `pos` (a *verified* length-3 match — sentinel or stale entries fail the
    `cand3 < pos` guard, collisions fail the byte compare); otherwise `0`,
    the empty seed. Packed rather than a `Nat × Nat` on purpose: `Prod`
    projections of this call inside a well-founded loop body (`buildCache`)
    send the kernel into deep recursion (the same class of WF-elaboration
    blowup the `buildCache` docstring records for literal constants). -/
@[inline] def hash3Probe (data : ByteArray) (windowSize pos cand3 : Nat)
    (hlt : pos + 2 < data.size) : Nat :=
  if hc : cand3 < pos ∧ pos - cand3 ≤ windowSize then
    if data[cand3]'(by omega) == data[pos]'(by omega) &&
       data[cand3 + 1]'(by omega) == data[pos + 1]'(by omega) &&
       data[cand3 + 2]'(by omega) == data[pos + 2]'(by omega) then
      cand3 * 512 + 3
    else 0
  else 0

/-- Reject length-3 singleton seeds farther than this (zlib `deflate.c`
    `TOO_FAR`): a length-3 match at a large distance costs more bits than three
    literals. The split-tier singleton probe caps its seed distance at
    `min windowSize tooFar3`, exactly as the L9/L10 cache build already does;
    measured optimal at 4096 (#2742 / the split-tier sweep). -/
def tooFar3 : Nat := 4096

/-- The hash3-singleton chain-walk seed at `pos`: when `useH3` is set, read the
    most-recent length-3 candidate from `h3tab` and `hash3Probe`-verify it within
    `min windowSize tooFar3`, returning the packed `cand3*512+3` on a hit (else
    `0`); when `useH3` is clear, the empty seed `0`. The result is *always* a real
    in-window backward match or empty (`h3Seed_spec`), so the seeded chain walk
    may return it and the loop emit it as a verified length-3 reference — this is
    how the split tier (L6–L8) sees the length-3 matches its hash4 chains miss.
    The `h3tab` contents are pure heuristic state: the probe re-verifies the
    bytes and the window, so they never enter a validity proof. -/
@[inline] def h3Seed (useH3 : Bool) (data : ByteArray) (h3tab : Array Nat)
    (windowSize pos : Nat) (hlt : pos + 2 < data.size) : Nat :=
  if useH3 then
    hash3Probe data (min windowSize tooFar3) pos (headProbeGuarded h3tab (hash3Single data pos hlt)) hlt
  else 0

/-- Interior-position hash3-singleton insertion, the length-3 twin of
    `lz77Chain.updateHashes`' chain insertion: for each `j ∈ [j, matchLen)` (also
    `≤ insertCap`) with three readable bytes, store `pos+j` into
    `h3tab[hash3Single data (pos+j)]`. Runs at exactly the interior positions the
    hash4 insertion covers, so the singleton stays as fresh as the chain. Pure
    heuristic state — never enters a validity proof. -/
def updateHash3 (data : ByteArray) (h3tab : Array Nat) (pos j matchLen insertCap : Nat) :
    Array Nat :=
  if j < matchLen ∧ j ≤ insertCap then
    if h : pos + j + 2 < data.size then
      updateHash3 data (guardedSet h3tab (hash3Single data (pos + j) h) (pos + j))
        pos (j + 1) matchLen insertCap
    else
      updateHash3 data h3tab pos (j + 1) matchLen insertCap
  else h3tab
termination_by matchLen - j
decreasing_by all_goals omega

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
    (insertCap : Nat := 1000000000) (niceLen : Nat := 258) :
    Array LZ77Token :=
  if data.size < 3 then
    (lz77Greedy.trailing data 0).toArray
  else
    let hashSize := 65536
    (mainLoop data windowSize hashSize maxChain niceLen
      (.replicate hashSize data.size) (.replicate (min chainWinSize data.size) data.size) 0 insertCap).toArray
where
  /-- Walk the `prev` chain up to `fuel` steps from `cand`, keeping the longest
      in-window match `(bestLen, bestPos)`. Stops at the first out-of-window or
      out-of-range link (`cand ≥ pos`, incl. the `data.size` sentinel). `prev`
      is the fixed-size circular ring indexed by `cand &&& 0x7FFF`; its contents
      are a pure heuristic, so the windowing never enters the validity proof. -/
  chainWalk (data : ByteArray) (prev : Array Nat) (windowSize pos maxLen niceLen : Nat)
      (hpm : pos + maxLen ≤ data.size) (cand fuel bestLen bestPos : Nat) : Nat × Nat :=
    if fuel = 0 then (bestLen, bestPos)
    else if hc : cand < pos ∧ pos - cand ≤ windowSize then
      have hcand : cand + maxLen ≤ data.size := by omega
      let ml := lz77Greedy.countMatch data cand pos maxLen hcand hpm
      let (bl, bp) := if ml > bestLen then (ml, cand) else (bestLen, bestPos)
      -- Early stop: once the best length reaches the level's `niceLen` cutoff (or
      -- the maximum possible `maxLen`, whichever is smaller) the match is already
      -- good enough, so stop walking the chain (libdeflate `nice_match_length`).
      -- The `maxLen` stop alone is provably zero ratio loss; a `niceLen < maxLen`
      -- cutoff trades a little ratio for a shorter walk at the deep levels.
      if bl ≥ min niceLen maxLen then (bl, bp)
      else chainWalk data prev windowSize pos maxLen niceLen hpm prev[cand &&& 0x7FFF]! (fuel - 1) bl bp
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
  mainLoop (data : ByteArray) (windowSize hashSize maxChain niceLen : Nat)
      (hashTable : Array Nat) (prev : Array Nat) (pos insertCap : Nat) : List LZ77Token :=
    if hlt : pos + 2 < data.size then
      let h := lz77Greedy.hash3 data pos hashSize hlt
      let head := headProbeGuarded hashTable h
      let hashTable := guardedSet hashTable h pos
      let prev := guardedSet prev (pos &&& 0x7FFF) head
      let maxLen := min 258 (data.size - pos)
      have hmaxLenP : pos + maxLen ≤ data.size := by omega
      let m := chainWalk data prev windowSize pos maxLen niceLen hmaxLenP head maxChain 0 0
      let matchLen := m.1
      let matchPos := m.2
      if hge : matchLen ≥ 3 then
        if hle : pos + matchLen ≤ data.size then
          have : data.size - (pos + matchLen) < data.size - pos := by omega
          let (hashTable, prev) := updateHashes data hashSize hashTable prev pos 1 matchLen insertCap
          .reference matchLen (pos - matchPos) ::
            mainLoop data windowSize hashSize maxChain niceLen hashTable prev (pos + matchLen) insertCap
        else
          .literal (data[pos]'(by omega)) ::
            mainLoop data windowSize hashSize maxChain niceLen hashTable prev (pos + 1) insertCap
      else
        .literal (data[pos]'(by omega)) ::
          mainLoop data windowSize hashSize maxChain niceLen hashTable prev (pos + 1) insertCap
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
def chainWalkFast (data : ByteArray) (prev : Array Nat) (windowSize pos maxLen niceLen : Nat)
    (hpm : pos + maxLen ≤ data.size) (hps : min chainWinSize data.size ≤ prev.size)
    (cand fuel bestLen bestPos : Nat) : Nat × Nat :=
  if fuel = 0 then (bestLen, bestPos)
  else if hc : cand < pos ∧ pos - cand ≤ windowSize then
    have hcand : cand + maxLen ≤ data.size := by omega
    let ml := lz77Greedy.countMatch data cand pos maxLen hcand hpm
    let (bl, bp) := if ml > bestLen then (ml, cand) else (bestLen, bestPos)
    if bl ≥ min niceLen maxLen then (bl, bp)
    else chainWalkFast data prev windowSize pos maxLen niceLen hpm hps
      (prev[cand &&& 0x7FFF]'(by have := winMask_lt cand; have := Nat.and_le_left (n := cand) (m := 0x7FFF); omega)) (fuel - 1) bl bp
  else (bestLen, bestPos)
termination_by fuel
decreasing_by omega

/-- One runtime `min chainWinSize data.size ≤ prev.size` check guards the whole `chainWalkFast`
    inner loop; the (unreachable, since `prev` is the fixed 32768-entry ring)
    fallback is the original panic-checked walk, so this equals `lz77Chain.chainWalk`. -/
@[inline] def chainWalkGuarded (data : ByteArray) (prev : Array Nat)
    (windowSize pos maxLen niceLen : Nat) (hpm : pos + maxLen ≤ data.size)
    (cand fuel bestLen bestPos : Nat) : Nat × Nat :=
  if hps : min chainWinSize data.size ≤ prev.size then
    chainWalkFast data prev windowSize pos maxLen niceLen hpm hps cand fuel bestLen bestPos
  else
    lz77Chain.chainWalk data prev windowSize pos maxLen niceLen hpm cand fuel bestLen bestPos

/-- Packed-result copy of `chainWalkFast` (Wave 5 de-boxing): the identical
    walk, but the `(bestLen, bestPos)` accumulator is carried and returned as
    the single small `Nat` `bestPos * 512 + bestLen`, so the per-position hot
    call allocates no pair constructor (and no per-step `(bl, bp)` pair
    either). `bestLen` never exceeds `maxLen`, which every call site clamps to
    `min 258 _ < 512`, so the call sites decode exactly with `% 512` / `/ 512`
    (`chainWalkGuardedPacked_mod`/`_div` in `LZ77ChainCorrect`, via the
    lockstep equality `chainWalkPacked_eq`). -/
def chainWalkPacked (data : ByteArray) (prev : Array Nat) (windowSize pos maxLen niceLen : Nat)
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
      -- Prefilter miss keeps `bestLen` unchanged; mirror `chainWalkFast`'s early
      -- stop so the two stay in lockstep (`chainWalkPacked_eq` holds for *any*
      -- `bestLen`, unconditionally). From the matcher call sites — which start at
      -- `bestLen = 0` and, on the non-skip branch, return the moment `bestLen`
      -- reaches the cutoff — every recursive call has `bestLen < min niceLen maxLen`,
      -- so this test is a well-predicted always-false branch on the hot skip path.
      if bestLen ≥ min niceLen maxLen then bestPos * 512 + bestLen
      else chainWalkPacked data prev windowSize pos maxLen niceLen hpm hps
        (prev[cand &&& 0x7FFF]'(by have := winMask_lt cand; have := Nat.and_le_left (n := cand) (m := 0x7FFF); omega)) (fuel - 1) bestLen bestPos
    else
      let ml := lz77Greedy.countMatch data cand pos maxLen hcand hpm
      let bl := if ml > bestLen then ml else bestLen
      let bp := if ml > bestLen then cand else bestPos
      if bl ≥ min niceLen maxLen then bp * 512 + bl
      else chainWalkPacked data prev windowSize pos maxLen niceLen hpm hps
        (prev[cand &&& 0x7FFF]'(by have := winMask_lt cand; have := Nat.and_le_left (n := cand) (m := 0x7FFF); omega)) (fuel - 1) bl bp
  else bestPos * 512 + bestLen
termination_by fuel
decreasing_by all_goals omega

/-- One runtime `min chainWinSize data.size ≤ prev.size` check guards the whole `chainWalkPacked`
    inner loop; the (unreachable) fallback packs the reference walk's pair, so
    this equals `bestPos * 512 + bestLen` of `lz77Chain.chainWalk`
    (`chainWalkGuardedPacked_eq`). -/
@[inline] def chainWalkGuardedPacked (data : ByteArray) (prev : Array Nat)
    (windowSize pos maxLen niceLen : Nat) (hpm : pos + maxLen ≤ data.size)
    (cand fuel bestLen bestPos : Nat) : Nat :=
  if hps : min chainWinSize data.size ≤ prev.size then
    chainWalkPacked data prev windowSize pos maxLen niceLen hpm hps cand fuel bestLen bestPos
  else
    let p := lz77Chain.chainWalk data prev windowSize pos maxLen niceLen hpm cand fuel bestLen bestPos
    p.2 * 512 + p.1

/-- USize-native de-boxed twin of `chainWalkPacked` (Wave 7 P1b): the per-position
    chain-walk bookkeeping — the fuel counter, the best-length/best-position
    accumulator, and the `scan_end` prefilter's index arithmetic — runs on unboxed
    `USize` rather than tagged `Nat`, so the hot loop pays no per-step tag test /
    untag on its scalar arithmetic. The chain link `cand` itself stays `Nat`: it is
    read straight from the `Nat` `prev` ring and handed to `countMatch` and the mask
    index with no conversion, matching the measured `UInt32`-ring tax the
    `chainWinSize` docstring records — only the accumulators move to `USize`. One
    runtime `data.size < USize.size` addressability witness (`hsz`, established by
    the guarded wrapper exactly as `countMatch` does for `goUW`) makes every
    `USize` add faithful, and the result is repacked into the `Nat`
    `bestPos * 512 + bestLen` at the leaves via `.toNat`, so no `USize` multiply can
    overflow. The invariant `USize` copies of `pos`/`maxLen`/`min niceLen maxLen`
    (`posU`/`maxLenU`/`cutoffU`, computed once by the wrapper) carry their `toNat`
    identities so the loop never reconverts them. Proven equal to `chainWalkPacked`
    (`chainWalkPackedU_eq`). -/
def chainWalkPackedU (data : ByteArray) (prev : Array Nat)
    (windowSize pos maxLen niceLen : Nat) (hpm : pos + maxLen ≤ data.size)
    (hps : min chainWinSize data.size ≤ prev.size) (hsz : data.size < USize.size)
    (posU maxLenU cutoffU : USize) (hposU : posU.toNat = pos) (hmaxU : maxLenU.toNat = maxLen)
    (hcutU : cutoffU.toNat = min niceLen maxLen)
    (cand : Nat) (fuelU bestLenU bestPosU : USize) : Nat :=
  if fuelU = 0 then bestPosU.toNat * 512 + bestLenU.toNat
  else if hc : cand < pos ∧ pos - cand ≤ windowSize then
    have hUS : USize.size = 2 ^ System.Platform.numBits := rfl
    have hcand : cand + maxLen ≤ data.size := by omega
    have hcandlt : cand < USize.size := by omega
    let candU : USize := cand.toUSize
    have hcandU : candU.toNat = cand := toUSize_toNat_of_lt hcandlt
    let skip : Bool := if hbl : bestLenU < maxLenU then
        have hbln : bestLenU.toNat < maxLen := by rw [← hmaxU]; exact USize.lt_iff_toNat_lt.mp hbl
        have hb1 : (candU + bestLenU).toNat < data.size := by
          have e : (candU + bestLenU).toNat = cand + bestLenU.toNat := by
            rw [USize.toNat_add, hcandU]; apply Nat.mod_eq_of_lt; omega
          omega
        have hb2 : (posU + bestLenU).toNat < data.size := by
          have e : (posU + bestLenU).toNat = pos + bestLenU.toNat := by
            rw [USize.toNat_add, hposU]; apply Nat.mod_eq_of_lt; omega
          omega
        data.uget (candU + bestLenU) hb1 != data.uget (posU + bestLenU) hb2
      else false
    if skip then
      if bestLenU ≥ cutoffU then bestPosU.toNat * 512 + bestLenU.toNat
      else chainWalkPackedU data prev windowSize pos maxLen niceLen hpm hps hsz posU maxLenU cutoffU
        hposU hmaxU hcutU
        (prev[cand &&& 0x7FFF]'(by have h1 := winMask_lt cand; have h2 := Nat.and_le_left (n := cand) (m := 0x7FFF); simp only [chainWinSize] at h1 hps; omega))
        (fuelU - 1) bestLenU bestPosU
    else
      let ml := lz77Greedy.countMatch data cand pos maxLen hcand hpm
      let mlU : USize := ml.toUSize
      let blU : USize := if mlU > bestLenU then mlU else bestLenU
      let bpU : USize := if mlU > bestLenU then candU else bestPosU
      if blU ≥ cutoffU then bpU.toNat * 512 + blU.toNat
      else chainWalkPackedU data prev windowSize pos maxLen niceLen hpm hps hsz posU maxLenU cutoffU
        hposU hmaxU hcutU
        (prev[cand &&& 0x7FFF]'(by have h1 := winMask_lt cand; have h2 := Nat.and_le_left (n := cand) (m := 0x7FFF); simp only [chainWinSize] at h1 hps; omega))
        (fuelU - 1) blU bpU
  else bestPosU.toNat * 512 + bestLenU.toNat
termination_by fuelU.toNat
decreasing_by
  all_goals
    have hfz : ¬ fuelU = 0 := by assumption
    have hpos : 0 < fuelU.toNat := by
      rcases Nat.eq_zero_or_pos fuelU.toNat with h | h
      · exact absurd (USize.toNat_inj.mp (by rw [h, USize.toNat_zero])) hfz
      · exact h
    have hle : (1 : USize) ≤ fuelU := by rw [USize.le_iff_toNat_le, USize.toNat_one]; omega
    have heq : (fuelU - 1).toNat = fuelU.toNat - 1 := by
      rw [USize.toNat_sub_of_le _ _ hle, USize.toNat_one]
    omega

/-- One runtime addressability + accumulator-faithfulness check guards the whole
    `chainWalkPackedU` inner loop: the single `Nat`-round-trip test
    `data.size.toUSize.toNat = data.size` witnesses `data.size < USize.size` (the
    `hsz` the loop needs), and the three `_.toUSize.toNat = _` conjuncts witness
    that `fuel`/`bestLen`/`bestPos` are representable. Every miss (never taken for
    the production matcher: `data.size` fits a `size_t`, `fuel = maxChain` is tiny,
    and the walk starts at `bestLen = bestPos = 0`) falls back to `chainWalkPacked`,
    so this equals `chainWalkGuardedPacked` (`chainWalkGuardedPackedU_eq`). -/
@[inline] def chainWalkGuardedPackedU (data : ByteArray) (prev : Array Nat)
    (windowSize pos maxLen niceLen : Nat) (hpm : pos + maxLen ≤ data.size)
    (cand fuel bestLen bestPos : Nat) : Nat :=
  if hps : min chainWinSize data.size ≤ prev.size then
    if hg : data.size.toUSize.toNat = data.size ∧ fuel.toUSize.toNat = fuel ∧
        bestLen.toUSize.toNat = bestLen ∧ bestPos.toUSize.toNat = bestPos then
      have hsz : data.size < USize.size := by rw [← hg.1]; exact USize.toNat_lt_two_pow_numBits _
      chainWalkPackedU data prev windowSize pos maxLen niceLen hpm hps hsz
        pos.toUSize maxLen.toUSize (min niceLen maxLen).toUSize
        (toUSize_toNat_of_lt (by omega)) (toUSize_toNat_of_lt (by omega))
        (toUSize_toNat_of_lt (by omega)) cand fuel.toUSize bestLen.toUSize bestPos.toUSize
    else
      chainWalkPacked data prev windowSize pos maxLen niceLen hpm hps cand fuel bestLen bestPos
  else
    let p := lz77Chain.chainWalk data prev windowSize pos maxLen niceLen hpm cand fuel bestLen bestPos
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
    (insertCap : Nat := 1000000000) (niceLen : Nat := 258) :
    Array LZ77Token :=
  if data.size < 3 then
    lz77GreedyIter.trailing data 0 #[]
  else
    let hashSize := 65536
    mainLoop data windowSize hashSize maxChain insertCap niceLen
      (.replicate hashSize data.size) (.replicate (min chainWinSize data.size) data.size) 0 #[]
where
  mainLoop (data : ByteArray) (windowSize hashSize maxChain insertCap niceLen : Nat)
      (hashTable : Array Nat) (prev : Array Nat) (pos : Nat) (acc : Array LZ77Token) :
      Array LZ77Token :=
    if hlt : pos + 2 < data.size then
      let h := lz77Greedy.hash3 data pos hashSize hlt
      let head := headProbeGuarded hashTable h
      let hashTable := guardedSet hashTable h pos
      let prev := guardedSet prev (pos &&& 0x7FFF) head
      let maxLen := min 258 (data.size - pos)
      have hmaxLenP : pos + maxLen ≤ data.size := by omega
      let r := chainWalkGuardedPacked data prev windowSize pos maxLen niceLen hmaxLenP head maxChain 0 0
      let matchLen := r % 512
      let matchPos := r / 512
      if hge : matchLen ≥ 3 then
        if hle : pos + matchLen ≤ data.size then
          have : data.size - (pos + matchLen) < data.size - pos := by omega
          let (hashTable, prev) :=
            updateHashesGuarded data hashSize hashTable prev pos 1 matchLen insertCap
          mainLoop data windowSize hashSize maxChain insertCap niceLen hashTable prev (pos + matchLen)
            (acc.push (.reference matchLen (pos - matchPos)))
        else
          mainLoop data windowSize hashSize maxChain insertCap niceLen hashTable prev (pos + 1)
            (acc.push (.literal (data[pos]'(by omega))))
      else
        mainLoop data windowSize hashSize maxChain insertCap niceLen hashTable prev (pos + 1)
          (acc.push (.literal (data[pos]'(by omega))))
    else
      lz77GreedyIter.trailing data pos acc
  termination_by data.size - pos
  decreasing_by all_goals omega

/-- libdeflate's cost-based lazy accept rule (`deflate_compress.c`, the first
    lookahead step). The lazy matcher prefers the `pos+1` match `(len2, dist2)`
    over the `pos` match `(len1, dist1)` when it is strictly longer **and** the
    length gain pays for the extra offset bits: `4·Δlen + bsr(dist1) − bsr(dist2)
    > 2`, where `bsr x = ⌊log2 x⌋` counts a distance's offset bits (written with
    additions on both sides so the `Nat` subtractions never truncate).

    This replaces the older conservative rule `len2 > len1 ∧ dist2 ≤ dist1`
    (accept a longer match only when it is *no farther*), which rejected every
    longer-but-farther match outright. The cost rule instead admits a farther
    match once its length gain outweighs the ⌈log2⌉ offset-bit cost — exactly the
    longer-but-farther deferrals a Huffman-distance model rewards. Measured
    (#2765, `lazy2-sweep`) at −0.4 %…−0.9 % Silesia/Canterbury ratio across
    *every* lazy level (4–9) and every file type — text (xml −2.0 %, dickens
    −0.8 %) and binary (osdb −1.6 %, mozilla −0.3 %, sao −0.2 %) alike, with no
    regression anywhere — at negligible cost (one `Nat.log2` per deferral, no
    extra chain walk). A two-position (`pos+2`) lookahead was measured alongside
    and rejected: it added ≤0.06 % for a second chain walk per position and a new
    proof branch.

    Purely a choice among valid matches — every emitted reference is re-verified
    at emission (`chainWalk_spec` holds for any chain state and any deferral
    predicate), so the rule never enters the correctness proof; the matcher
    contracts hold for any accept predicate. -/
@[inline] def lazyAcceptCost (len1 dist1 len2 dist2 : Nat) : Bool :=
  decide (len1 < len2) && decide (4 * (len2 - len1) + dist1.log2 > 2 + dist2.log2)

/-- Accepting the lookahead match implies it is strictly longer — the correctness
    proofs use this to rule out the "no match at `pos+1`" case. -/
theorem lazyAcceptCost_lt {len1 dist1 len2 dist2 : Nat}
    (h : lazyAcceptCost len1 dist1 len2 dist2 = true) : len1 < len2 := by
  simp only [lazyAcceptCost, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

/-- Chain depth for a rolling-lazy2 follow-up probe (`rollDefer`). Mirrors the
    certified spike's mode-0 ladder (`bench/ZipLazyRollSweep.lean`, #2837): a
    constant `maxChain / 4` after the main loop's own full-depth `pos+1` probe,
    floored at 1 so a probe never runs at zero fuel. A pure heuristic — depth
    never enters a validity proof (`chainWalk_spec` holds for any fuel). -/
@[inline] def lazy2ProbeDepth (maxChain : Nat) : Nat :=
  max 1 (maxChain / 4)

/-! Rolling multi-step deferral for `lz77ChainLazy` (rung 1 of #2837). `mainLoop`
    is the boxed lazy matcher extended with a `lazy2Steps` knob: when the accept
    rule fires and steps remain (`1 < lazy2Steps`), it emits the pending
    match-start byte as a literal and enters `rollDefer`, which keeps deferring
    while each next position strictly improves the pending match (libdeflate's
    `deflate_compress_lazy2` loop). `lazy2Steps = 1` never enters `rollDefer` — it
    is the original single-deferral behavior verbatim, so every downstream `_eq`
    holds at the default. Match-finding stays opaque to correctness
    (`chainWalk_spec` for any chain state), and every emitted reference is
    re-verified at emission, so the roll's chain state never enters a proof. -/
mutual

def lz77ChainLazy.mainLoop (data : ByteArray) (windowSize hashSize maxChain : Nat) (useH3 : Bool)
    (hashTable : Array Nat) (prev h3tab : Array Nat) (pos insertCap goodMatch niceLen lazyDepth lazy2Steps : Nat) : List LZ77Token :=
  if hlt : pos + 2 < data.size then
    let h := lz77Greedy.hash3 data pos hashSize hlt
    let head := headProbeGuarded hashTable h
    let hashTable := guardedSet hashTable h pos
    let prev := guardedSet prev (pos &&& 0x7FFF) head
    let seed := h3Seed useH3 data h3tab windowSize pos hlt
    let h3tab := if useH3 then guardedSet h3tab (hash3Single data pos hlt) pos else h3tab
    let maxLen := min 258 (data.size - pos)
    have hmaxLenP : pos + maxLen ≤ data.size := by omega
    let m := lz77Chain.chainWalk data prev windowSize pos maxLen niceLen hmaxLenP head maxChain (seed % 512) (seed / 512)
    let matchLen := m.1
    let matchPos := m.2
    if hge : matchLen ≥ 3 then
      if hle : pos + matchLen ≤ data.size then
        if h3lt : pos + 3 < data.size then
          if matchLen < goodMatch then
            let h2 := lz77Greedy.hash3 data (pos + 1) hashSize (by omega)
            let head2 := headProbeGuarded hashTable h2
            let maxLen2 := min 258 (data.size - (pos + 1))
            have hmaxLen2P : (pos + 1) + maxLen2 ≤ data.size := by omega
            let m2 :=
              lz77Chain.chainWalk data prev windowSize (pos + 1) maxLen2 niceLen hmaxLen2P head2 lazyDepth 0 0
            let matchLen2 := m2.1
            let matchPos2 := m2.2
            if lazyAcceptCost matchLen (pos - matchPos) matchLen2 (pos + 1 - matchPos2) then
              if hle2 : pos + 1 + matchLen2 ≤ data.size then
                if h1 : 1 < lazy2Steps then
                  -- Rolling deferral (rung 1 of #2837): emit the pending
                  -- match-start byte as a literal, roll the pending match `M'`
                  -- forward into `rollDefer` at `pos+1`, step 1. `rollDefer` re-derives
                  -- its bounds locally (rung 5 of #2837): no dependent proof-args cross
                  -- the mutual boundary, keeping the lockstep proofs motive-correct.
                  .literal (data[pos]'(by omega)) ::
                    lz77ChainLazy.rollDefer data windowSize hashSize maxChain useH3
                      hashTable prev h3tab (pos + 1) matchLen2 matchPos2 1
                      insertCap goodMatch niceLen lazyDepth lazy2Steps
                else
                  -- Single deferral (`lazy2Steps ≤ 1`): the original lazy behavior.
                  have : data.size - (pos + 1 + matchLen2) < data.size - pos := by omega
                  let (hashTable, prev) :=
                    lz77Chain.updateHashes data hashSize hashTable prev pos 1 (matchLen2 + 1) insertCap
                  let h3tab := if useH3 then updateHash3 data h3tab pos 1 (matchLen2 + 1) insertCap else h3tab
                  .literal (data[pos]'(by omega)) ::
                    .reference matchLen2 (pos + 1 - matchPos2) ::
                      lz77ChainLazy.mainLoop data windowSize hashSize maxChain useH3 hashTable prev h3tab (pos + 1 + matchLen2) insertCap goodMatch niceLen lazyDepth lazy2Steps
              else
                have : data.size - (pos + matchLen) < data.size - pos := by omega
                let (hashTable, prev) :=
                  lz77Chain.updateHashes data hashSize hashTable prev pos 1 matchLen insertCap
                let h3tab := if useH3 then updateHash3 data h3tab pos 1 matchLen insertCap else h3tab
                .reference matchLen (pos - matchPos) ::
                  lz77ChainLazy.mainLoop data windowSize hashSize maxChain useH3 hashTable prev h3tab (pos + matchLen) insertCap goodMatch niceLen lazyDepth lazy2Steps
            else
              have : data.size - (pos + matchLen) < data.size - pos := by omega
              let (hashTable, prev) :=
                lz77Chain.updateHashes data hashSize hashTable prev pos 1 matchLen insertCap
              let h3tab := if useH3 then updateHash3 data h3tab pos 1 matchLen insertCap else h3tab
              .reference matchLen (pos - matchPos) ::
                lz77ChainLazy.mainLoop data windowSize hashSize maxChain useH3 hashTable prev h3tab (pos + matchLen) insertCap goodMatch niceLen lazyDepth lazy2Steps
          else
            -- Gated: long first match, skip the lookahead; still insert interior hashes.
            have : data.size - (pos + matchLen) < data.size - pos := by omega
            let (hashTable, prev) :=
              lz77Chain.updateHashes data hashSize hashTable prev pos 1 matchLen insertCap
            let h3tab := if useH3 then updateHash3 data h3tab pos 1 matchLen insertCap else h3tab
            .reference matchLen (pos - matchPos) ::
              lz77ChainLazy.mainLoop data windowSize hashSize maxChain useH3 hashTable prev h3tab (pos + matchLen) insertCap goodMatch niceLen lazyDepth lazy2Steps
        else
          -- Near end of data: keep match at pos
          have : data.size - (pos + matchLen) < data.size - pos := by omega
          .reference matchLen (pos - matchPos) ::
            lz77ChainLazy.mainLoop data windowSize hashSize maxChain useH3 hashTable prev h3tab (pos + matchLen) insertCap goodMatch niceLen lazyDepth lazy2Steps
      else
        .literal (data[pos]'(by omega)) ::
          lz77ChainLazy.mainLoop data windowSize hashSize maxChain useH3 hashTable prev h3tab (pos + 1) insertCap goodMatch niceLen lazyDepth lazy2Steps
    else
      .literal (data[pos]'(by omega)) ::
        lz77ChainLazy.mainLoop data windowSize hashSize maxChain useH3 hashTable prev h3tab (pos + 1) insertCap goodMatch niceLen lazyDepth lazy2Steps
  else
    lz77Greedy.trailing data pos
termination_by 2 * (data.size - pos)
decreasing_by all_goals (first | omega | (refine Nat.mul_lt_mul_of_pos_left ?_ (by decide); omega))

/-- Rolling sub-recursion: a pending match `(pLen, pMatchPos)` starts at `mp`;
    positions `< mp` are already decided. If a defer remains (`step < lazy2Steps`,
    room, and the pending match is short) and re-probing `mp+1` at
    `lazy2ProbeDepth` strictly improves it (`lazyAcceptCost`), emit `lit(mp)` and
    roll to the new match at `mp+1`, step `+1`. Otherwise commit the pending match
    at `mp`. The no-more-defers commit uses the production batch
    `updateHashes (mp-1) 1 (pLen+1)`, so `mainLoop`'s `lazy2Steps = 1` entry (which
    never reaches here) matches production exactly. Rung 5 of #2837: no `hmp`/`hpl`
    proof-args — the termination bound is re-derived locally from `hcan`, and the
    mutual uses an interleaved measure (`2*(data.size-mp)+1`) so the commit back into
    `mainLoop` always decreases without a pending-length hypothesis. This keeps the
    chain walk out of every dependent proof-arg, so the lockstep rewrites stay
    motive-correct. The emitted reference's validity is re-established at emission
    (see `LZ77ChainLazyCorrect`). -/
def lz77ChainLazy.rollDefer (data : ByteArray) (windowSize hashSize maxChain : Nat) (useH3 : Bool)
    (hashTable : Array Nat) (prev h3tab : Array Nat)
    (mp pLen pMatchPos step insertCap goodMatch niceLen lazyDepth lazy2Steps : Nat) : List LZ77Token :=
  if hcan : step < lazy2Steps ∧ mp + 3 < data.size ∧ pLen < goodMatch then
    -- Insert `mp` (loop-top style) so `mp+1` can match against it.
    let hmh := lz77Greedy.hash3 data mp hashSize (by omega)
    let headmp := headProbeGuarded hashTable hmh
    let hashTable := guardedSet hashTable hmh mp
    let prev := guardedSet prev (mp &&& 0x7FFF) headmp
    let h3tab := if useH3 then guardedSet h3tab (hash3Single data mp (by omega)) mp else h3tab
    -- Probe `mp+1` at the ladder depth. Unseeded (0,0): a length seed only changes
    -- a rejected result, and acceptance needs `len' > pLen` strictly (matches the
    -- seeded spike's accepted output exactly), so this stays validity-provable.
    let h2 := lz77Greedy.hash3 data (mp + 1) hashSize (by omega)
    let head2 := headProbeGuarded hashTable h2
    let maxLen2 := min 258 (data.size - (mp + 1))
    have hmaxLen2P : (mp + 1) + maxLen2 ≤ data.size := by omega
    let m2 := lz77Chain.chainWalk data prev windowSize (mp + 1) maxLen2 niceLen hmaxLen2P head2 (lazy2ProbeDepth maxChain) 0 0
    let len' := m2.1
    let pos' := m2.2
    if lazyAcceptCost pLen (mp - pMatchPos) len' (mp + 1 - pos') = true ∧ (mp + 1) + len' ≤ data.size then
      .literal (data[mp]'(by omega)) ::
        lz77ChainLazy.rollDefer data windowSize hashSize maxChain useH3
          hashTable prev h3tab (mp + 1) len' pos' (step + 1)
          insertCap goodMatch niceLen lazyDepth lazy2Steps
    else
      -- No improvement: commit the pending match at `mp`. `mp` already inserted
      -- above, so insert only the interior `mp+1 .. mp+pLen-1`.
      let (hashTable, prev) := lz77Chain.updateHashes data hashSize hashTable prev mp 1 pLen insertCap
      let h3tab := if useH3 then updateHash3 data h3tab mp 1 pLen insertCap else h3tab
      .reference pLen (mp - pMatchPos) ::
        lz77ChainLazy.mainLoop data windowSize hashSize maxChain useH3 hashTable prev h3tab (mp + pLen) insertCap goodMatch niceLen lazyDepth lazy2Steps
  else
    -- No more defers: commit the pending match at `mp` via the production batch
    -- `updateHashes (mp-1) 1 (pLen+1)` (inserts `mp .. mp+pLen-1`).
    let (hashTable, prev) := lz77Chain.updateHashes data hashSize hashTable prev (mp - 1) 1 (pLen + 1) insertCap
    let h3tab := if useH3 then updateHash3 data h3tab (mp - 1) 1 (pLen + 1) insertCap else h3tab
    .reference pLen (mp - pMatchPos) ::
      lz77ChainLazy.mainLoop data windowSize hashSize maxChain useH3 hashTable prev h3tab (mp + pLen) insertCap goodMatch niceLen lazyDepth lazy2Steps
termination_by 2 * (data.size - mp) + 1
decreasing_by all_goals omega

end

/-- Lazy (one-byte-lookahead, zlib `deflate_slow`-style) variant of `lz77Chain`.
    At each position it finds the best chain match `M` at `pos`; before emitting it
    runs a *second* `chainWalk` at `pos+1` for `M'`. It defers — emits a literal at
    `pos` and takes `M'` (advancing to `pos+1+len M'`) — when `lazyAcceptCost`
    (libdeflate's cost rule: `M'` strictly longer and its length gain pays for the
    extra offset bits) holds; otherwise it emits `M` (advancing to `pos+len M`).
    The accept rule is the ratio lever — see `lazyAcceptCost` for the measured
    win and why the older "longer and no farther" guard was replaced. It is not a
    global optimum — the shallow levels still lose to a Huffman-distribution
    effect no *local* deferral rule captures (that needs the cost-model parse of
    #2526 part 2).

    The lookahead walk at `pos+1` runs at `lazyDepth` chain steps, a separate knob
    from the `pos` walk's `maxChain`. It defaults to `maxChain` (full-depth probe,
    the original behavior); callers pass a reduced value (libdeflate probes its
    first lookahead at *half* depth) to buy back the second full-depth walk each
    matched position otherwise pays. Depth is a pure heuristic — `chainWalk_spec`
    holds for any fuel — so any `lazyDepth` keeps the encoder contracts.

    Match-finding stays opaque to correctness — `chainWalk_spec` holds for *any*
    chain state and *any* deferral predicate, so validity is re-established at
    emission exactly as for `lz77Chain`. `pos+1` is intentionally *not* inserted
    before the lookahead walk (you cannot match a position against itself; matches
    zlib, and is correctness-irrelevant). Reuses `lz77Chain`'s `chainWalk`/
    `updateHashes` and `lz77Greedy.trailing`. Equal-quality contracts proven in
    `LZ77ChainLazyCorrect`. -/
def lz77ChainLazy (data : ByteArray) (maxChain : Nat) (windowSize : Nat := 32768)
    (insertCap : Nat := 1000000000) (goodMatch : Nat := 259) (niceLen : Nat := 258)
    (lazyDepth : Nat := maxChain) (useH3 : Bool := false) (lazy2Steps : Nat := 1) :
    Array LZ77Token :=
  if data.size < 3 then
    (lz77Greedy.trailing data 0).toArray
  else
    let hashSize := 65536
    (lz77ChainLazy.mainLoop data windowSize hashSize maxChain useH3
      (.replicate hashSize data.size) (.replicate (min chainWinSize data.size) data.size)
      (.replicate 32768 data.size) 0 insertCap goodMatch niceLen lazyDepth lazy2Steps).toArray

/-! Iterative (accumulator) twin of the rolling-lazy2 boxed `mutual`
    (`lz77ChainLazy.mainLoop`/`rollDefer`), threading the `lazy2Steps` knob (rung 2
    of #2837). `lz77ChainLazyIter.mainLoop` mirrors the boxed `mainLoop` branch for
    branch (push vs. cons at each emission, `chainWalkGuardedPacked`'s packed
    result vs. `chainWalk`'s pair, `updateHashesGuarded` vs. `updateHashes`), and
    its rolling arm forwards into `lz77ChainLazyIter.rollDefer`, the accumulator
    twin of `rollDefer`. `lazy2Steps = 1` (the default and the only value any call
    site passes) never enters `rollDefer`, so production output is byte-identical.
    Proven equal to the boxed matchers in `LZ77ChainLazyCorrect`. -/
mutual

def lz77ChainLazyIter.mainLoop (data : ByteArray) (windowSize hashSize maxChain insertCap goodMatch niceLen lazyDepth lazy2Steps : Nat) (useH3 : Bool)
    (hashTable : Array Nat) (prev h3tab : Array Nat) (pos : Nat) (acc : Array LZ77Token) :
    Array LZ77Token :=
  if hlt : pos + 2 < data.size then
    let h := lz77Greedy.hash3 data pos hashSize hlt
    let head := headProbeGuarded hashTable h
    let hashTable := guardedSet hashTable h pos
    let prev := guardedSet prev (pos &&& 0x7FFF) head
    let seed := h3Seed useH3 data h3tab windowSize pos hlt
    let h3tab := if useH3 then guardedSet h3tab (hash3Single data pos hlt) pos else h3tab
    let maxLen := min 258 (data.size - pos)
    have hmaxLenP : pos + maxLen ≤ data.size := by omega
    let r := chainWalkGuardedPacked data prev windowSize pos maxLen niceLen hmaxLenP head maxChain (seed % 512) (seed / 512)
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
              chainWalkGuardedPacked data prev windowSize (pos + 1) maxLen2 niceLen hmaxLen2P head2 lazyDepth 0 0
            let matchLen2 := r2 % 512
            let matchPos2 := r2 / 512
            if lazyAcceptCost matchLen (pos - matchPos) matchLen2 (pos + 1 - matchPos2) then
              if hle2 : pos + 1 + matchLen2 ≤ data.size then
                if h1 : 1 < lazy2Steps then
                  -- Rolling deferral: push the pending match-start byte as a
                  -- literal and roll into `rollDefer` at `pos+1`, step 1 (rung 5:
                  -- no proof-args cross the mutual boundary).
                  lz77ChainLazyIter.rollDefer data windowSize hashSize maxChain insertCap goodMatch niceLen lazyDepth lazy2Steps useH3
                    hashTable prev h3tab (pos + 1) matchLen2 matchPos2 1
                    (acc.push (.literal (data[pos]'(by omega))))
                else
                  -- Single deferral (`lazy2Steps ≤ 1`): the original lazy behavior.
                  have : data.size - (pos + 1 + matchLen2) < data.size - pos := by omega
                  let (hashTable, prev) :=
                    updateHashesGuarded data hashSize hashTable prev pos 1 (matchLen2 + 1) insertCap
                  let h3tab := if useH3 then updateHash3 data h3tab pos 1 (matchLen2 + 1) insertCap else h3tab
                  lz77ChainLazyIter.mainLoop data windowSize hashSize maxChain insertCap goodMatch niceLen lazyDepth lazy2Steps useH3 hashTable prev h3tab (pos + 1 + matchLen2)
                    (acc.push (.literal (data[pos]'(by omega))) |>.push
                      (.reference matchLen2 (pos + 1 - matchPos2)))
              else
                have : data.size - (pos + matchLen) < data.size - pos := by omega
                let (hashTable, prev) :=
                  updateHashesGuarded data hashSize hashTable prev pos 1 matchLen insertCap
                let h3tab := if useH3 then updateHash3 data h3tab pos 1 matchLen insertCap else h3tab
                lz77ChainLazyIter.mainLoop data windowSize hashSize maxChain insertCap goodMatch niceLen lazyDepth lazy2Steps useH3 hashTable prev h3tab (pos + matchLen)
                  (acc.push (.reference matchLen (pos - matchPos)))
            else
              have : data.size - (pos + matchLen) < data.size - pos := by omega
              let (hashTable, prev) :=
                updateHashesGuarded data hashSize hashTable prev pos 1 matchLen insertCap
              let h3tab := if useH3 then updateHash3 data h3tab pos 1 matchLen insertCap else h3tab
              lz77ChainLazyIter.mainLoop data windowSize hashSize maxChain insertCap goodMatch niceLen lazyDepth lazy2Steps useH3 hashTable prev h3tab (pos + matchLen)
                (acc.push (.reference matchLen (pos - matchPos)))
          else
            -- Gated: long first match, skip the lookahead; still insert interior hashes.
            have : data.size - (pos + matchLen) < data.size - pos := by omega
            let (hashTable, prev) :=
              updateHashesGuarded data hashSize hashTable prev pos 1 matchLen insertCap
            let h3tab := if useH3 then updateHash3 data h3tab pos 1 matchLen insertCap else h3tab
            lz77ChainLazyIter.mainLoop data windowSize hashSize maxChain insertCap goodMatch niceLen lazyDepth lazy2Steps useH3 hashTable prev h3tab (pos + matchLen)
              (acc.push (.reference matchLen (pos - matchPos)))
        else
          have : data.size - (pos + matchLen) < data.size - pos := by omega
          lz77ChainLazyIter.mainLoop data windowSize hashSize maxChain insertCap goodMatch niceLen lazyDepth lazy2Steps useH3 hashTable prev h3tab (pos + matchLen)
            (acc.push (.reference matchLen (pos - matchPos)))
      else
        lz77ChainLazyIter.mainLoop data windowSize hashSize maxChain insertCap goodMatch niceLen lazyDepth lazy2Steps useH3 hashTable prev h3tab (pos + 1)
          (acc.push (.literal (data[pos]'(by omega))))
    else
      lz77ChainLazyIter.mainLoop data windowSize hashSize maxChain insertCap goodMatch niceLen lazyDepth lazy2Steps useH3 hashTable prev h3tab (pos + 1)
        (acc.push (.literal (data[pos]'(by omega))))
  else
    lz77GreedyIter.trailing data pos acc
termination_by 2 * (data.size - pos)
decreasing_by all_goals (first | omega | (refine Nat.mul_lt_mul_of_pos_left ?_ (by decide); omega))

/-- Accumulator twin of `lz77ChainLazy.rollDefer`: identical rolling deferral, push
    vs. cons at each emission. Rung 5 of #2837: no proof-args cross the mutual
    boundary; termination is the interleaved `2*(data.size-mp)+1` measure and the
    bound is re-derived locally. Validity is re-established at emission
    (`LZ77ChainLazyCorrect`). -/
def lz77ChainLazyIter.rollDefer (data : ByteArray) (windowSize hashSize maxChain insertCap goodMatch niceLen lazyDepth lazy2Steps : Nat) (useH3 : Bool)
    (hashTable : Array Nat) (prev h3tab : Array Nat)
    (mp pLen pMatchPos step : Nat) (acc : Array LZ77Token) : Array LZ77Token :=
  if hcan : step < lazy2Steps ∧ mp + 3 < data.size ∧ pLen < goodMatch then
    let hmh := lz77Greedy.hash3 data mp hashSize (by omega)
    let headmp := headProbeGuarded hashTable hmh
    let hashTable := guardedSet hashTable hmh mp
    let prev := guardedSet prev (mp &&& 0x7FFF) headmp
    let h3tab := if useH3 then guardedSet h3tab (hash3Single data mp (by omega)) mp else h3tab
    let h2 := lz77Greedy.hash3 data (mp + 1) hashSize (by omega)
    let head2 := headProbeGuarded hashTable h2
    let maxLen2 := min 258 (data.size - (mp + 1))
    have hmaxLen2P : (mp + 1) + maxLen2 ≤ data.size := by omega
    let r2 := chainWalkGuardedPacked data prev windowSize (mp + 1) maxLen2 niceLen hmaxLen2P head2 (lazy2ProbeDepth maxChain) 0 0
    let len' := r2 % 512
    let pos' := r2 / 512
    if lazyAcceptCost pLen (mp - pMatchPos) len' (mp + 1 - pos') = true ∧ (mp + 1) + len' ≤ data.size then
      lz77ChainLazyIter.rollDefer data windowSize hashSize maxChain insertCap goodMatch niceLen lazyDepth lazy2Steps useH3
        hashTable prev h3tab (mp + 1) len' pos' (step + 1)
        (acc.push (.literal (data[mp]'(by omega))))
    else
      let (hashTable, prev) := updateHashesGuarded data hashSize hashTable prev mp 1 pLen insertCap
      let h3tab := if useH3 then updateHash3 data h3tab mp 1 pLen insertCap else h3tab
      lz77ChainLazyIter.mainLoop data windowSize hashSize maxChain insertCap goodMatch niceLen lazyDepth lazy2Steps useH3 hashTable prev h3tab (mp + pLen)
        (acc.push (.reference pLen (mp - pMatchPos)))
  else
    let (hashTable, prev) := updateHashesGuarded data hashSize hashTable prev (mp - 1) 1 (pLen + 1) insertCap
    let h3tab := if useH3 then updateHash3 data h3tab (mp - 1) 1 (pLen + 1) insertCap else h3tab
    lz77ChainLazyIter.mainLoop data windowSize hashSize maxChain insertCap goodMatch niceLen lazyDepth lazy2Steps useH3 hashTable prev h3tab (mp + pLen)
      (acc.push (.reference pLen (mp - pMatchPos)))
termination_by 2 * (data.size - mp) + 1
decreasing_by all_goals omega

end

/-- Iterative (tail-recursive, `Array`-accumulating) version of `lz77ChainLazy`.
    Same output, no stack overflow on large inputs. Reuses `lz77Chain`'s
    `chainWalk`/`updateHashes` and `lz77GreedyIter.trailing`; only the
    token-emitting `mainLoop` differs (push vs. cons). Threads the rolling-lazy2
    `lazy2Steps` knob (default `1`, the only value any call site passes). Proven
    equal to `lz77ChainLazy` in `LZ77ChainLazyCorrect`. -/
def lz77ChainLazyIter (data : ByteArray) (maxChain : Nat) (windowSize : Nat := 32768)
    (insertCap : Nat := 1000000000) (goodMatch : Nat := 259) (niceLen : Nat := 258)
    (lazyDepth : Nat := maxChain) (useH3 : Bool := false) (lazy2Steps : Nat := 1) :
    Array LZ77Token :=
  if data.size < 3 then
    lz77GreedyIter.trailing data 0 #[]
  else
    let hashSize := 65536
    lz77ChainLazyIter.mainLoop data windowSize hashSize maxChain insertCap goodMatch niceLen lazyDepth lazy2Steps useH3
      (.replicate hashSize data.size) (.replicate (min chainWinSize data.size) data.size)
      (.replicate 32768 data.size) 0 #[]

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

/-- `TokenArray` twin of `trailingP` (stage 2/7 of the token-stream unboxing):
    pushes `packTok (.literal _)` for each remaining byte into a `TokenArray`
    accumulator (4 B/token) instead of an `Array UInt32` (boxed 8 B/token). The
    boxed `trailingP` stays the lazy tier's trailing loop until stage 3; this twin
    serves the greedy matchers. Equal to `trailingP` under `.toArray`
    (`trailingPT_toArray` in `Zip/Spec/LZ77PackedCorrect.lean`). -/
def trailingPT (data : ByteArray) (pos : Nat) (acc : TokenArray) : TokenArray :=
  if h : pos < data.size then
    trailingPT data (pos + 1) (acc.push (packTok (.literal data[pos])))
  else acc
termination_by data.size - pos

/-- Packed-token twin of `lz77ChainIter` (greedy hash-chain matcher):
    identical control flow and chain state, `Array UInt32` accumulator.
    Equal to `(lz77ChainIter ..).map packTok` (`lz77ChainIterP_eq`). -/
def lz77ChainIterP (data : ByteArray) (maxChain : Nat) (windowSize : Nat := 32768)
    (insertCap : Nat := 1000000000) (niceLen : Nat := 258) :
    TokenArray :=
  if data.size < 3 then
    trailingPT data 0 TokenArray.empty
  else
    let hashSize := 65536
    mainLoop data windowSize hashSize maxChain insertCap niceLen
      (.replicate hashSize data.size) (.replicate (min chainWinSize data.size) data.size) 0
      TokenArray.empty
where
  mainLoop (data : ByteArray) (windowSize hashSize maxChain insertCap niceLen : Nat)
      (hashTable : Array Nat) (prev : Array Nat) (pos : Nat) (acc : TokenArray) :
      TokenArray :=
    if hlt : pos + 2 < data.size then
      let h := lz77Greedy.hash3 data pos hashSize hlt
      let head := headProbeGuarded hashTable h
      let hashTable := guardedSet hashTable h pos
      let prev := guardedSet prev (pos &&& 0x7FFF) head
      let maxLen := min 258 (data.size - pos)
      have hmaxLenP : pos + maxLen ≤ data.size := by omega
      let r := chainWalkGuardedPackedU data prev windowSize pos maxLen niceLen hmaxLenP head maxChain 0 0
      let matchLen := r % 512
      let matchPos := r / 512
      if hge : matchLen ≥ 3 then
        if hle : pos + matchLen ≤ data.size then
          have : data.size - (pos + matchLen) < data.size - pos := by omega
          let (hashTable, prev) :=
            updateHashesGuarded data hashSize hashTable prev pos 1 matchLen insertCap
          mainLoop data windowSize hashSize maxChain insertCap niceLen hashTable prev (pos + matchLen)
            (acc.push (packTok (.reference matchLen (pos - matchPos))))
        else
          mainLoop data windowSize hashSize maxChain insertCap niceLen hashTable prev (pos + 1)
            (acc.push (packTok (.literal (data[pos]'(by omega)))))
      else
        mainLoop data windowSize hashSize maxChain insertCap niceLen hashTable prev (pos + 1)
          (acc.push (packTok (.literal (data[pos]'(by omega)))))
    else
      trailingPT data pos acc
  termination_by data.size - pos
  decreasing_by all_goals omega

mutual

/-- Packed-token twin of `lz77ChainLazyIter.mainLoop` (rung 4 of #2837): threads
    the rolling-lazy2 `lazy2Steps` knob and forwards into the packed `rollDefer`
    twin exactly as the boxed-token iter loop forwards into its. Byte-for-byte the
    plain-iter loop with `packTok` pushes and the `USize` walk
    (`chainWalkGuardedPackedU`); `lazy2Steps = 1` never enters `rollDefer`, so
    production output is byte-identical. Proven equal to
    `(lz77ChainLazyIter.mainLoop ..).map packTok` in `LZ77PackedCorrect`. -/
def lz77ChainLazyIterP.mainLoop (data : ByteArray) (windowSize hashSize maxChain insertCap goodMatch niceLen lazyDepth lazy2Steps : Nat) (useH3 : Bool)
    (hashTable : Array Nat) (prev h3tab : Array Nat) (pos : Nat) (acc : Array UInt32) :
    Array UInt32 :=
  if hlt : pos + 2 < data.size then
    let h := lz77Greedy.hash3 data pos hashSize hlt
    let head := headProbeGuarded hashTable h
    let hashTable := guardedSet hashTable h pos
    let prev := guardedSet prev (pos &&& 0x7FFF) head
    let seed := h3Seed useH3 data h3tab windowSize pos hlt
    let h3tab := if useH3 then guardedSet h3tab (hash3Single data pos hlt) pos else h3tab
    let maxLen := min 258 (data.size - pos)
    have hmaxLenP : pos + maxLen ≤ data.size := by omega
    let r := chainWalkGuardedPackedU data prev windowSize pos maxLen niceLen hmaxLenP head maxChain (seed % 512) (seed / 512)
    let matchLen := r % 512
    let matchPos := r / 512
    if hge : matchLen ≥ 3 then
      if hle : pos + matchLen ≤ data.size then
        if h3lt : pos + 3 < data.size then
          -- Lazy gate (zlib `good_match`): only run the second `pos+1` chain walk
          -- when the first match is short (`matchLen < goodMatch`). `goodMatch = 259`
          -- (> max match 258) restores the ungated matcher exactly.
          if matchLen < goodMatch then
            let h2 := lz77Greedy.hash3 data (pos + 1) hashSize (by omega)
            let head2 := headProbeGuarded hashTable h2
            let maxLen2 := min 258 (data.size - (pos + 1))
            have hmaxLen2P : (pos + 1) + maxLen2 ≤ data.size := by omega
            let r2 :=
              chainWalkGuardedPackedU data prev windowSize (pos + 1) maxLen2 niceLen hmaxLen2P head2 lazyDepth 0 0
            let matchLen2 := r2 % 512
            let matchPos2 := r2 / 512
            if lazyAcceptCost matchLen (pos - matchPos) matchLen2 (pos + 1 - matchPos2) then
              if hle2 : pos + 1 + matchLen2 ≤ data.size then
                if h1 : 1 < lazy2Steps then
                  -- Rolling deferral: push the pending match-start byte as a
                  -- literal and roll into `rollDefer` at `pos+1`, step 1 (rung 5:
                  -- no proof-args cross the mutual boundary).
                  lz77ChainLazyIterP.rollDefer data windowSize hashSize maxChain insertCap goodMatch niceLen lazyDepth lazy2Steps useH3
                    hashTable prev h3tab (pos + 1) matchLen2 matchPos2 1
                    (acc.push (packTok (.literal (data[pos]'(by omega)))))
                else
                  -- Single deferral (`lazy2Steps ≤ 1`): the original lazy behavior.
                  have : data.size - (pos + 1 + matchLen2) < data.size - pos := by omega
                  let (hashTable, prev) :=
                    updateHashesGuarded data hashSize hashTable prev pos 1 (matchLen2 + 1) insertCap
                  let h3tab := if useH3 then updateHash3 data h3tab pos 1 (matchLen2 + 1) insertCap else h3tab
                  lz77ChainLazyIterP.mainLoop data windowSize hashSize maxChain insertCap goodMatch niceLen lazyDepth lazy2Steps useH3 hashTable prev h3tab (pos + 1 + matchLen2)
                    (acc.push (packTok (.literal (data[pos]'(by omega)))) |>.push
                      (packTok (.reference matchLen2 (pos + 1 - matchPos2))))
              else
                have : data.size - (pos + matchLen) < data.size - pos := by omega
                let (hashTable, prev) :=
                  updateHashesGuarded data hashSize hashTable prev pos 1 matchLen insertCap
                let h3tab := if useH3 then updateHash3 data h3tab pos 1 matchLen insertCap else h3tab
                lz77ChainLazyIterP.mainLoop data windowSize hashSize maxChain insertCap goodMatch niceLen lazyDepth lazy2Steps useH3 hashTable prev h3tab (pos + matchLen)
                  (acc.push (packTok (.reference matchLen (pos - matchPos))))
            else
              have : data.size - (pos + matchLen) < data.size - pos := by omega
              let (hashTable, prev) :=
                updateHashesGuarded data hashSize hashTable prev pos 1 matchLen insertCap
              let h3tab := if useH3 then updateHash3 data h3tab pos 1 matchLen insertCap else h3tab
              lz77ChainLazyIterP.mainLoop data windowSize hashSize maxChain insertCap goodMatch niceLen lazyDepth lazy2Steps useH3 hashTable prev h3tab (pos + matchLen)
                (acc.push (packTok (.reference matchLen (pos - matchPos))))
          else
            -- Gated: first match already long; skip the lookahead, but still insert
            -- interior hashes for the match (mid-buffer) then emit it.
            have : data.size - (pos + matchLen) < data.size - pos := by omega
            let (hashTable, prev) :=
              updateHashesGuarded data hashSize hashTable prev pos 1 matchLen insertCap
            let h3tab := if useH3 then updateHash3 data h3tab pos 1 matchLen insertCap else h3tab
            lz77ChainLazyIterP.mainLoop data windowSize hashSize maxChain insertCap goodMatch niceLen lazyDepth lazy2Steps useH3 hashTable prev h3tab (pos + matchLen)
              (acc.push (packTok (.reference matchLen (pos - matchPos))))
        else
          have : data.size - (pos + matchLen) < data.size - pos := by omega
          lz77ChainLazyIterP.mainLoop data windowSize hashSize maxChain insertCap goodMatch niceLen lazyDepth lazy2Steps useH3 hashTable prev h3tab (pos + matchLen)
            (acc.push (packTok (.reference matchLen (pos - matchPos))))
      else
        lz77ChainLazyIterP.mainLoop data windowSize hashSize maxChain insertCap goodMatch niceLen lazyDepth lazy2Steps useH3 hashTable prev h3tab (pos + 1)
          (acc.push (packTok (.literal (data[pos]'(by omega)))))
    else
      lz77ChainLazyIterP.mainLoop data windowSize hashSize maxChain insertCap goodMatch niceLen lazyDepth lazy2Steps useH3 hashTable prev h3tab (pos + 1)
        (acc.push (packTok (.literal (data[pos]'(by omega)))))
  else
    trailingP data pos acc
termination_by 2 * (data.size - pos)
decreasing_by all_goals (first | omega | (refine Nat.mul_lt_mul_of_pos_left ?_ (by decide); omega))

/-- Packed-token accumulator twin of `lz77ChainLazyIter.rollDefer`: identical
    rolling deferral, `packTok` pushes and the `USize` re-probe walk. The re-probe
    is unseeded `(0, 0)` exactly as the plain-iter twin (the merged loop length-
    seeds and bridges to this via `seeded_probe_bridge`). Rung 5 of #2837: no
    proof-args cross the mutual boundary; termination via the interleaved measure. -/
def lz77ChainLazyIterP.rollDefer (data : ByteArray) (windowSize hashSize maxChain insertCap goodMatch niceLen lazyDepth lazy2Steps : Nat) (useH3 : Bool)
    (hashTable : Array Nat) (prev h3tab : Array Nat)
    (mp pLen pMatchPos step : Nat) (acc : Array UInt32) : Array UInt32 :=
  if hcan : step < lazy2Steps ∧ mp + 3 < data.size ∧ pLen < goodMatch then
    let hmh := lz77Greedy.hash3 data mp hashSize (by omega)
    let headmp := headProbeGuarded hashTable hmh
    let hashTable := guardedSet hashTable hmh mp
    let prev := guardedSet prev (mp &&& 0x7FFF) headmp
    let h3tab := if useH3 then guardedSet h3tab (hash3Single data mp (by omega)) mp else h3tab
    let h2 := lz77Greedy.hash3 data (mp + 1) hashSize (by omega)
    let head2 := headProbeGuarded hashTable h2
    let maxLen2 := min 258 (data.size - (mp + 1))
    have hmaxLen2P : (mp + 1) + maxLen2 ≤ data.size := by omega
    let r2 := chainWalkGuardedPackedU data prev windowSize (mp + 1) maxLen2 niceLen hmaxLen2P head2 (lazy2ProbeDepth maxChain) 0 0
    let len' := r2 % 512
    let pos' := r2 / 512
    if lazyAcceptCost pLen (mp - pMatchPos) len' (mp + 1 - pos') = true ∧ (mp + 1) + len' ≤ data.size then
      lz77ChainLazyIterP.rollDefer data windowSize hashSize maxChain insertCap goodMatch niceLen lazyDepth lazy2Steps useH3
        hashTable prev h3tab (mp + 1) len' pos' (step + 1)
        (acc.push (packTok (.literal (data[mp]'(by omega)))))
    else
      let (hashTable, prev) := updateHashesGuarded data hashSize hashTable prev mp 1 pLen insertCap
      let h3tab := if useH3 then updateHash3 data h3tab mp 1 pLen insertCap else h3tab
      lz77ChainLazyIterP.mainLoop data windowSize hashSize maxChain insertCap goodMatch niceLen lazyDepth lazy2Steps useH3 hashTable prev h3tab (mp + pLen)
        (acc.push (packTok (.reference pLen (mp - pMatchPos))))
  else
    let (hashTable, prev) := updateHashesGuarded data hashSize hashTable prev (mp - 1) 1 (pLen + 1) insertCap
    let h3tab := if useH3 then updateHash3 data h3tab (mp - 1) 1 (pLen + 1) insertCap else h3tab
    lz77ChainLazyIterP.mainLoop data windowSize hashSize maxChain insertCap goodMatch niceLen lazyDepth lazy2Steps useH3 hashTable prev h3tab (mp + pLen)
      (acc.push (packTok (.reference pLen (mp - pMatchPos))))
termination_by 2 * (data.size - mp) + 1
decreasing_by all_goals omega

end

/-- Packed-token twin of `lz77ChainLazyIter` (lazy one-byte-lookahead matcher):
    identical control flow and chain state, `Array UInt32` accumulator. Threads
    the rolling-lazy2 `lazy2Steps` knob (default `1`, the only value any call site
    passes). Equal to `(lz77ChainLazyIter ..).map packTok` (`lz77ChainLazyIterP_eq`). -/
def lz77ChainLazyIterP (data : ByteArray) (maxChain : Nat) (windowSize : Nat := 32768)
    (insertCap : Nat := 1000000000) (goodMatch : Nat := 259) (niceLen : Nat := 258)
    (lazyDepth : Nat := maxChain) (useH3 : Bool := false) (lazy2Steps : Nat := 1) :
    Array UInt32 :=
  if data.size < 3 then
    trailingP data 0 #[]
  else
    let hashSize := 65536
    lz77ChainLazyIterP.mainLoop data windowSize hashSize maxChain insertCap goodMatch niceLen lazyDepth lazy2Steps useH3
      (.replicate hashSize data.size) (.replicate (min chainWinSize data.size) data.size)
      (.replicate 32768 data.size) 0
      (Array.emptyWithCapacity data.size)

/-! ## SPIKE (#2767 salvage): merged-array lazy matcher (single `Array Nat`)

The chain state is held in ONE `Array Nat` of size `prevSize + hashSize`, with
the `prev` ring at offset `[0, prevSize)` and the hash table at
`[prevSize, prevSize + hashSize)`. Because `prev` sits at offset 0, the
34%-hot chain walk (`chainWalkGuardedPackedU`) reads `c[cand &&& 0x7FFF]`
**unchanged** — the combined array is passed straight in where `prev` was. Only
the once-per-position hash-table accesses take a `+ prevSize` offset.

The payoff: the interior-hash walk (`updateHashesMerged`) threads and returns a
**single** array — no `(hashTable, prev)` Prod is ever allocated, unpacked, or
freed — while the main loop stays one self-tail-recursive function (a `goto`
loop: no stack growth, arrays stay linear ⇒ in-place `set`). Measurement scaffold
only: `partial` + sorried bounds (production indices are genuinely in range ⇒
byte-identical). -/
/-- Merged-array interior-hash insertion: the twin of `updateHashesGuarded`'s
    walk on the single combined array. Reads the bucket head at `prevSize + hsh`
    and writes both the hash bucket (`prevSize + hsh`) and the `prev` slot
    (`(pos+j) &&& 0x7FFF`, offset 0) into the same array `c`, so it threads and
    returns **one** `Array Nat` — no `(hashTable, prev)` pair. Uses the
    runtime-guarded `headProbeGuarded`/`guardedSet` (bounds dead in practice), so
    no bounds hypotheses thread through the loop. -/
def updateHashesMerged (data : ByteArray) (hashSize prevSize : Nat)
    (c : Array Nat) (pos j matchLen insertCap : Nat) : Array Nat :=
  if j < matchLen ∧ j ≤ insertCap then
    if h : pos + j + 2 < data.size then
      let hsh := lz77Greedy.hash3 data (pos + j) hashSize h
      let head := headProbeGuarded c (prevSize + hsh)
      updateHashesMerged data hashSize prevSize
        (guardedSet (guardedSet c (prevSize + hsh) (pos + j)) ((pos + j) &&& 0x7FFF) head)
        pos (j + 1) matchLen insertCap
    else
      updateHashesMerged data hashSize prevSize c pos (j + 1) matchLen insertCap
  else c
termination_by matchLen - j
decreasing_by all_goals omega

/-- Proven-bounds merged insertion: the two writes and the head read use
    `Array.set`/`getElem` with proofs (no runtime bounds branch), so the hot
    per-insertion loop pays nothing per step for the merge. The bucket index
    `prevSize + hsh < c.size` (`hb`) and the chain-mask `(pos+j) &&& 0x7FFF <
    c.size` (`hmask`) are discharged from the combined-array size hypothesis
    `hph : prevSize + hashSize ≤ c.size` and the window guard `hpv`. Proven equal
    to the `guardedSet` walk (`updateHashesMergedFast_eq`); the guards always hold
    for the production combined array, so this is the runtime path. -/
def updateHashesMergedFast (data : ByteArray) (hashSize prevSize : Nat)
    (c : Array Nat) (pos j matchLen insertCap : Nat)
    (hhs : 0 < hashSize) (hph : prevSize + hashSize ≤ c.size)
    (hpv : min chainWinSize data.size ≤ prevSize) : Array Nat :=
  if j < matchLen ∧ j ≤ insertCap then
    if h : pos + j + 2 < data.size then
      let hsh := lz77Greedy.hash3 data (pos + j) hashSize h
      have hb : prevSize + hsh < c.size := by
        have : hsh < hashSize := Nat.mod_lt _ hhs
        omega
      have hmask : ((pos + j) &&& 0x7FFF) < c.size := by
        have h1 := winMask_lt (pos + j)
        have h2 := Nat.and_le_left (n := pos + j) (m := 0x7FFF)
        simp only [chainWinSize] at h1 hpv; omega
      let head := c[prevSize + hsh]'hb
      updateHashesMergedFast data hashSize prevSize
        ((c.set (prevSize + hsh) (pos + j) hb).set ((pos + j) &&& 0x7FFF) head
          (by rw [Array.size_set]; exact hmask))
        pos (j + 1) matchLen insertCap hhs
        (by rw [Array.size_set, Array.size_set]; exact hph) hpv
    else
      updateHashesMergedFast data hashSize prevSize c pos (j + 1) matchLen insertCap hhs hph hpv
  else c
termination_by matchLen - j
decreasing_by all_goals omega

/-- `lz77Greedy.hash3` with the per-call `USize` bookkeeping hoisted: the caller
    supplies the already-converted `USize` position `pU` and the buffer
    addressability witness `hsz` once, so the hot insertion loop pays neither the
    `data.size.toUSize.toNat = data.size` round-trip check nor the `pos.toUSize`
    conversion per call, and the final bucket reduction runs as one unboxed
    `USize` mod instead of a boxed `Nat` mod. Same wide-load / 3-byte-tail
    fallback structure as `hash3`, so `hash3U_toNat` (in `LZ77MergedCorrect`)
    shows the value is exactly `hash3`'s whenever the buffer is
    `USize`-addressable. -/
@[inline] def hash3U (data : ByteArray) (p : Nat) (pU hashSizeU : USize)
    (hpU : pU.toNat = p) (h : p + 2 < data.size) : USize :=
  let word :=
    if h4 : p + 4 ≤ data.size then
      ByteArray.ugetUInt32LE data pU (by rw [hpU]; omega)
    else
      let a := (data[p]'(by omega)).toUInt32
      let b := (data[p + 1]'(by omega)).toUInt32
      let c := (data[p + 2]'(by omega)).toUInt32
      a ||| (b <<< 8) ||| (c <<< 16)
  ((word * 2654435761) >>> 16).toUSize % hashSizeU

/-- The `USize` bucket index is in range: `hash3U` ends in `% hashSizeU`, whose
    `toNat` is the `Nat` mod by `hashSize`. Discharges the write bounds inside
    `updateHashesMergedFastU`. -/
theorem hash3U_toNat_lt (data : ByteArray) (p hashSize : Nat) (pU hashSizeU : USize)
    (hpU : pU.toNat = p) (h : p + 2 < data.size)
    (hhsU : hashSizeU.toNat = hashSize) (hhs : 0 < hashSize) :
    (hash3U data p pU hashSizeU hpU h).toNat < hashSize := by
  unfold hash3U
  simp only [USize.toNat_mod, hhsU]
  exact Nat.mod_lt _ hhs

/-- `USize`-argument twin of `hash3Single` for the de-boxed insertion loop: the
    hoisted addressability witness (`hsz` at the wrapper) lets it skip
    `hash3Single`'s per-call `data.size.toUSize.toNat = data.size` check and take
    the wide load directly. Same word, same 24-bit mask, same 15-bit bucket
    (`hash3SingleU_toNat` in `LZ77MergedCorrect` shows the value is exactly
    `hash3Single`'s). The word computation is deliberately identical to
    `hash3U`'s load so the two per-insertion hashes share one wide load (CSE). -/
@[inline] def hash3SingleU (data : ByteArray) (p : Nat) (pU : USize)
    (hpU : pU.toNat = p) (h : p + 2 < data.size) : USize :=
  let word :=
    if h4 : p + 4 ≤ data.size then
      ByteArray.ugetUInt32LE data pU (by rw [hpU]; omega)
    else
      let a := (data[p]'(by omega)).toUInt32
      let b := (data[p + 1]'(by omega)).toUInt32
      let c := (data[p + 2]'(by omega)).toUInt32
      a ||| (b <<< 8) ||| (c <<< 16)
  ((((word &&& 0xFFFFFF) * 2654435761)) >>> 17).toUSize

/-- The `USize` singleton bucket is always in the 32768-entry table: a
    `UInt32 >>> 17` has 15 bits. Discharges the `h3tab` write bounds inside the
    fused insertion loop. -/
theorem hash3SingleU_toNat_lt (data : ByteArray) (p : Nat) (pU : USize)
    (hpU : pU.toNat = p) (h : p + 2 < data.size) :
    (hash3SingleU data p pU hpU h).toNat < 32768 := by
  unfold hash3SingleU
  generalize (if h4 : p + 4 ≤ data.size then _ else _ : UInt32) = word
  rw [UInt32.toNat_toUSize, UInt32.toNat_shiftRight,
    show ((17 : UInt32).toNat % 32) = 17 from rfl]
  have := UInt32.toNat_lt ((word &&& 0xFFFFFF) * 2654435761)
  omega

/-- USize-native de-boxed twin of `updateHashesMergedFast` (the interior-hash
    insertion loop, 13–25% of L4–L8 compress time): the per-insertion index
    bookkeeping — the loop counter `jU`, the data-bound test, the bucket index
    `prevSizeU + hshU`, and the chain mask `pjU &&& 0x7FFF` — runs on unboxed
    `USize` instead of tagged `Nat`, with the two hot writes and the head read as
    `Array.uset`/`Array.uget` (no per-step bounds branch, no `Nat` untag on the
    index). The data-bound test is one `USize` compare against the hoisted
    remaining-bytes bound `rem2U` (`= data.size - pos - 2`, computed once by the
    guarded wrapper), and the per-step hash goes through `hash3U`, which skips
    `hash3`'s per-call addressability round-trip. The stored position value stays
    `Nat` (the array is a `Nat` ring), produced by one `USize.toNat` per
    insertion. Proven equal to `updateHashesMerged`
    (`updateHashesMergedFastU_eq` in `LZ77MergedCorrect`). -/
def updateHashesMergedFastU (data : ByteArray) (hashSize prevSize pos : Nat)
    (c : Array Nat)
    (hhs : 0 < hashSize) (hph : prevSize + hashSize ≤ c.size)
    (hpv : min chainWinSize data.size ≤ prevSize)
    (hsz : data.size < USize.size) (hphlt : prevSize + hashSize < USize.size)
    (posU prevSizeU hashSizeU rem2U capU : USize)
    (hposU : posU.toNat = pos) (hpsU : prevSizeU.toNat = prevSize)
    (hhsU : hashSizeU.toNat = hashSize)
    (hrem2U : rem2U.toNat = data.size - pos - 2)
    (jU matchLenU : USize) : Array Nat :=
  if jU < matchLenU ∧ jU ≤ capU then
    if hd : jU < rem2U then
      have hUS : USize.size = 2 ^ System.Platform.numBits := rfl
      have hjlt : jU.toNat < data.size - pos - 2 := by
        rw [← hrem2U]; exact USize.lt_iff_toNat_lt.mp hd
      have hpjU : (posU + jU).toNat = pos + jU.toNat := by
        rw [USize.toNat_add, hposU]; exact Nat.mod_eq_of_lt (by omega)
      have hp2 : (posU + jU).toNat + 2 < data.size := by omega
      let hshU := hash3U data ((posU + jU).toNat) (posU + jU) hashSizeU rfl hp2
      have hshlt : hshU.toNat < hashSize :=
        hash3U_toNat_lt data ((posU + jU).toNat) hashSize (posU + jU) hashSizeU rfl hp2 hhsU hhs
      have hidx : (prevSizeU + hshU).toNat = prevSize + hshU.toNat := by
        rw [USize.toNat_add, hpsU]; exact Nat.mod_eq_of_lt (by omega)
      have hb : (prevSizeU + hshU).toNat < c.size := by rw [hidx]; omega
      let head := c.uget (prevSizeU + hshU) hb
      have hmaskb : ((posU + jU) &&& 0x7FFF).toNat < c.size := by
        rw [USize.toNat_and,
          USize.toNat_ofNat_of_lt (Nat.lt_of_lt_of_le (by decide) USize.le_size)]
        show ((posU + jU).toNat &&& 0x7FFF) < c.size
        have h1 := winMask_lt ((posU + jU).toNat)
        have h2 := Nat.and_le_left (n := (posU + jU).toNat) (m := 0x7FFF)
        simp only [chainWinSize] at h1 hpv
        omega
      updateHashesMergedFastU data hashSize prevSize pos
        ((c.uset (prevSizeU + hshU) ((posU + jU).toNat) hb).uset ((posU + jU) &&& 0x7FFF) head
          (by rw [Array.size_uset]; exact hmaskb))
        hhs (by rw [Array.size_uset, Array.size_uset]; exact hph) hpv hsz hphlt
        posU prevSizeU hashSizeU rem2U capU hposU hpsU hhsU hrem2U (jU + 1) matchLenU
    else
      updateHashesMergedFastU data hashSize prevSize pos c hhs hph hpv hsz hphlt
        posU prevSizeU hashSizeU rem2U capU hposU hpsU hhsU hrem2U (jU + 1) matchLenU
  else c
termination_by matchLenU.toNat - jU.toNat
decreasing_by
  all_goals
    have hUS : USize.size = 2 ^ System.Platform.numBits := rfl
    have hc : jU < matchLenU ∧ jU ≤ capU := by assumption
    have hlt : jU.toNat < matchLenU.toNat := USize.lt_iff_toNat_lt.mp hc.1
    have hml := USize.toNat_lt_two_pow_numBits matchLenU
    have hj1 : (jU + 1).toNat = jU.toNat + 1 := by
      rw [USize.toNat_add, USize.toNat_one]; exact Nat.mod_eq_of_lt (by omega)
    omega

/-- Fused split-tier insertion walk: `updateHashesMergedFastU` with the
    hash3-singleton store folded into the same traversal. Each step does the two
    hash4 writes on the combined array `c` *and* one `h3tab.uset` at the
    `hash3SingleU` bucket — one loop, one data-bound test, one shared wide load
    (`hash3U`/`hash3SingleU` read the same word; CSE folds them), instead of the
    second `updateHash3` traversal with its per-step `guardedSet` bounds checks.
    The pair is only constructed at the base case (the recursion is a tail
    call), so no Prod churns per step. Byte-identical state: `.1` is exactly
    `updateHashesMerged` and `.2` exactly `updateHash3`
    (`updateHashesMergedH3FastU_eq` in `LZ77MergedCorrect`). -/
def updateHashesMergedH3FastU (data : ByteArray) (hashSize prevSize pos : Nat)
    (c h3tab : Array Nat)
    (hhs : 0 < hashSize) (hph : prevSize + hashSize ≤ c.size)
    (hpv : min chainWinSize data.size ≤ prevSize) (hh3 : 32768 ≤ h3tab.size)
    (hsz : data.size < USize.size) (hphlt : prevSize + hashSize < USize.size)
    (posU prevSizeU hashSizeU rem2U capU : USize)
    (hposU : posU.toNat = pos) (hpsU : prevSizeU.toNat = prevSize)
    (hhsU : hashSizeU.toNat = hashSize)
    (hrem2U : rem2U.toNat = data.size - pos - 2)
    (jU matchLenU : USize) : Array Nat × Array Nat :=
  if jU < matchLenU ∧ jU ≤ capU then
    if hd : jU < rem2U then
      have hUS : USize.size = 2 ^ System.Platform.numBits := rfl
      have hjlt : jU.toNat < data.size - pos - 2 := by
        rw [← hrem2U]; exact USize.lt_iff_toNat_lt.mp hd
      have hpjU : (posU + jU).toNat = pos + jU.toNat := by
        rw [USize.toNat_add, hposU]; exact Nat.mod_eq_of_lt (by omega)
      have hp2 : (posU + jU).toNat + 2 < data.size := by omega
      let hshU := hash3U data ((posU + jU).toNat) (posU + jU) hashSizeU rfl hp2
      have hshlt : hshU.toNat < hashSize :=
        hash3U_toNat_lt data ((posU + jU).toNat) hashSize (posU + jU) hashSizeU rfl hp2 hhsU hhs
      have hidx : (prevSizeU + hshU).toNat = prevSize + hshU.toNat := by
        rw [USize.toNat_add, hpsU]; exact Nat.mod_eq_of_lt (by omega)
      have hb : (prevSizeU + hshU).toNat < c.size := by rw [hidx]; omega
      let head := c.uget (prevSizeU + hshU) hb
      have hmaskb : ((posU + jU) &&& 0x7FFF).toNat < c.size := by
        rw [USize.toNat_and,
          USize.toNat_ofNat_of_lt (Nat.lt_of_lt_of_le (by decide) USize.le_size)]
        show ((posU + jU).toNat &&& 0x7FFF) < c.size
        have h1 := winMask_lt ((posU + jU).toNat)
        have h2 := Nat.and_le_left (n := (posU + jU).toNat) (m := 0x7FFF)
        simp only [chainWinSize] at h1 hpv
        omega
      let h3U := hash3SingleU data ((posU + jU).toNat) (posU + jU) rfl hp2
      have hh3b : h3U.toNat < h3tab.size :=
        Nat.lt_of_lt_of_le (hash3SingleU_toNat_lt data ((posU + jU).toNat) (posU + jU) rfl hp2) hh3
      updateHashesMergedH3FastU data hashSize prevSize pos
        ((c.uset (prevSizeU + hshU) ((posU + jU).toNat) hb).uset ((posU + jU) &&& 0x7FFF) head
          (by rw [Array.size_uset]; exact hmaskb))
        (h3tab.uset h3U ((posU + jU).toNat) hh3b)
        hhs (by rw [Array.size_uset, Array.size_uset]; exact hph) hpv
        (by rw [Array.size_uset]; exact hh3) hsz hphlt
        posU prevSizeU hashSizeU rem2U capU hposU hpsU hhsU hrem2U (jU + 1) matchLenU
    else
      updateHashesMergedH3FastU data hashSize prevSize pos c h3tab hhs hph hpv hh3 hsz hphlt
        posU prevSizeU hashSizeU rem2U capU hposU hpsU hhsU hrem2U (jU + 1) matchLenU
  else (c, h3tab)
termination_by matchLenU.toNat - jU.toNat
decreasing_by
  all_goals
    have hUS : USize.size = 2 ^ System.Platform.numBits := rfl
    have hc : jU < matchLenU ∧ jU ≤ capU := by assumption
    have hlt : jU.toNat < matchLenU.toNat := USize.lt_iff_toNat_lt.mp hc.1
    have hml := USize.toNat_lt_two_pow_numBits matchLenU
    have hj1 : (jU + 1).toNat = jU.toNat + 1 := by
      rw [USize.toNat_add, USize.toNat_one]; exact Nat.mod_eq_of_lt (by omega)
    omega

/-- One runtime `0 < hashSize ∧ prevSize + hashSize ≤ c.size ∧ min chainWinSize
    data.size ≤ prevSize` check guards the whole merged insertion loop, unlocking
    the proven-bounds walk; a second `USize`-faithfulness check (one
    `data.size.toUSize.toNat = data.size` round-trip witnessing addressability,
    plus round-trips for the small loop arguments — never failing in production:
    `data.size` fits a `size_t`, `matchLen ≤ 259`, `insertCap` is the fixed knob)
    then unlocks the de-boxed `USize` walk (`updateHashesMergedFastU`). The
    fallbacks are the proven-bounds `Nat` walk (`updateHashesMergedFast`) and the
    runtime-guarded `updateHashesMerged` (both dead in practice — the production
    combined array is a fixed `prevSize + hashSize`-entry `replicate`). Proven
    equal to `updateHashesMerged` (`updateHashesMergedGuarded_eq`). -/
@[inline] def updateHashesMergedGuarded (data : ByteArray) (hashSize prevSize : Nat)
    (c : Array Nat) (pos j matchLen insertCap : Nat) : Array Nat :=
  if hg : 0 < hashSize ∧ prevSize + hashSize ≤ c.size ∧ min chainWinSize data.size ≤ prevSize then
    if hu : data.size.toUSize.toNat = data.size ∧
        (prevSize + hashSize).toUSize.toNat = prevSize + hashSize ∧
        pos.toUSize.toNat = pos ∧ j.toUSize.toNat = j ∧
        matchLen.toUSize.toNat = matchLen ∧ insertCap.toUSize.toNat = insertCap then
      have hsz : data.size < USize.size := by
        rw [← hu.1]; exact USize.toNat_lt_two_pow_numBits _
      have hphlt : prevSize + hashSize < USize.size := by
        rw [← hu.2.1]; exact USize.toNat_lt_two_pow_numBits _
      updateHashesMergedFastU data hashSize prevSize pos c hg.1 hg.2.1 hg.2.2 hsz hphlt
        pos.toUSize prevSize.toUSize hashSize.toUSize (data.size - pos - 2).toUSize
        insertCap.toUSize hu.2.2.1 (toUSize_toNat_of_lt (by omega))
        (toUSize_toNat_of_lt (by omega)) (toUSize_toNat_of_lt (by omega))
        j.toUSize matchLen.toUSize
    else
      updateHashesMergedFast data hashSize prevSize c pos j matchLen insertCap hg.1 hg.2.1 hg.2.2
  else
    updateHashesMerged data hashSize prevSize c pos j matchLen insertCap

/-- Split-tier interior insertion: one call updates both the combined chain
    array and (when `useH3`) the hash3-singleton table, through the fused
    single-traversal `updateHashesMergedH3FastU` — the production path pays one
    walk over the interior range instead of two. With `useH3 := false` this is
    exactly `(updateHashesMergedGuarded …, h3tab)` (the singleton is untouched,
    no extra work). The `.1`/`.2` are byte-for-byte `updateHashesMerged` and the
    `useH3`-gated `updateHash3` (`updateHashesMergedH3Guarded_eq` in
    `LZ77MergedCorrect`), so the fusion cannot change the emitted stream. -/
@[inline] def updateHashesMergedH3Guarded (useH3 : Bool) (data : ByteArray)
    (hashSize prevSize : Nat) (c h3tab : Array Nat) (pos j matchLen insertCap : Nat) :
    Array Nat × Array Nat :=
  if useH3 then
    if hg : 0 < hashSize ∧ prevSize + hashSize ≤ c.size ∧
        min chainWinSize data.size ≤ prevSize ∧ 32768 ≤ h3tab.size then
      if hu : data.size.toUSize.toNat = data.size ∧
          (prevSize + hashSize).toUSize.toNat = prevSize + hashSize ∧
          pos.toUSize.toNat = pos ∧ j.toUSize.toNat = j ∧
          matchLen.toUSize.toNat = matchLen ∧ insertCap.toUSize.toNat = insertCap then
        have hsz : data.size < USize.size := by
          rw [← hu.1]; exact USize.toNat_lt_two_pow_numBits _
        have hphlt : prevSize + hashSize < USize.size := by
          rw [← hu.2.1]; exact USize.toNat_lt_two_pow_numBits _
        updateHashesMergedH3FastU data hashSize prevSize pos c h3tab hg.1 hg.2.1 hg.2.2.1
          hg.2.2.2 hsz hphlt
          pos.toUSize prevSize.toUSize hashSize.toUSize (data.size - pos - 2).toUSize
          insertCap.toUSize hu.2.2.1 (toUSize_toNat_of_lt (by omega))
          (toUSize_toNat_of_lt (by omega)) (toUSize_toNat_of_lt (by omega))
          j.toUSize matchLen.toUSize
      else
        (updateHashesMergedFast data hashSize prevSize c pos j matchLen insertCap hg.1 hg.2.1 hg.2.2.1,
         updateHash3 data h3tab pos j matchLen insertCap)
    else
      (updateHashesMerged data hashSize prevSize c pos j matchLen insertCap,
       updateHash3 data h3tab pos j matchLen insertCap)
  else
    (updateHashesMergedGuarded data hashSize prevSize c pos j matchLen insertCap, h3tab)

/-- Merged-array twin of `lz77ChainLazyIterP` with the mainLoop **and** the
    rolling deferral fused into one hot loop (#2837): identical control flow, but
    the chain state is the single combined array `c` (prev ring at offset 0, hash
    table at offset `prevSize`). The rolling-lazy2 deferral is carried in flat
    `Nat` state args `pLen pMatchPos step` — `pLen = 0` is the "no pending roll"
    sentinel (the fresh-position mainLoop mode, full chain walk at `pos`); `pLen >
    0` is the rolling mode formerly in `rollDefer` (the pending match `(pLen,
    pMatchPos)` was found by the previous step's lookahead, so this position does
    no fresh walk, only the seeded re-probe at `pos+1`). An accepted lazy deferral
    therefore rolls by **self-recursion** in the same function instead of a mutual
    outcall, so the compiler keeps a single loop on the hot accept path (the
    structural win of #2837). The per-position insertion goes through
    `updateHashesMerged*` (one array in, one out, no Prod). The rolling re-probe is
    **length-seeded** (`seed := if pLen < cutoff2 then pLen else 0`) exactly as the
    main-loop lookahead and the certified spike; the packed twin re-probes
    unseeded, so `mergedLoop_eq` bridges the two with `seeded_probe_bridge`. Threads
    `lazy2Steps` (rung 4/5 of #2837); `lazy2Steps = 1` never enters the rolling
    mode, so production output at other levels is byte-identical. The `maxLen`
    lookahead bounds are inlined (not `let`-bound) and each recursive call carries
    an inline measure witness so the well-founded termination goal — which fully
    expands the shadowed `c`/probe `let`s — closes by `assumption` against the
    (definitionally equal) witness. The interleaved measure is `2·(size−pos) +
    min pLen 1` (`min pLen 1` is the `mainLoop`-vs-`rollDefer` `+1` offset that was
    the mutual pair's two termination measures). Proven equal to the packed
    `lz77ChainLazyIterP.{mainLoop,rollDefer}` twins (`mergedLoop_eq` in
    `LZ77MergedCorrect`). -/
def lz77LazyMergedLoop (data : ByteArray)
    (windowSize hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth lazy2Steps : Nat) (useH3 : Bool)
    (c h3tab : Array Nat) (pos pLen pMatchPos step : Nat) (acc : Array UInt32) : Array UInt32 :=
  if hpz : pLen = 0 then
    -- Fresh-position mode (formerly `mainLoop`): full chain walk at `pos`.
    if hlt : pos + 2 < data.size then
      let h := lz77Greedy.hash3 data pos hashSize hlt
      let head := headProbeGuarded c (prevSize + h)
      let c := guardedSet c (prevSize + h) pos
      let c := guardedSet c (pos &&& 0x7FFF) head
      let seed := h3Seed useH3 data h3tab windowSize pos hlt
      let h3tab := if useH3 then guardedSet h3tab (hash3Single data pos hlt) pos else h3tab
      have hmaxLenP : pos + min 258 (data.size - pos) ≤ data.size := by omega
      let r := chainWalkGuardedPackedU data c windowSize pos (min 258 (data.size - pos)) niceLen hmaxLenP head maxChain (seed % 512) (seed / 512)
      let matchLen := r % 512
      let matchPos := r / 512
      if hge : matchLen ≥ 3 then
        if hle : pos + matchLen ≤ data.size then
          if h3lt : pos + 3 < data.size then
            if matchLen < goodMatch then
              let h2 := lz77Greedy.hash3 data (pos + 1) hashSize (by omega)
              let head2 := headProbeGuarded c (prevSize + h2)
              have hmaxLen2P : (pos + 1) + min 258 (data.size - (pos + 1)) ≤ data.size := by omega
              let cutoff2 := min niceLen (min 258 (data.size - (pos + 1)))
              let seed := if matchLen < cutoff2 then matchLen else 0
              let r2 :=
                chainWalkGuardedPackedU data c windowSize (pos + 1) (min 258 (data.size - (pos + 1))) niceLen hmaxLen2P head2 lazyDepth seed 0
              let matchLen2 := r2 % 512
              let matchPos2 := r2 / 512
              if lazyAcceptCost matchLen (pos - matchPos) matchLen2 (pos + 1 - matchPos2) then
                if hle2 : pos + 1 + matchLen2 ≤ data.size then
                  if h1 : 1 < lazy2Steps then
                    -- Rolling deferral: push the pending match-start byte as a
                    -- literal and roll into the rolling mode at `pos+1`, step 1, by
                    -- self-recursion (`pLen := matchLen2 > 0` — no mutual outcall).
                    have : 2 * (data.size - (pos + 1)) + min matchLen2 1 < 2 * (data.size - pos) + min pLen 1 := by omega
                    lz77LazyMergedLoop data windowSize hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth lazy2Steps useH3
                      c h3tab (pos + 1) matchLen2 matchPos2 1
                      (acc.push (packTok (.literal (data[pos]'(by omega)))))
                  else
                    -- Single deferral (`lazy2Steps ≤ 1`): the original lazy behavior.
                    have : 2 * (data.size - (pos + 1 + matchLen2)) + min (0:Nat) 1 < 2 * (data.size - pos) + min pLen 1 := by omega
                    let (c, h3tab) := updateHashesMergedH3Guarded useH3 data hashSize prevSize c h3tab pos 1 (matchLen2 + 1) insertCap
                    lz77LazyMergedLoop data windowSize hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth lazy2Steps useH3 c h3tab (pos + 1 + matchLen2) 0 0 0
                      (acc.push (packTok (.literal (data[pos]'(by omega)))) |>.push
                        (packTok (.reference matchLen2 (pos + 1 - matchPos2))))
                else
                  have : 2 * (data.size - (pos + matchLen)) + min (0:Nat) 1 < 2 * (data.size - pos) + min pLen 1 := by omega
                  let (c, h3tab) := updateHashesMergedH3Guarded useH3 data hashSize prevSize c h3tab pos 1 matchLen insertCap
                  lz77LazyMergedLoop data windowSize hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth lazy2Steps useH3 c h3tab (pos + matchLen) 0 0 0
                    (acc.push (packTok (.reference matchLen (pos - matchPos))))
              else
                have : 2 * (data.size - (pos + matchLen)) + min (0:Nat) 1 < 2 * (data.size - pos) + min pLen 1 := by omega
                let (c, h3tab) := updateHashesMergedH3Guarded useH3 data hashSize prevSize c h3tab pos 1 matchLen insertCap
                lz77LazyMergedLoop data windowSize hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth lazy2Steps useH3 c h3tab (pos + matchLen) 0 0 0
                  (acc.push (packTok (.reference matchLen (pos - matchPos))))
            else
              have : 2 * (data.size - (pos + matchLen)) + min (0:Nat) 1 < 2 * (data.size - pos) + min pLen 1 := by omega
              let (c, h3tab) := updateHashesMergedH3Guarded useH3 data hashSize prevSize c h3tab pos 1 matchLen insertCap
              lz77LazyMergedLoop data windowSize hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth lazy2Steps useH3 c h3tab (pos + matchLen) 0 0 0
                (acc.push (packTok (.reference matchLen (pos - matchPos))))
          else
            have : 2 * (data.size - (pos + matchLen)) + min (0:Nat) 1 < 2 * (data.size - pos) + min pLen 1 := by omega
            lz77LazyMergedLoop data windowSize hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth lazy2Steps useH3 c h3tab (pos + matchLen) 0 0 0
              (acc.push (packTok (.reference matchLen (pos - matchPos))))
        else
          have : 2 * (data.size - (pos + 1)) + min (0:Nat) 1 < 2 * (data.size - pos) + min pLen 1 := by omega
          lz77LazyMergedLoop data windowSize hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth lazy2Steps useH3 c h3tab (pos + 1) 0 0 0
            (acc.push (packTok (.literal (data[pos]'(by omega)))))
      else
        have : 2 * (data.size - (pos + 1)) + min (0:Nat) 1 < 2 * (data.size - pos) + min pLen 1 := by omega
        lz77LazyMergedLoop data windowSize hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth lazy2Steps useH3 c h3tab (pos + 1) 0 0 0
          (acc.push (packTok (.literal (data[pos]'(by omega)))))
    else
      trailingP data pos acc
  else
    -- Rolling mode (formerly `rollDefer`): a `pLen > 0` pending match starts at
    -- `pos` (`pos` plays the role of the old `rollDefer` `mp`). No fresh chain walk;
    -- only the seeded re-probe at `pos+1`.
    if hcan : step < lazy2Steps ∧ pos + 3 < data.size ∧ pLen < goodMatch then
      let hmh := lz77Greedy.hash3 data pos hashSize (by omega)
      let headmp := headProbeGuarded c (prevSize + hmh)
      let c := guardedSet c (prevSize + hmh) pos
      let c := guardedSet c (pos &&& 0x7FFF) headmp
      let h3tab := if useH3 then guardedSet h3tab (hash3Single data pos (by omega)) pos else h3tab
      let h2 := lz77Greedy.hash3 data (pos + 1) hashSize (by omega)
      let head2 := headProbeGuarded c (prevSize + h2)
      have hmaxLen2P : (pos + 1) + min 258 (data.size - (pos + 1)) ≤ data.size := by omega
      -- Length-seed the re-probe with the pending length (zlib `deflate_slow`'s
      -- `prev_length` trick, exactly as the certified spike): a candidate shorter
      -- than the pending match cannot improve on it, so pre-loading `pLen` as the
      -- probe's best length lets `scan_end` reject those candidates at one
      -- byte-compare instead of a full `countMatch`. The seed only changes a
      -- *rejected* result (acceptance needs `len' > pLen` strictly), so it is
      -- output-neutral; `mergedLoop_eq` bridges it to the unseeded packed twin via
      -- `seeded_probe_bridge` (as the main lookahead already does).
      let cutoff2 := min niceLen (min 258 (data.size - (pos + 1)))
      let seed := if pLen < cutoff2 then pLen else 0
      let r2 := chainWalkGuardedPackedU data c windowSize (pos + 1) (min 258 (data.size - (pos + 1))) niceLen hmaxLen2P head2 (lazy2ProbeDepth maxChain) seed 0
      let len' := r2 % 512
      let pos' := r2 / 512
      if lazyAcceptCost pLen (pos - pMatchPos) len' (pos + 1 - pos') = true ∧ (pos + 1) + len' ≤ data.size then
        have : 2 * (data.size - (pos + 1)) + min len' 1 < 2 * (data.size - pos) + min pLen 1 := by omega
        lz77LazyMergedLoop data windowSize hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth lazy2Steps useH3
          c h3tab (pos + 1) len' pos' (step + 1)
          (acc.push (packTok (.literal (data[pos]'(by omega)))))
      else
        have : 2 * (data.size - (pos + pLen)) + min (0:Nat) 1 < 2 * (data.size - pos) + min pLen 1 := by omega
        let (c, h3tab) := updateHashesMergedH3Guarded useH3 data hashSize prevSize c h3tab pos 1 pLen insertCap
        lz77LazyMergedLoop data windowSize hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth lazy2Steps useH3 c h3tab (pos + pLen) 0 0 0
          (acc.push (packTok (.reference pLen (pos - pMatchPos))))
    else
      have : 2 * (data.size - (pos + pLen)) + min (0:Nat) 1 < 2 * (data.size - pos) + min pLen 1 := by omega
      let (c, h3tab) := updateHashesMergedH3Guarded useH3 data hashSize prevSize c h3tab (pos - 1) 1 (pLen + 1) insertCap
      lz77LazyMergedLoop data windowSize hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth lazy2Steps useH3 c h3tab (pos + pLen) 0 0 0
        (acc.push (packTok (.reference pLen (pos - pMatchPos))))
termination_by 2 * (data.size - pos) + min pLen 1
decreasing_by all_goals (first | assumption | omega)

/-- Merged-array entry mirroring `lz77ChainLazyIterP`: builds the combined
    `prevSize + hashSize` array and runs `lz77LazyMergedLoop`. Threads the
    rolling-lazy2 `lazy2Steps` knob (default `1`). Proven equal to
    `lz77ChainLazyIterP` (`lz77ChainLazyIterPMerged_eq`). -/
def lz77ChainLazyIterPMerged (data : ByteArray) (maxChain : Nat) (windowSize : Nat := 32768)
    (insertCap : Nat := 1000000000) (goodMatch : Nat := 259) (niceLen : Nat := 258)
    (lazyDepth : Nat := maxChain) (useH3 : Bool := false) (lazy2Steps : Nat := 1) :
    Array UInt32 :=
  if data.size < 3 then
    trailingP data 0 #[]
  else
    let hashSize := 65536
    let prevSize := min chainWinSize data.size
    lz77LazyMergedLoop data windowSize hashSize prevSize maxChain insertCap goodMatch niceLen lazyDepth lazy2Steps useH3
      (.replicate (prevSize + hashSize) data.size) (.replicate 32768 data.size) 0 0 0 0
      (Array.emptyWithCapacity data.size)

/-- Merged-array twin of `lz77ChainIterP.mainLoop` (the greedy tier, levels
    1–3): identical control flow, but the chain state is the single combined
    array `c` (prev ring at offset 0, hash table at offset `prevSize`), exactly
    the layout `lz77LazyMergedLoop` uses on the lazy tier. The chain walk reads
    the prev ring unchanged (`cand &&& 0x7FFF < prevSize`), so the combined
    array is passed straight in where `prev` was; only the once-per-position
    hash-table head read/insert takes a `+ prevSize` offset. The per-match
    interior insertion goes through `updateHashesMergedGuarded` (one array in,
    one array out, de-boxed `USize` walk inside), so no `(hashTable, prev)`
    Prod is ever allocated, unpacked, or freed. Proven equal to
    `lz77ChainIterP.mainLoop` (`greedyMergedLoop_eq` in
    `Zip/Spec/LZ77MergedCorrect.lean`). -/
def lz77GreedyMergedLoop (data : ByteArray)
    (windowSize hashSize prevSize maxChain insertCap niceLen : Nat)
    (c : Array Nat) (pos : Nat) (acc : TokenArray) : TokenArray :=
  if hlt : pos + 2 < data.size then
    let h := lz77Greedy.hash3 data pos hashSize hlt
    let head := headProbeGuarded c (prevSize + h)
    let c := guardedSet c (prevSize + h) pos
    let c := guardedSet c (pos &&& 0x7FFF) head
    let maxLen := min 258 (data.size - pos)
    have hmaxLenP : pos + maxLen ≤ data.size := by omega
    let r := chainWalkGuardedPackedU data c windowSize pos maxLen niceLen hmaxLenP head maxChain 0 0
    let matchLen := r % 512
    let matchPos := r / 512
    if hge : matchLen ≥ 3 then
      if hle : pos + matchLen ≤ data.size then
        have : data.size - (pos + matchLen) < data.size - pos := by omega
        let c := updateHashesMergedGuarded data hashSize prevSize c pos 1 matchLen insertCap
        lz77GreedyMergedLoop data windowSize hashSize prevSize maxChain insertCap niceLen c (pos + matchLen)
          (acc.push (packTok (.reference matchLen (pos - matchPos))))
      else
        lz77GreedyMergedLoop data windowSize hashSize prevSize maxChain insertCap niceLen c (pos + 1)
          (acc.push (packTok (.literal (data[pos]'(by omega)))))
    else
      lz77GreedyMergedLoop data windowSize hashSize prevSize maxChain insertCap niceLen c (pos + 1)
        (acc.push (packTok (.literal (data[pos]'(by omega)))))
  else
    trailingPT data pos acc
termination_by data.size - pos
decreasing_by all_goals omega

/-- Merged-array entry mirroring `lz77ChainIterP`: builds the combined
    `prevSize + hashSize` array and runs `lz77GreedyMergedLoop`. Proven equal
    to `lz77ChainIterP` (`lz77ChainIterPMerged_eq`). -/
def lz77ChainIterPMerged (data : ByteArray) (maxChain : Nat) (windowSize : Nat := 32768)
    (insertCap : Nat := 1000000000) (niceLen : Nat := 258) :
    TokenArray :=
  if data.size < 3 then
    trailingPT data 0 TokenArray.empty
  else
    let hashSize := 65536
    let prevSize := min chainWinSize data.size
    lz77GreedyMergedLoop data windowSize hashSize prevSize maxChain insertCap niceLen
      (.replicate (prevSize + hashSize) data.size) 0
      TokenArray.empty

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
def deflateFixedBlockP (data : ByteArray) (tokens : Array UInt32) (cap : Nat := 0) : ByteArray :=
  let bw := BitWriter.emptyWithCapacity cap
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
