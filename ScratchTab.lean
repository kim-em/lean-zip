import Zip.Native.BitWriter
import Zip.Native.Inflate
import Std.Tactic.BVDecide

namespace Scratch
open Zip.Native

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

/-! ## Dense length/distance code tables (Wave 5.0)

`findLengthCode`/`findDistCode` are linear searches through the RFC 1951
base tables, run once or twice per reference token by the frequency pass
and both packed emitters — measured at ~14% of level-1 attributable
samples (track-d W5.P1). `lenCodeTab`/`distCodeTab` precompute every
answer into dense tables indexed by the value itself (length 0–258,
distance 0–32768), packing the `(idx, extraBits, extraVal)` triple into
one `UInt32` (`packCode`: idx bits 0–7, extraBits bits 8–15, extraVal
bits 16–31 — the widest field is the distance extraVal ≤ 32768 < 2^16…
in fact < 2^14, but 16 bits are free). `findLengthCodeFast`/
`findDistCodeFast` read the table for in-range values and fall back to
the linear search out of range, and are proven **equal** to the linear
searches (`findLengthCodeFast_eq`/`findDistCodeFast_eq`), so the hot
consumers (`bumpRef*FreqP`, `emitRefFixedP`, `emitRefWithCodesP`) swap
them in with no statement changes anywhere; the boxed reference paths
stay on the linear search (they are the spec subjects). The tables are
built *by* the linear search at module initialization (259 + 32769
probes, one-time), which keeps the equality proofs small: the only
content fact needed is `getElem`-of-`map`-of-`range`, never an
evaluation of the table. Caution (WF landmine, see
`Zip/Native/DeflateFreqs.lean`): never let `whnf`/`decide` evaluate the
table terms — the builder applies `findLengthCode` (a `WellFounded` fix)
259/32769 times. -/

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
private theorem findTableCode_go_fields {baseTable : Array UInt16} {extraTable : Array UInt8}
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
private theorem findLengthCode_isSome (len : Nat) : (findLengthCode len).isSome :=
  findTableCode_go_isSome (by rw [Inflate.lengthBase_size]; omega)

/-- `findDistCode` always succeeds. -/
private theorem findDistCode_isSome (dist : Nat) : (findDistCode dist).isSome :=
  findTableCode_go_isSome (by rw [Inflate.distBase_size]; omega)

/-- Pack a `(idx, extraBits, extraVal)` code triple into one `UInt32`:
    idx bits 0–7, extraBits bits 8–15, extraVal bits 16–31. -/
@[inline] private def packCode (idx extraN : Nat) (extraV : UInt32) : UInt32 :=
  idx.toUInt32 ||| (extraN.toUInt32 <<< 8) ||| (extraV <<< 16)

/-- Field extraction inverts `packCode` when the fields are in range. -/
private theorem packCode_fields {idx extraN : Nat} {extraV : UInt32}
    (hidx : idx < 256) (hen : extraN < 256) (hev : extraV < 65536) :
    (packCode idx extraN extraV &&& 0xFF).toNat = idx ∧
    ((packCode idx extraN extraV >>> 8) &&& 0xFF).toNat = extraN ∧
    packCode idx extraN extraV >>> 16 = extraV := by
  have hi : idx.toUInt32.toNat = idx := by
    simp only [Nat.toUInt32, UInt32.toNat_ofNat']
    omega
  have he : extraN.toUInt32.toNat = extraN := by
    simp only [Nat.toUInt32, UInt32.toNat_ofNat']
    omega
  have hiu : idx.toUInt32 < 256 := by
    change idx.toUInt32.toNat < (256 : UInt32).toNat
    rw [hi]; exact hidx
  have heu : extraN.toUInt32 < 256 := by
    change extraN.toUInt32.toNat < (256 : UInt32).toNat
    rw [he]; exact hen
  unfold packCode
  refine ⟨?_, ?_, ?_⟩
  · rw [show (idx.toUInt32 ||| (extraN.toUInt32 <<< 8) ||| (extraV <<< 16)) &&& 0xFF
        = idx.toUInt32 by bv_decide]
    exact hi
  · rw [show ((idx.toUInt32 ||| (extraN.toUInt32 <<< 8) ||| (extraV <<< 16)) >>> 8) &&& 0xFF
        = extraN.toUInt32 by bv_decide]
    exact he
  · bv_decide

/-- Dense length-code table: entry `len` (0–258) packs `findLengthCode len`.
    Built by the linear search itself, so `lenCodeTab_getElem` is by
    construction. -/
def lenCodeTab : Array UInt32 :=
  (Array.range 259).map fun len =>
    match findLengthCode len with
    | some (idx, en, ev) => packCode idx en ev
    | none => 0

/-- Dense distance-code table: entry `dist` (0–32768) packs
    `findDistCode dist`. -/
def distCodeTab : Array UInt32 :=
  (Array.range 32769).map fun dist =>
    match findDistCode dist with
    | some (idx, en, ev) => packCode idx en ev
    | none => 0

@[simp] theorem lenCodeTab_size : lenCodeTab.size = 259 := by
  simp [lenCodeTab]

@[simp] theorem distCodeTab_size : distCodeTab.size = 32769 := by
  simp [distCodeTab]

private theorem lenCodeTab_getElem {len idx en : Nat} {ev : UInt32} (hlen : len < 259)
    (h : findLengthCode len = some (idx, en, ev)) :
    lenCodeTab[len]'(lenCodeTab_size ▸ hlen) = packCode idx en ev := by
  simp only [lenCodeTab, Array.getElem_map, Array.getElem_range, h]

private theorem distCodeTab_getElem {dist idx en : Nat} {ev : UInt32} (hdist : dist < 32769)
    (h : findDistCode dist = some (idx, en, ev)) :
    distCodeTab[dist]'(distCodeTab_size ▸ hdist) = packCode idx en ev := by
  simp only [distCodeTab, Array.getElem_map, Array.getElem_range, h]

/-- Table-backed `findLengthCode`: one dense-array read for the in-range
    lengths (0–258), the linear search beyond. Equal to `findLengthCode`
    everywhere (`findLengthCodeFast_eq`). -/
@[inline] def findLengthCodeFast (length : Nat) : Option (Nat × Nat × UInt32) :=
  if h : length < 259 then
    let e := lenCodeTab[length]'(lenCodeTab_size ▸ h)
    some ((e &&& 0xFF).toNat, ((e >>> 8) &&& 0xFF).toNat, e >>> 16)
  else findLengthCode length

/-- Table-backed `findDistCode`: one dense-array read for the in-range
    distances (0–32768), the linear search beyond. Equal to `findDistCode`
    everywhere (`findDistCodeFast_eq`). -/
@[inline] def findDistCodeFast (dist : Nat) : Option (Nat × Nat × UInt32) :=
  if h : dist < 32769 then
    let e := distCodeTab[dist]'(distCodeTab_size ▸ h)
    some ((e &&& 0xFF).toNat, ((e >>> 8) &&& 0xFF).toNat, e >>> 16)
  else findDistCode dist

theorem findLengthCodeFast_eq (length : Nat) :
    findLengthCodeFast length = findLengthCode length := by
  unfold findLengthCodeFast
  split
  · rename_i hlen
    match hflc : findLengthCode length with
    | none =>
      exfalso
      have hs := findLengthCode_isSome length
      rw [hflc] at hs
      exact nomatch hs
    | some (idx, en, ev) =>
      have hidx : idx < 29 := findLengthCode_idx_lt hflc
      obtain ⟨hen, hev⟩ := findTableCode_go_fields hflc
      have hen' : en < 256 := by
        rw [hen]; exact UInt8.toNat_lt _
      have hev' : ev < 65536 := by
        change ev.toNat < 65536
        rw [hev]
        simp only [Nat.toUInt32, UInt32.toNat_ofNat']
        omega
      rw [lenCodeTab_getElem hlen hflc]
      obtain ⟨h1, h2, h3⟩ := packCode_fields (idx := idx) (by omega) hen' hev'
      simp only [h1, h2, h3]
  · rfl

theorem findDistCodeFast_eq (dist : Nat) :
    findDistCodeFast dist = findDistCode dist := by
  unfold findDistCodeFast
  split
  · rename_i hdist
    match hfdc : findDistCode dist with
    | none =>
      exfalso
      have hs := findDistCode_isSome dist
      rw [hfdc] at hs
      exact nomatch hs
    | some (idx, en, ev) =>
      have hidx : idx < 30 := findDistCode_idx_lt hfdc
      obtain ⟨hen, hev⟩ := findTableCode_go_fields hfdc
      have hen' : en < 256 := by
        rw [hen]; exact UInt8.toNat_lt _
      have hev' : ev < 65536 := by
        change ev.toNat < 65536
        rw [hev]
        simp only [Nat.toUInt32, UInt32.toNat_ofNat']
        omega
      rw [distCodeTab_getElem hdist hfdc]
      obtain ⟨h1, h2, h3⟩ := packCode_fields (idx := idx) (by omega) hen' hev'
      simp only [h1, h2, h3]
  · rfl

end Scratch
