import Zip.Native.Inflate
import Zip.Native.Wide

/-!
# Tree-free canonical decode — the production DEFLATE decoder

This file defines the **production** decoders `Inflate.inflate` / `inflateRaw`: a
DEFLATE Huffman decode that builds **no** Huffman tree. The fast ≤11-bit codes go
through the canonical 11-bit table (`buildTableCanonicalFast`), and the rare >11-bit
codes go through a canonical bit-by-bit decode keyed off the per-length
`count` / `firstCode` / sorted-symbol arrays — never a tree walk. This skips the
`fromLengths`/`insertLoop` build entirely (the ~7% decode win).

The decode loops are well-founded (`termination_by`, mirroring the verified
`goFusedP`/`goFusedPU`/`inflateLoop`); the canonical structures and their
correctness are proven in `Zip.Spec.InflateTreeFreeCorrect`.

`decodeDynamicLengthsOnly` runs the same `HuffTree.validateLengths`
(`maxBits`/Kraft) check `decodeDynamicTrees` does, so the production decoder's
accept-set is **exactly** the verified reference's
(`Inflate.inflateReference` / `inflateRawReference`, in `Zip.Native.Inflate`) —
proven as the two-sided `inflate_ok_iff_reference`
(`inflate data = .ok out ↔ inflateReference data = .ok out`) and
`inflateRaw_ok_iff_reference`. Every decode-correctness theorem about the
reference therefore transfers, and the `native ⊆ FFI` posture is preserved.
-/

namespace Zip.Native
open ZipCommon (BitReader)

namespace HuffTree

/-- Canonical long-code decode tables (for codes longer than the 11-bit window):
    `count[len]` codes of each length, `firstCode[len]` the first canonical code
    of that length, `firstIndex[len]` the offset into `symbols` (symbols sorted by
    `(length, symbol)`). -/
structure LongDecode where
  count : Array Nat
  firstCode : Array Nat
  firstIndex : Array Nat
  symbols : Array UInt16

/-- `firstIndex[len]` = number of positive-length symbols of length `< len`
    (prefix sum of `count`). Well-founded form of the prototype loop. -/
def buildFirstIndex (count : Array Nat) (maxBits : Nat) : Array Nat :=
  go 1 0 (Array.replicate (maxBits + 2) 0)
where
  go (len idx : Nat) (fi : Array Nat) : Array Nat :=
    if len > maxBits then fi
    else go (len + 1) (idx + count[len]!) (fi.set! len idx)
  termination_by maxBits + 1 - len
  decreasing_by omega

/-- Counting sort: place each positive-length symbol at `offset[len]` (starting
    from `firstIndex`), so `symbols` lists symbols by `(length, symbol)`. -/
def buildSymbols (lengths : Array UInt8) (maxBits total : Nat) (firstIndex : Array Nat) :
    Array UInt16 :=
  go 0 firstIndex (Array.replicate total 0)
where
  go (s : Nat) (offset : Array Nat) (symbols : Array UInt16) : Array UInt16 :=
    if s ≥ lengths.size then symbols
    else
      let l := lengths[s]!.toNat
      if 0 < l ∧ l ≤ maxBits then
        go (s + 1) (offset.set! l (offset[l]! + 1)) (symbols.set! offset[l]! s.toUInt16)
      else go (s + 1) offset symbols
  termination_by lengths.size - s
  decreasing_by all_goals omega

/-- Build the canonical long-code tables from code lengths in O(n + maxBits).
    `firstCode` is the canonical first-code-per-length recurrence (RFC 1951
    §3.2.2), exactly `Huffman.Spec.nextCodes`; `firstIndex`/`symbols` are the
    prefix-sum and counting-sort over the code lengths. -/
def buildLongDecode (lengths : Array UInt8) (maxBits : Nat) : LongDecode :=
  let count := countLengthsFast lengths maxBits
  let firstCode := Huffman.Spec.nextCodes count maxBits
  let firstIndex := buildFirstIndex count maxBits
  let total := firstIndex[maxBits]! + count[maxBits]!
  let symbols := buildSymbols lengths maxBits total firstIndex
  { count, firstCode, firstIndex, symbols }

/-- Does any codeword exceed the `fastBits`-wide fast table — i.e. can the
    `walkCanonical` long-code fallback ever fire productively? `count[len] > 0` for
    some `fastBits < len ≤ maxBits`. When this is `false`, every codeword resolves
    in the fast table, so the long-code counting sort (`buildSymbols`, allocating a
    `total`-element array) is dead work. One pass over the small `count` array. -/
def hasLongCode (count : Array Nat) (maxBits : Nat) : Bool :=
  go count maxBits (fastBits + 1)
where
  go (count : Array Nat) (maxBits len : Nat) : Bool :=
    if len > maxBits then false
    else if count[len]! > 0 then true
    else go count maxBits (len + 1)
  termination_by maxBits + 1 - len

/-- `buildLongDecode` sharing a precomputed length histogram, and skipping the
    `buildSymbols` counting sort entirely when no codeword exceeds the fast table
    (`hasLongCode count maxBits = false`). In that case `walkCanonical` is never
    productive — every codeword resolves in the fast `fastBits`-bit table — so the
    `total`-element `symbols` allocation is dead work and we leave it empty. When a
    long code does exist this matches `buildLongDecode` exactly
    (`buildLongDecodeWithCount_eq`). -/
def buildLongDecodeWithCount (lengths : Array UInt8) (count : Array Nat) (maxBits : Nat) :
    LongDecode :=
  let firstCode := Huffman.Spec.nextCodes count maxBits
  let firstIndex := buildFirstIndex count maxBits
  if hasLongCode count maxBits then
    let total := firstIndex[maxBits]! + count[maxBits]!
    let symbols := buildSymbols lengths maxBits total firstIndex
    { count, firstCode, firstIndex, symbols }
  else
    { count, firstCode, firstIndex, symbols := #[] }

/-- Canonical bit-by-bit long-code decode: read bits MSB-first, accumulate the
    code value, and return the symbol once the code lands in some length's
    canonical range. Tree-free replacement for `walkTree`. -/
def walkCanonical (ld : LongDecode) (maxBits : Nat) (bitBuf : UInt64) (cnt : Nat) :
    Except String (UInt16 × UInt64 × Nat × Nat) :=
  go 1 0 bitBuf cnt
where
  go (len code : Nat) (bitBuf : UInt64) (cnt : Nat) :
      Except String (UInt16 × UInt64 × Nat × Nat) :=
    if hlen : len > maxBits then .error "Inflate: invalid Huffman code"
    else if cnt = 0 then .error "BitReader: unexpected end of input"
    else
      let code := code * 2 + (bitBuf &&& 1).toNat
      let bitBuf := bitBuf >>> 1
      let cnt := cnt - 1
      let fc := ld.firstCode[len]!
      let cl := ld.count[len]!
      if fc ≤ code ∧ code < fc + cl then
        .ok (ld.symbols[ld.firstIndex[len]! + (code - fc)]!, bitBuf, cnt, len)
      else go (len + 1) code bitBuf cnt
  termination_by maxBits + 1 - len
  decreasing_by omega

/-- `decodeSym` with the canonical long-code fallback (no tree). -/
@[inline] def decodeSymCanon (ld : LongDecode) (table : DecodeTable) (maxBits : Nat)
    (bitBuf : UInt64) (cnt : Nat) : Except String (UInt16 × UInt64 × Nat × Nat) :=
  let idx := (bitBuf &&& 0x7FF).toNat
  let e := table.entryAt idx
  let len := (unpackLen e).toNat
  if len == 0 || len > cnt then walkCanonical ld maxBits bitBuf cnt
  else .ok (unpackSym e, bitBuf >>> len.toUInt64, cnt - len, len)

end HuffTree

namespace InflateBuf
open Zip.Native.HuffTree (DecodeTable LongDecode decodeSymCanon)

/-- Tree-free copy of `goFusedP`: same wide-buffer loop, with the canonical
    long-code fallback (`decodeSymCanon`) in place of the tree walk. -/
def goTreeFree (litTable distTable : DecodeTable) (litLD distLD : LongDecode)
    (maxBits : Nat) (data : ByteArray) (maxOut : Nat)
    (pos : Nat) (bitBuf : UInt64) (cnt : Nat) (output : ByteArray) :
    Except String (ByteArray × Nat × UInt64 × Nat) := do
  if hrc : cnt ≤ 56 ∧ pos < data.size then
    goTreeFree litTable distTable litLD distLD maxBits data maxOut
      (pos + 1) (bitBuf ||| (data[pos]!.toUInt64 <<< cnt.toUInt64)) (cnt + 8) output
  else
  if hlit : (litTable.lenAt (bitBuf &&& 0x7FF).toNat).toNat ≠ 0
      ∧ (litTable.lenAt (bitBuf &&& 0x7FF).toNat).toNat ≤ cnt
      ∧ litTable.symAt (bitBuf &&& 0x7FF).toNat < 256 then
    if output.size ≥ maxOut then throw "Inflate: output exceeds maximum size"
    else
      goTreeFree litTable distTable litLD distLD maxBits data maxOut pos
        (bitBuf >>> ((litTable.lenAt (bitBuf &&& 0x7FF).toNat).toNat).toUInt64)
        (cnt - (litTable.lenAt (bitBuf &&& 0x7FF).toNat).toNat)
        (output.push (litTable.symAt (bitBuf &&& 0x7FF).toNat).toUInt8)
  else
  let cnt0 := cnt
  match decodeSymCanon litLD litTable maxBits bitBuf cnt with
  | .error e => .error e
  | .ok (sym, bitBuf, cnt, _used) =>
    if sym < 256 then
      if output.size ≥ maxOut then throw "Inflate: output exceeds maximum size"
      else if hnp : cnt0 ≤ cnt then throw "Inflate: no progress in Huffman decode"
      else goTreeFree litTable distTable litLD distLD maxBits data maxOut pos bitBuf cnt (output.push sym.toUInt8)
    else if sym == 256 then .ok (output, pos, bitBuf, cnt)
    else
      let idx := sym.toNat - 257
      if h : idx ≥ Inflate.lengthBase.size then throw s!"Inflate: invalid length code {sym}"
      else
        let base := Inflate.lengthBase[idx]
        let extra := Inflate.lengthExtra[idx]'(by simp [Inflate.lengthExtra_size, Inflate.lengthBase_size] at h ⊢; omega)
        let (extraBits, bitBuf, cnt) ← takeBits bitBuf cnt extra.toNat
        let length := base.toNat + extraBits
        match decodeSymCanon distLD distTable maxBits bitBuf cnt with
        | .error e => .error e
        | .ok (distSym, bitBuf, cnt, _dused) =>
          let dIdx := distSym.toNat
          if h : dIdx ≥ Inflate.distBase.size then throw s!"Inflate: invalid distance code {distSym}"
          else
            let dBase := Inflate.distBase[dIdx]
            let dExtra := Inflate.distExtra[dIdx]'(by simp [Inflate.distExtra_size, Inflate.distBase_size] at h ⊢; omega)
            let (dExtraBits, bitBuf, cnt) ← takeBits bitBuf cnt dExtra.toNat
            let distance := dBase.toNat + dExtraBits
            if hz : distance = 0 then throw s!"Inflate: zero back-reference distance"
            else if hds : distance > output.size then
              throw s!"Inflate: distance {distance} exceeds output size {output.size}"
            else if output.size + length > maxOut then throw "Inflate: output exceeds maximum size"
            else if hnp : cnt0 ≤ cnt then throw "Inflate: no progress in Huffman decode"
            else
              let out := Inflate.copyLoop output (output.size - distance) distance 0 length
                (by omega) (by omega)
              goTreeFree litTable distTable litLD distLD maxBits data maxOut pos bitBuf cnt out
  termination_by (data.size - pos) * 9 + cnt
  decreasing_by
    · obtain ⟨_, hp⟩ := hrc; omega
    · obtain ⟨hne, hle, _⟩ := hlit; omega
    · omega
    · omega

set_option maxRecDepth 4096 in
/-- USize-scalar copy of `goTreeFree` (mirrors `goFusedPU`): `pos`/`cnt` are
    unboxed `USize`, the refill uses `data.uget`; same canonical long-code
    fallback. Well-founded (termination mirrors `goFusedPU`). -/
def goTreeFreeU (litTable distTable : DecodeTable) (litLD distLD : LongDecode)
    (maxBits : Nat) (data : ByteArray) (maxOut : Nat)
    (pos : USize) (bitBuf : UInt64) (cnt : USize)
    (hsz : data.size < USize.size) (output : ByteArray) :
    Except String (ByteArray × USize × UInt64 × USize) := do
  if hrc : cnt ≤ 56 ∧ pos < data.size.toUSize then
    goTreeFreeU litTable distTable litLD distLD maxBits data maxOut
      (pos + 1)
      (bitBuf ||| ((data.uget pos (by
          have h := USize.lt_iff_toNat_lt.mp hrc.2
          rwa [toUSize_toNat_of_lt hsz] at h)).toUInt64 <<< cnt.toUInt64))
      (cnt + 8) hsz output
  else
  let e := litTable.entryAt (bitBuf &&& 0x7FF).toNat
  if hlit : HuffTree.unpackLen e ≠ 0
      ∧ (HuffTree.unpackLen e).toUSize ≤ cnt
      ∧ HuffTree.unpackSym e < 256 then
    if output.size ≥ maxOut then throw "Inflate: output exceeds maximum size"
    else
      goTreeFreeU litTable distTable litLD distLD maxBits data maxOut pos
        (bitBuf >>> (HuffTree.unpackLen e).toUInt64)
        (cnt - (HuffTree.unpackLen e).toUSize)
        hsz
        (output.push (HuffTree.unpackSym e).toUInt8)
  else
  let cnt0 := cnt.toNat
  match decodeSymCanon litLD litTable maxBits bitBuf cnt.toNat with
  | .error e => .error e
  | .ok (sym, bitBuf, cnt', _used) =>
    if sym < 256 then
      if output.size ≥ maxOut then throw "Inflate: output exceeds maximum size"
      else if hnp : cnt0 ≤ cnt' then throw "Inflate: no progress in Huffman decode"
      else
        goTreeFreeU litTable distTable litLD distLD maxBits data maxOut pos bitBuf
          cnt'.toUSize hsz (output.push sym.toUInt8)
    else if sym == 256 then .ok (output, pos, bitBuf, cnt'.toUSize)
    else
      let idx := sym.toNat - 257
      if h : idx ≥ Inflate.lengthBase.size then throw s!"Inflate: invalid length code {sym}"
      else
        let base := Inflate.lengthBase[idx]
        let extra := Inflate.lengthExtra[idx]'(by simp [Inflate.lengthExtra_size, Inflate.lengthBase_size] at h ⊢; omega)
        let (extraBits, bitBuf, cnt'') ← takeBits bitBuf cnt' extra.toNat
        let length := base.toNat + extraBits
        match decodeSymCanon distLD distTable maxBits bitBuf cnt'' with
        | .error e => .error e
        | .ok (distSym, bitBuf, cnt3, _dused) =>
          let dIdx := distSym.toNat
          if h : dIdx ≥ Inflate.distBase.size then throw s!"Inflate: invalid distance code {distSym}"
          else
            let dBase := Inflate.distBase[dIdx]
            let dExtra := Inflate.distExtra[dIdx]'(by simp [Inflate.distExtra_size, Inflate.distBase_size] at h ⊢; omega)
            let (dExtraBits, bitBuf, cnt4) ← takeBits bitBuf cnt3 dExtra.toNat
            let distance := dBase.toNat + dExtraBits
            if hz : distance = 0 then throw s!"Inflate: zero back-reference distance"
            else if hds : distance > output.size then
              throw s!"Inflate: distance {distance} exceeds output size {output.size}"
            else if output.size + length > maxOut then throw "Inflate: output exceeds maximum size"
            else if hnp : cnt0 ≤ cnt4 then throw "Inflate: no progress in Huffman decode"
            else
              let out := Inflate.copyLoop output (output.size - distance) distance 0 length
                (by omega) (by omega)
              goTreeFreeU litTable distTable litLD distLD maxBits data maxOut pos bitBuf
                cnt4.toUSize hsz out
  termination_by (data.size - pos.toNat) * 9 + cnt.toNat
  decreasing_by
    · obtain ⟨hc, hp⟩ := hrc
      have hbig : (64 : Nat) < 2 ^ System.Platform.numBits :=
        USize.size_eq_two_pow ▸ Nat.lt_of_lt_of_le (by decide) USize.le_size
      have hpn : pos.toNat < data.size := by
        have h := USize.lt_iff_toNat_lt.mp hp; rwa [toUSize_toNat_of_lt hsz] at h
      have hcn : cnt.toNat ≤ 56 := by
        have h := USize.le_iff_toNat_le.mp hc
        rwa [USize.toNat_ofNat_of_lt (Nat.lt_of_lt_of_le (by decide) USize.le_size)] at h
      have hpa : (pos + 1).toNat = pos.toNat + 1 := by
        rw [USize.toNat_add, USize.toNat_one]; apply Nat.mod_eq_of_lt
        have : pos.toNat + 1 < USize.size := by omega
        exact USize.size_eq_two_pow ▸ this
      have h8 : (8 : USize).toNat = 8 :=
        USize.toNat_ofNat_of_lt (Nat.lt_of_lt_of_le (by decide) USize.le_size)
      have hca : (cnt + 8).toNat = cnt.toNat + 8 := by
        rw [USize.toNat_add, h8]; apply Nat.mod_eq_of_lt; omega
      rw [hpa, hca]; omega
    · obtain ⟨hne, hle, _⟩ := hlit
      have hne' : (HuffTree.unpackLen e).toNat ≠ 0 := (uint8_ne_zero_iff_toNat _).mp hne
      have hlen : ((HuffTree.unpackLen e).toUSize).toNat = (HuffTree.unpackLen e).toNat :=
        UInt8.toNat_toUSize _
      have hsub : (cnt - (HuffTree.unpackLen e).toUSize).toNat
          = cnt.toNat - (HuffTree.unpackLen e).toNat := by
        rw [USize.toNat_sub_of_le _ _ hle, hlen]
      have hlecnt : (HuffTree.unpackLen e).toNat ≤ cnt.toNat :=
        hlen ▸ USize.le_iff_toNat_le.mp hle
      rw [hsub]; omega
    · have hcsz : cnt.toNat < USize.size := cnt.toNat_lt_two_pow_numBits
      have hb : cnt'.toUSize.toNat = cnt' := toUSize_toNat_of_lt (by omega)
      rw [hb]; omega
    · have hcsz : cnt.toNat < USize.size := cnt.toNat_lt_two_pow_numBits
      have hb : cnt4.toUSize.toNat = cnt4 := toUSize_toNat_of_lt (by omega)
      rw [hb]; omega

/-- A small `USize` (`≤ 7`) increments without wrapping. Discharges the
    pending-literal-count bound carried by `goTreeFreeUB`. -/
private theorem usize_toNat_add_one_of_le_7 {c : USize} (h : c.toNat ≤ 7) :
    (c + 1).toNat = c.toNat + 1 := by
  rw [USize.toNat_add, USize.toNat_one]
  have h9 : (9 : Nat) < USize.size := Nat.lt_of_lt_of_le (by decide) USize.le_size
  have : c.toNat + 1 < USize.size := by omega
  exact Nat.mod_eq_of_lt (USize.size_eq_two_pow ▸ this)

set_option maxRecDepth 4096 in
/-- Literal-batching variant of `goTreeFreeU` (#2795): up to eight consecutive
    literals accumulate LSB-first into the `UInt64` word `litAcc` (`litCnt` of
    them pending, `≤ 7` at entry) and reach `output` as **one**
    `ByteArray.pushUInt64LE` call — a single out-of-line append per eight
    literals instead of a `lean_byte_array_push` call (exclusivity + capacity
    check + size bump) per literal. The batch flushes when the eighth literal
    arrives and at the top of the slow branch, i.e. before anything that
    observes `output` (long-code literal, back-reference copy, end-of-block);
    the output-limit guard reads the conceptual size `output.size + litCnt`.
    Proven equal to `goTreeFreeU` over the flushed output
    (`Zip.Spec.InflateTreeFreeCorrect.goTreeFreeUB_eq`), through the flush
    extern's proven reference body `ByteArray.pushLEBytes`, under the invariant
    that `litAcc`'s bits at and above `8·litCnt` are zero. -/
def goTreeFreeUB (litTable distTable : DecodeTable) (litLD distLD : LongDecode)
    (maxBits : Nat) (data : ByteArray) (maxOut : Nat)
    (pos : USize) (bitBuf : UInt64) (cnt : USize)
    (hsz : data.size < USize.size)
    (litAcc : UInt64) (litCnt : USize) (hlc : litCnt.toNat ≤ 7)
    (output : ByteArray) :
    Except String (ByteArray × USize × UInt64 × USize) := do
  if hrc : cnt ≤ 56 ∧ pos < data.size.toUSize then
    goTreeFreeUB litTable distTable litLD distLD maxBits data maxOut
      (pos + 1)
      (bitBuf ||| ((data.uget pos (by
          have h := USize.lt_iff_toNat_lt.mp hrc.2
          rwa [toUSize_toNat_of_lt hsz] at h)).toUInt64 <<< cnt.toUInt64))
      (cnt + 8) hsz litAcc litCnt hlc output
  else
  let e := litTable.entryAt (bitBuf &&& 0x7FF).toNat
  if hlit : HuffTree.unpackLen e ≠ 0
      ∧ (HuffTree.unpackLen e).toUSize ≤ cnt
      ∧ HuffTree.unpackSym e < 256 then
    -- CEILING PROBE (measurement-only, NOT semantics-preserving): the original
    -- cheap guard, off by ≤ 7 bytes at the output limit. Isolates the pure
    -- effect of removing the per-literal push call from the guard arithmetic.
    if output.size ≥ maxOut then throw "Inflate: output exceeds maximum size"
    else
      let litAcc := litAcc ||| ((HuffTree.unpackSym e).toUInt64 <<< (8 * litCnt.toUInt64))
      if hfull : litCnt = 7 then
        goTreeFreeUB litTable distTable litLD distLD maxBits data maxOut pos
          (bitBuf >>> (HuffTree.unpackLen e).toUInt64)
          (cnt - (HuffTree.unpackLen e).toUSize)
          hsz 0 0 (by simp)
          (output.pushUInt64LE litAcc 8 (by
            rw [USize.toNat_ofNat_of_lt (Nat.lt_of_lt_of_le (by decide) USize.le_size)]
            exact Nat.le_refl 8))
      else
        goTreeFreeUB litTable distTable litLD distLD maxBits data maxOut pos
          (bitBuf >>> (HuffTree.unpackLen e).toUInt64)
          (cnt - (HuffTree.unpackLen e).toUSize)
          hsz litAcc (litCnt + 1) (by
            rw [usize_toNat_add_one_of_le_7 hlc]
            have h7 : (7 : USize).toNat = 7 :=
              USize.toNat_ofNat_of_lt (Nat.lt_of_lt_of_le (by decide) USize.le_size)
            have : litCnt.toNat ≠ 7 := fun h => hfull (USize.toNat_inj.mp (h7 ▸ h))
            omega)
          output
  else
  let output := output.pushUInt64LE litAcc litCnt (by omega)
  let cnt0 := cnt.toNat
  match decodeSymCanon litLD litTable maxBits bitBuf cnt.toNat with
  | .error e => .error e
  | .ok (sym, bitBuf, cnt', _used) =>
    if sym < 256 then
      if output.size ≥ maxOut then throw "Inflate: output exceeds maximum size"
      else if hnp : cnt0 ≤ cnt' then throw "Inflate: no progress in Huffman decode"
      else
        goTreeFreeUB litTable distTable litLD distLD maxBits data maxOut pos bitBuf
          cnt'.toUSize hsz 0 0 (by simp) (output.push sym.toUInt8)
    else if sym == 256 then .ok (output, pos, bitBuf, cnt'.toUSize)
    else
      let idx := sym.toNat - 257
      if h : idx ≥ Inflate.lengthBase.size then throw s!"Inflate: invalid length code {sym}"
      else
        let base := Inflate.lengthBase[idx]
        let extra := Inflate.lengthExtra[idx]'(by simp [Inflate.lengthExtra_size, Inflate.lengthBase_size] at h ⊢; omega)
        let (extraBits, bitBuf, cnt'') ← takeBits bitBuf cnt' extra.toNat
        let length := base.toNat + extraBits
        match decodeSymCanon distLD distTable maxBits bitBuf cnt'' with
        | .error e => .error e
        | .ok (distSym, bitBuf, cnt3, _dused) =>
          let dIdx := distSym.toNat
          if h : dIdx ≥ Inflate.distBase.size then throw s!"Inflate: invalid distance code {distSym}"
          else
            let dBase := Inflate.distBase[dIdx]
            let dExtra := Inflate.distExtra[dIdx]'(by simp [Inflate.distExtra_size, Inflate.distBase_size] at h ⊢; omega)
            let (dExtraBits, bitBuf, cnt4) ← takeBits bitBuf cnt3 dExtra.toNat
            let distance := dBase.toNat + dExtraBits
            if hz : distance = 0 then throw s!"Inflate: zero back-reference distance"
            else if hds : distance > output.size then
              throw s!"Inflate: distance {distance} exceeds output size {output.size}"
            else if output.size + length > maxOut then throw "Inflate: output exceeds maximum size"
            else if hnp : cnt0 ≤ cnt4 then throw "Inflate: no progress in Huffman decode"
            else
              let out := Inflate.copyLoop output (output.size - distance) distance 0 length
                (by omega) (by omega)
              goTreeFreeUB litTable distTable litLD distLD maxBits data maxOut pos bitBuf
                cnt4.toUSize hsz 0 0 (by simp) out
  termination_by (data.size - pos.toNat) * 9 + cnt.toNat
  decreasing_by
    · obtain ⟨hc, hp⟩ := hrc
      have hbig : (64 : Nat) < 2 ^ System.Platform.numBits :=
        USize.size_eq_two_pow ▸ Nat.lt_of_lt_of_le (by decide) USize.le_size
      have hpn : pos.toNat < data.size := by
        have h := USize.lt_iff_toNat_lt.mp hp; rwa [toUSize_toNat_of_lt hsz] at h
      have hcn : cnt.toNat ≤ 56 := by
        have h := USize.le_iff_toNat_le.mp hc
        rwa [USize.toNat_ofNat_of_lt (Nat.lt_of_lt_of_le (by decide) USize.le_size)] at h
      have hpa : (pos + 1).toNat = pos.toNat + 1 := by
        rw [USize.toNat_add, USize.toNat_one]; apply Nat.mod_eq_of_lt
        have : pos.toNat + 1 < USize.size := by omega
        exact USize.size_eq_two_pow ▸ this
      have h8 : (8 : USize).toNat = 8 :=
        USize.toNat_ofNat_of_lt (Nat.lt_of_lt_of_le (by decide) USize.le_size)
      have hca : (cnt + 8).toNat = cnt.toNat + 8 := by
        rw [USize.toNat_add, h8]; apply Nat.mod_eq_of_lt; omega
      rw [hpa, hca]; omega
    · obtain ⟨hne, hle, _⟩ := hlit
      have hne' : (HuffTree.unpackLen e).toNat ≠ 0 := (uint8_ne_zero_iff_toNat _).mp hne
      have hlen : ((HuffTree.unpackLen e).toUSize).toNat = (HuffTree.unpackLen e).toNat :=
        UInt8.toNat_toUSize _
      have hsub : (cnt - (HuffTree.unpackLen e).toUSize).toNat
          = cnt.toNat - (HuffTree.unpackLen e).toNat := by
        rw [USize.toNat_sub_of_le _ _ hle, hlen]
      have hlecnt : (HuffTree.unpackLen e).toNat ≤ cnt.toNat :=
        hlen ▸ USize.le_iff_toNat_le.mp hle
      rw [hsub]; omega
    · obtain ⟨hne, hle, _⟩ := hlit
      have hne' : (HuffTree.unpackLen e).toNat ≠ 0 := (uint8_ne_zero_iff_toNat _).mp hne
      have hlen : ((HuffTree.unpackLen e).toUSize).toNat = (HuffTree.unpackLen e).toNat :=
        UInt8.toNat_toUSize _
      have hsub : (cnt - (HuffTree.unpackLen e).toUSize).toNat
          = cnt.toNat - (HuffTree.unpackLen e).toNat := by
        rw [USize.toNat_sub_of_le _ _ hle, hlen]
      have hlecnt : (HuffTree.unpackLen e).toNat ≤ cnt.toNat :=
        hlen ▸ USize.le_iff_toNat_le.mp hle
      rw [hsub]; omega
    · have hcsz : cnt.toNat < USize.size := cnt.toNat_lt_two_pow_numBits
      have hb : cnt'.toUSize.toNat = cnt' := toUSize_toNat_of_lt (by omega)
      rw [hb]; omega
    · have hcsz : cnt.toNat < USize.size := cnt.toNat_lt_two_pow_numBits
      have hb : cnt4.toUSize.toNat = cnt4 := toUSize_toNat_of_lt (by omega)
      rw [hb]; omega

/-- Tree-free wide-buffer block decode from prebuilt tables: runs the tree-free
    loop (no Huffman tree) over the already-constructed fast/long decode tables.
    Runs the unboxed `goTreeFreeU` when the input is addressable, else the boxed
    `goTreeFree` — mirroring `goFusedPDispatch`. Factored out of
    `decodeHuffmanFastBufTreeFree` so the fixed-Huffman path can pass the
    compile-time-constant fixed tables instead of rebuilding them every block. -/
def decodeHuffmanFastBufTables (br : BitReader) (output : ByteArray)
    (litTable distTable : DecodeTable) (litLD distLD : LongDecode) (maxOut : Nat) :
    Except String (ByteArray × BitReader) := do
  let (pos, bitBuf, cnt) := refill br.data br.pos 0 0
  let bitBuf := bitBuf >>> br.bitOff.toUInt64
  let cnt := cnt - br.bitOff
  let (out, pos', bitBuf', cnt') ←
    if hsz : br.data.size.toUSize.toNat = br.data.size then
      Except.map (fun x => (x.1, x.2.1.toNat, x.2.2.1, x.2.2.2.toNat))
        (goTreeFreeUB litTable distTable litLD distLD 15 br.data maxOut
          pos.toUSize bitBuf cnt.toUSize (by rw [← hsz]; exact USize.toNat_lt_two_pow_numBits _)
          0 0 (by simp) output)
    else
      goTreeFree litTable distTable litLD distLD 15 br.data maxOut pos bitBuf cnt output
  let _ := bitBuf'
  let endbit := pos' * 8 - cnt'
  .ok (out, { data := br.data, pos := endbit / 8, bitOff := endbit % 8 })

/-- Tree-free wide-buffer block decode: builds the fast tables canonically and
    the long-code tables, then runs the tree-free loop (no Huffman tree) via
    `decodeHuffmanFastBufTables`. -/
def decodeHuffmanFastBufTreeFree (br : BitReader) (output : ByteArray)
    (litLengths distLengths : Array UInt8) (maxOut : Nat) :
    Except String (ByteArray × BitReader) :=
  let litCount := HuffTree.countLengthsFast litLengths 15
  let distCount := HuffTree.countLengthsFast distLengths 15
  let litTable := HuffTree.buildTableCanonicalFastWithCount litLengths litCount 15
  let distTable := HuffTree.buildTableCanonicalFastWithCount distLengths distCount 15
  let litLD := HuffTree.buildLongDecodeWithCount litLengths litCount 15
  let distLD := HuffTree.buildLongDecodeWithCount distLengths distCount 15
  decodeHuffmanFastBufTables br output litTable distTable litLD distLD maxOut

end InflateBuf

namespace Inflate

open Zip.Native.HuffTree (DecodeTable LongDecode)

/-! ### Fixed-Huffman decode tables as compile-time constants

RFC 1951 §3.2.6 fixes the lit/length and distance code lengths, so their canonical
decode tables and long-code tables are the same for *every* fixed block. As nullary
`def`s these are closed terms: the Lean runtime computes each exactly once (via a
`lean_once_cell_t`) and caches it, so the fixed-Huffman decode path never rebuilds a
table. `decodeHuffmanFastBufFixed` runs `decodeHuffmanFastBufTables` over these
constants, and is proven equal to the per-block build
(`Zip.Spec.InflateTreeFreeCorrect.decodeHuffmanFastBufFixed_eq`). -/

/-- Per-length histogram for `fixedLitLengths` (shared by the fixed lit table and
    long-decode table). -/
def fixedLitCount : Array Nat := HuffTree.countLengthsFast fixedLitLengths 15

/-- Per-length histogram for `fixedDistLengths`. -/
def fixedDistCount : Array Nat := HuffTree.countLengthsFast fixedDistLengths 15

/-- The fixed lit/length canonical fast decode table (RFC 1951 §3.2.6), built once. -/
def fixedLitTable : DecodeTable :=
  HuffTree.buildTableCanonicalFastWithCount fixedLitLengths fixedLitCount 15

/-- The fixed distance canonical fast decode table (RFC 1951 §3.2.6), built once. -/
def fixedDistTable : DecodeTable :=
  HuffTree.buildTableCanonicalFastWithCount fixedDistLengths fixedDistCount 15

/-- The fixed lit/length long-code decode table, built once. -/
def fixedLitLD : LongDecode := HuffTree.buildLongDecodeWithCount fixedLitLengths fixedLitCount 15

/-- The fixed distance long-code decode table, built once. -/
def fixedDistLD : LongDecode := HuffTree.buildLongDecodeWithCount fixedDistLengths fixedDistCount 15

/-- Fixed-Huffman block decode over the compile-time-constant fixed tables — no
    per-block table build. Equal to
    `decodeHuffmanFastBufTreeFree br output fixedLitLengths fixedDistLengths maxOut`
    (`decodeHuffmanFastBufFixed_eq`). -/
def decodeHuffmanFastBufFixed (br : BitReader) (output : ByteArray) (maxOut : Nat) :
    Except String (ByteArray × BitReader) :=
  InflateBuf.decodeHuffmanFastBufTables br output fixedLitTable fixedDistTable
    fixedLitLD fixedDistLD maxOut

/-- Like `decodeDynamicTrees`, but returns only the code-length vectors — it never
    builds the lit/dist Huffman trees (the whole point of the tree-free path). The
    small code-length tree (`clTree`, 19 symbols) is still built to decode the
    length symbols.

    The lit/dist length vectors are still run through `HuffTree.validateLengths`
    (the `maxBits`/Kraft check `fromLengths` performs) so this rejects exactly the
    malformed code-length sets `decodeDynamicTrees` rejects, with identical error
    messages — closing the strictness gap the tree-free path would otherwise open
    (`Zip.Spec.InflateTreeFreeCorrect.decodeDynamicTrees_of_lengthsOnly`, the
    converse of `decodeDynamicTrees_extract`). The check is computable from the
    lengths alone — no tree is built. -/
def decodeDynamicLengthsOnly (br : BitReader) :
    Except String (Array UInt8 × Array UInt8 × BitReader) := do
  let (hlit, br) ← br.readBits 5
  let (hdist, br) ← br.readBits 5
  let (hclen, br) ← br.readBits 4
  let numLitLen := hlit.toNat + 257
  let numDist := hdist.toNat + 1
  let numCodeLen := hclen.toNat + 4
  let (clLengths, br) ← readCLCodeLengths br (.replicate 19 0) 0 numCodeLen
  let clTree ← HuffTree.fromLengths clLengths 7
  let totalCodes := numLitLen + numDist
  let (codeLengths, br) ← decodeCLSymbols clTree br (.replicate totalCodes 0) 0 totalCodes
  let litLenLengths := codeLengths.extract 0 numLitLen
  let distLengths := codeLengths.extract numLitLen totalCodes
  let _ ← HuffTree.validateLengths litLenLengths 15
  let _ ← HuffTree.validateLengths distLengths 15
  return (litLenLengths, distLengths, br)

/-- Tree-free block loop (mirrors `inflateLoop`): fixed and dynamic Huffman blocks
    decode through the canonical tree-free decoder; stored blocks unchanged. The
    `bitPos`-advance and out-of-range guards supply the well-founded measure (same
    as `inflateLoop`). -/
def inflateLoopTreeFree (br : BitReader) (output : ByteArray) (maxOut dataSize : Nat) :
    Except String (ByteArray × Nat) := do
  let (bfinal, br₁) ← br.readBits 1
  let (btype, br₂) ← br₁.readBits 2
  let (output', br') ← match btype with
    | 0 => Inflate.decodeStored br₂ output maxOut
    | 1 => decodeHuffmanFastBufFixed br₂ output maxOut
    | 2 => do
      let (litLens, distLens, br₃) ← decodeDynamicLengthsOnly br₂
      InflateBuf.decodeHuffmanFastBufTreeFree br₃ output litLens distLens maxOut
    | _ => throw s!"Inflate: reserved block type {btype}"
  if bfinal == 1 then
    return (output', br'.alignToByte.pos)
  else
    if _h₁ : br'.bitPos ≤ br.bitPos then
      throw "Inflate: no progress in inflate loop"
    else if _h₂ : dataSize * 8 < br'.bitPos then
      throw "Inflate: bit position out of range"
    else
      inflateLoopTreeFree br' output' maxOut dataSize
  termination_by dataSize * 8 - br.bitPos
  decreasing_by all_goals omega

/-- Inflate a raw DEFLATE stream starting at byte offset `startPos`, returning the
    decompressed data and the byte-aligned position after the last block. **This is
    the production decoder**: a tree-free canonical Huffman decode that builds no
    Huffman tree anywhere on the decode path (the loop reads `fixedLit/DistLengths`
    directly and decodes through the canonical table + `walkCanonical` fallback).
    Proven accept-set equal to the verified reference `inflateRawReference`
    (`Zip.Spec.InflateTreeFreeCorrect.inflateRaw_ok_iff_reference`), so every downstream
    correctness theorem transfers. `maxOutputSize` (default 1 GiB) caps output;
    `sizeHint` pre-reserves capacity (computationally inert — see
    `inflateRaw_sizeHint_eq`). -/
def inflateRaw (data : ByteArray) (startPos : Nat := 0)
    (maxOutputSize : Nat := 1024 * 1024 * 1024) (sizeHint : Nat := 0) :
    Except String (ByteArray × Nat) := do
  let br : BitReader := { data, pos := startPos, bitOff := 0 }
  inflateLoopTreeFree br (ByteArray.emptyWithCapacity sizeHint) maxOutputSize data.size

/-- Inflate a raw DEFLATE stream (whole buffer). **The production decoder** — the
    tree-free counterpart of the reference `inflateReference`, proven accept-set
    equal to it (`Zip.Spec.InflateTreeFreeCorrect.inflate_ok_iff_reference`). -/
def inflate (data : ByteArray) (maxOutputSize : Nat := 1024 * 1024 * 1024)
    (sizeHint : Nat := 0) :
    Except String ByteArray := do
  let (output, _) ← inflateRaw data 0 maxOutputSize sizeHint
  return output

/-- The output capacity hint is computationally inert (`ByteArray.emptyWithCapacity n`
    reduces to `{ data := Array.empty }` for every `n`). -/
@[simp] theorem inflateRaw_sizeHint_eq (data : ByteArray)
    (startPos maxOutputSize sizeHint : Nat) :
    inflateRaw data startPos maxOutputSize sizeHint = inflateRaw data startPos maxOutputSize :=
  rfl

/-- `inflate` with any `sizeHint` equals it with the default `0`. -/
@[simp] theorem inflate_sizeHint_eq (data : ByteArray) (maxOutputSize sizeHint : Nat) :
    inflate data maxOutputSize sizeHint = inflate data maxOutputSize :=
  rfl

end Inflate
end Zip.Native
