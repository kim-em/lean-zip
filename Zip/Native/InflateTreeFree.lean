import Zip.Native.Inflate

/-!
# Tree-free canonical decode — the production DEFLATE decoder

This file defines the **production** decoders `Inflate.inflate` / `inflateRaw`: a
DEFLATE Huffman decode that builds **no** Huffman tree. The fast ≤11-bit codes go
through the canonical 11-bit table (`buildTableCanonicalFast`), and the rare >11-bit
codes go through libdeflate-style **subtables** (`subLookup`: two masked loads, no
per-bit boxed accumulation) — never a tree walk, never a boxed scan. This skips the
`fromLengths`/`insertLoop` build entirely (the ~7% decode win). The boxed per-bit
`walkCanonical` survives only as the proof-side reference `subLookup` is verified
against (`subLookup_ok_iff_walkCanonical`).

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

/-- Canonical long-code decode tables (for codes longer than the 11-bit window).

    The first four fields are the counting-sort reference structure the verified
    `walkCanonical` reads: `count[len]` codes of each length, `firstCode[len]` the
    first canonical code of that length, `firstIndex[len]` the offset into
    `symbols` (symbols sorted by `(length, symbol)`).

    The last field is the flat `subs` array of the libdeflate-style **subtables**
    the production `subLookup` reads. There is **no** separate root map: a long
    prefix's subtable-block offset is stored *inline* in the root fast table's
    sentinel slot — `packEntry (off + 1) 0` (the length stays `0`, so the fast path
    still misses and falls through; the biased `off + 1` rides in the symbol field,
    `0` meaning "no long code with this prefix"). So a long codeword is resolved by
    reading the root table entry `subLookup` was handed anyway (its symbol field
    gives the block offset) and one masked load into `subs` — no per-bit boxed
    accumulation, and no second `2^fastBits` array built per block. In the context
    `subLookup` is actually called (the root table missed, so any codeword present is
    longer than `fastBits`), it is proven to agree with `walkCanonical`
    (`subLookup_ok_iff_walkCanonical`), so the subtable is a verified drop-in for the
    boxed fallback. (As standalone functions the two differ: `walkCanonical` also
    resolves short codes, which never reach this path.) -/
structure LongDecode where
  count : Array Nat
  firstCode : Array Nat
  firstIndex : Array Nat
  symbols : Array UInt16
  subs : Array UInt32

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

/-- Total number of codewords longer than `fastBits` (`∑_{fastBits < len ≤ maxBits}
    count[len]`). The `subs` array is sized `2^(maxBits - fastBits)` times this: every
    long code owns one `2^(maxBits - fastBits)`-entry subtable block at most, so this
    over-allocates only when several long codes share a `fastBits`-bit prefix (a
    block is one-per-prefix). One pass over the small `count` array. -/
def countLongCodes (count : Array Nat) (maxBits : Nat) : Nat :=
  go count maxBits (fastBits + 1) 0
where
  go (count : Array Nat) (maxBits len acc : Nat) : Nat :=
    if len > maxBits then acc
    else go count maxBits (len + 1) (acc + count[len]!)
  termination_by maxBits + 1 - len

/-- The libdeflate-style **inline** subtable fill (mirrors `buildCanonicalLoop`'s
    `nextCode` threading, but for codes *longer* than `fastBits`). For each symbol
    from `start`, look up its canonical code `c = nextCode[len]` (advancing
    `nextCode[len]`), and — for `fastBits < len ≤ maxBits` — resolve which subtable
    block its `fastBits`-bit prefix owns, then fill the `2^(maxBits - len)` sub-slots
    the code owns in `subs` (`fillSlots`, stride `2^(len - fastBits)`, from the code's
    residual bits).

    The block offset is stored **inline in the root fast table `root`**: a long
    prefix's slot is a fast-table sentinel (`packEntry 0 0`, length `0`); the first
    time the prefix appears we overwrite it with `packEntry (off + 1) 0` (length
    still `0`, so the fast path keeps missing; the biased `off + 1` block offset
    rides in the symbol field), allocating a fresh `2^(maxBits - fastBits)`-entry
    block via the discovery-order counter `nextBlock`. On a repeat sighting the slot
    already holds `off + 1` (its symbol field is non-zero), so we reuse it — no
    second `2^fastBits` array. Codes `≤ fastBits` and `len = 0` are skipped. -/
def buildSubLoop (lengths : Array UInt8) (nextCode : Array UInt32) (maxBits start : Nat)
    (root subs : Array UInt32) (nextBlock : Nat) : Array UInt32 × Array UInt32 :=
  if h : start < lengths.size then
    let len := lengths[start]
    if hlen : 0 < len.toNat ∧ len.toNat < nextCode.size then
      let c := nextCode[len.toNat]'hlen.2
      let nextCode' := nextCode.set! len.toNat (c + 1)
      if fastBits < len.toNat then
        let rev := bitReverse c.toNat len.toNat 0
        let p := rev % (2 ^ fastBits)
        let subBase := rev / (2 ^ fastBits)
        let seenSym := (unpackSym root[p]!).toNat
        let off := if seenSym == 0 then nextBlock * (2 ^ (maxBits - fastBits)) else seenSym - 1
        let root' := if seenSym == 0 then root.set! p (packEntry (off + 1).toUInt16 0) else root
        let nextBlock' := if seenSym == 0 then nextBlock + 1 else nextBlock
        let stride := 2 ^ (len.toNat - fastBits)
        let cnt := 2 ^ (maxBits - len.toNat)
        let entry := packEntry start.toUInt16 len
        let subs' := fillSlots subs (off + subBase) stride cnt entry
        buildSubLoop lengths nextCode' maxBits (start + 1) root' subs' nextBlock'
      else
        buildSubLoop lengths nextCode' maxBits (start + 1) root subs nextBlock
    else
      buildSubLoop lengths nextCode maxBits (start + 1) root subs nextBlock
  else (root, subs)
termination_by lengths.size - start

/-- Augment a prebuilt root fast table with inline subtable-block offsets and build
    the flat `subs` array, sharing the precomputed histogram. `root` (the fast
    table's packed array, size `2^fastBits`) is written in place — offsets ride in
    the sentinel slots of long prefixes; `subs` is fresh (size
    `2^(maxBits - fastBits) · countLongCodes`). No new `2^fastBits` array. -/
def augmentSubTables (root : Array UInt32) (lengths : Array UInt8) (count : Array Nat)
    (maxBits : Nat) : Array UInt32 × Array UInt32 :=
  let nextCode := nextCodesFast count maxBits
  let numLong := countLongCodes count maxBits
  buildSubLoop lengths nextCode maxBits 0 root
    (Array.replicate (2 ^ (maxBits - fastBits) * numLong) (packEntry 0 0)) 0

/-- The canonical long-code **reference** structure (read only by the proof-side
    `walkCanonical`): `firstCode` is the canonical first-code-per-length recurrence
    (RFC 1951 §3.2.2), exactly `Huffman.Spec.nextCodes`; `firstIndex`/`symbols` are
    the prefix-sum and counting-sort over the code lengths. `subs` is left empty here
    — the production `subs`/inline offsets are built by `buildTreeFreeWithCount`
    (which also augments the fast table); `walkCanonical` never reads `subs`. -/
def buildLongDecode (lengths : Array UInt8) (maxBits : Nat) : LongDecode :=
  let count := countLengthsFast lengths maxBits
  let firstCode := Huffman.Spec.nextCodes count maxBits
  let firstIndex := buildFirstIndex count maxBits
  let total := firstIndex[maxBits]! + count[maxBits]!
  let symbols := buildSymbols lengths maxBits total firstIndex
  { count, firstCode, firstIndex, symbols, subs := #[] }

/-- Does any codeword exceed the `fastBits`-wide fast table — i.e. can the long-code
    subtable path ever fire? `count[len] > 0` for some `fastBits < len ≤ maxBits`.
    When this is `false`, every codeword resolves in the fast table, so the long-code
    counting sort (`buildSymbols`) and the subtable build are dead work and are
    skipped. One pass over the small `count` array. -/
def hasLongCode (count : Array Nat) (maxBits : Nat) : Bool :=
  go count maxBits (fastBits + 1)
where
  go (count : Array Nat) (maxBits len : Nat) : Bool :=
    if len > maxBits then false
    else if count[len]! > 0 then true
    else go count maxBits (len + 1)
  termination_by maxBits + 1 - len

/-- Build the fast root table *and* the tree-free long-code structures in one shot,
    sharing the histogram. The fast table (`buildTableCanonicalFastWithCount`) is
    augmented in place with inline subtable offsets (`augmentSubTables`); the returned
    `LongDecode` carries the reference fields plus the flat `subs`. When no codeword
    exceeds `fastBits` (`hasLongCode` false) the fast table is returned untouched and
    `subs`/`symbols` are empty (the subtable path is dead). Returns the augmented
    table and the long-code structure together so the decode loop and the fallback
    share one build. -/
def buildTreeFreeWithCount (lengths : Array UInt8) (count : Array Nat) (maxBits : Nat) :
    DecodeTable × LongDecode :=
  let table := buildTableCanonicalFastWithCount lengths count maxBits
  if hasLongCode count maxBits then
    let (root, subs) := augmentSubTables table.packed lengths count maxBits
    -- only `subs` (and the inline offsets in `root`) feed the runtime `subLookup`;
    -- the `firstCode`/`firstIndex`/`symbols` reference fields are dead here (they
    -- belong to the proof-side `walkCanonical`), so leave them empty to avoid the
    -- counting-sort / prefix-sum work per block.
    ({ packed := root },
      { count, firstCode := #[], firstIndex := #[], symbols := #[], subs })
  else
    (table, { count, firstCode := #[], firstIndex := #[], symbols := #[], subs := #[] })

/-- `buildSubLoop` preserves the size of the root table it augments (every write is
    an in-place `set!`). -/
theorem buildSubLoop_size (lengths : Array UInt8) (nextCode : Array UInt32)
    (maxBits start : Nat) (root subs : Array UInt32) (nextBlock : Nat) :
    (buildSubLoop lengths nextCode maxBits start root subs nextBlock).1.size = root.size := by
  unfold buildSubLoop
  split
  · dsimp only []
    split
    · split
      · rw [buildSubLoop_size]; split
        · rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
        · rfl
      · rw [buildSubLoop_size]
    · rw [buildSubLoop_size]
  · rfl
termination_by lengths.size - start

/-- The `buildTreeFreeWithCount` root table is the `2^fastBits`-entry fast table
    (augmented in place, so size-preserving). -/
theorem buildTreeFreeWithCount_size (lengths : Array UInt8) (count : Array Nat)
    (maxBits : Nat) :
    (buildTreeFreeWithCount lengths count maxBits).1.packed.size = 2 ^ fastBits := by
  unfold buildTreeFreeWithCount
  split
  · show (augmentSubTables _ lengths count maxBits).1.size = _
    unfold augmentSubTables
    rw [buildSubLoop_size, buildTableCanonicalFastWithCount_size]
  · exact buildTableCanonicalFastWithCount_size lengths count maxBits

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

/-- libdeflate-style inline-subtable long-code resolve. The root fast table entry at
    the `fastBits`-bit prefix (which `decodeSymCanon` already read to miss the fast
    path) carries the prefix's subtable-block offset in its symbol field
    (`packEntry (off + 1) 0`); one masked load into `subs` (indexed by the next
    `maxBits - fastBits` bits) then reads the packed `(sym, fullLen)` — no per-bit
    boxed accumulation, no second `2^fastBits` array. A real short code with too few
    buffered bits (`unpackLen ≠ 0`, the `len > cnt` fast-path miss) or a genuine
    no-code prefix (symbol field `0`) or a sentinel-`0` sub-slot is the "invalid
    code" error; too few bits for the resolved length is "unexpected end of input".
    In the fallback context it is called from (root table missed → any codeword is
    long), proven to return exactly what the boxed `walkCanonical` returns
    (`subLookup_ok_iff_walkCanonical`). -/
@[inline] def subLookup (ld : LongDecode) (table : DecodeTable) (maxBits : Nat)
    (bitBuf : UInt64) (cnt : Nat) : Except String (UInt16 × UInt64 × Nat × Nat) :=
  let p := (bitBuf &&& 0x7FF).toNat
  let rootE := table.entryAt p
  if unpackLen rootE ≠ 0 then .error "Inflate: invalid Huffman code"
  else
    let off1 := (unpackSym rootE).toNat
    if off1 == 0 then .error "Inflate: invalid Huffman code"
    else
      let off := off1 - 1
      let subIdx := ((bitBuf >>> (fastBits : Nat).toUInt64)
        &&& (2 ^ (maxBits - fastBits) - 1 : Nat).toUInt64).toNat
      let e := ld.subs[off + subIdx]!
      let len := (unpackLen e).toNat
      if len == 0 then .error "Inflate: invalid Huffman code"
      else if len > cnt then .error "BitReader: unexpected end of input"
      else .ok (unpackSym e, bitBuf >>> len.toUInt64, cnt - len, len)

/-- `decodeSym` with the tree-free long-code fallback: the ≤`fastBits` root table
    hit as before, the >`fastBits` codes resolved by the boxing-free inline-subtable
    `subLookup` (retiring the boxed per-bit `walkCanonical`, which survives only as
    the proof-side reference `subLookup` is verified against). -/
@[inline] def decodeSymCanon (ld : LongDecode) (table : DecodeTable) (maxBits : Nat)
    (bitBuf : UInt64) (cnt : Nat) : Except String (UInt16 × UInt64 × Nat × Nat) :=
  let idx := (bitBuf &&& 0x7FF).toNat
  let e := table.entryAt idx
  let len := (unpackLen e).toNat
  if len == 0 || len > cnt then subLookup ld table maxBits bitBuf cnt
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
    (hsz : data.size < USize.size)
    (hlp : litTable.packed.size = 2 ^ HuffTree.fastBits) (output : ByteArray) :
    Except String (ByteArray × USize × UInt64 × USize) := do
  if hrc : cnt ≤ 56 ∧ pos < data.size.toUSize then
    goTreeFreeU litTable distTable litLD distLD maxBits data maxOut
      (pos + 1)
      (bitBuf ||| ((data.uget pos (by
          have h := USize.lt_iff_toNat_lt.mp hrc.2
          rwa [toUSize_toNat_of_lt hsz] at h)).toUInt64 <<< cnt.toUInt64))
      (cnt + 8) hsz hlp output
  else
  let e := litTable.entryAtU (bitBuf &&& 0x7FF).toUSize
    (by rw [hlp]; exact HuffTree.and_0x7FF_toUSize_toNat_lt bitBuf)
  if hlit : HuffTree.unpackLen e ≠ 0
      ∧ (HuffTree.unpackLen e).toUSize ≤ cnt
      ∧ HuffTree.unpackSym e < 256 then
    if output.size ≥ maxOut then throw "Inflate: output exceeds maximum size"
    else
      goTreeFreeU litTable distTable litLD distLD maxBits data maxOut pos
        (bitBuf >>> (HuffTree.unpackLen e).toUInt64)
        (cnt - (HuffTree.unpackLen e).toUSize)
        hsz hlp
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
          cnt'.toUSize hsz hlp (output.push sym.toUInt8)
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
                cnt4.toUSize hsz hlp out
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

/-- Tree-free wide-buffer block decode from prebuilt tables: runs the tree-free
    loop (no Huffman tree) over the already-constructed fast/long decode tables.
    Runs the unboxed `goTreeFreeU` when the input is addressable, else the boxed
    `goTreeFree` — mirroring `goFusedPDispatch`. Factored out of
    `decodeHuffmanFastBufTreeFree` so the fixed-Huffman path can pass the
    compile-time-constant fixed tables instead of rebuilding them every block. -/
def decodeHuffmanFastBufTables (br : BitReader) (output : ByteArray)
    (litTable distTable : DecodeTable) (litLD distLD : LongDecode) (maxOut : Nat)
    (hlp : litTable.packed.size = 2 ^ HuffTree.fastBits) :
    Except String (ByteArray × BitReader) := do
  let (pos, bitBuf, cnt) := refill br.data br.pos 0 0
  let bitBuf := bitBuf >>> br.bitOff.toUInt64
  let cnt := cnt - br.bitOff
  let (out, pos', bitBuf', cnt') ←
    if hsz : br.data.size.toUSize.toNat = br.data.size then
      Except.map (fun x => (x.1, x.2.1.toNat, x.2.2.1, x.2.2.2.toNat))
        (goTreeFreeU litTable distTable litLD distLD 15 br.data maxOut
          pos.toUSize bitBuf cnt.toUSize (by rw [← hsz]; exact USize.toNat_lt_two_pow_numBits _)
          hlp output)
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
  let litTF := HuffTree.buildTreeFreeWithCount litLengths litCount 15
  let distTF := HuffTree.buildTreeFreeWithCount distLengths distCount 15
  decodeHuffmanFastBufTables br output litTF.1 distTF.1 litTF.2 distTF.2 maxOut
    (HuffTree.buildTreeFreeWithCount_size litLengths litCount 15)

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

/-- The fixed lit/length fast table + long-code structure (RFC 1951 §3.2.6), built
    once. Fixed lit codes are ≤ 9 bits, so `hasLongCode` is false: the table is the
    plain fast table and `subs` is empty (the subtable path is dead). -/
def fixedLitTF : DecodeTable × LongDecode :=
  HuffTree.buildTreeFreeWithCount fixedLitLengths fixedLitCount 15

/-- The fixed distance fast table + long-code structure (RFC 1951 §3.2.6), built once. -/
def fixedDistTF : DecodeTable × LongDecode :=
  HuffTree.buildTreeFreeWithCount fixedDistLengths fixedDistCount 15

/-- Fixed-Huffman block decode over the compile-time-constant fixed tables — no
    per-block table build. Equal to
    `decodeHuffmanFastBufTreeFree br output fixedLitLengths fixedDistLengths maxOut`
    (`decodeHuffmanFastBufFixed_eq`). -/
def decodeHuffmanFastBufFixed (br : BitReader) (output : ByteArray) (maxOut : Nat) :
    Except String (ByteArray × BitReader) :=
  InflateBuf.decodeHuffmanFastBufTables br output fixedLitTF.1 fixedDistTF.1
    fixedLitTF.2 fixedDistTF.2 maxOut
    (HuffTree.buildTreeFreeWithCount_size fixedLitLengths fixedLitCount 15)

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
