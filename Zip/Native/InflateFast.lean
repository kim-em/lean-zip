import Zip.Native.InflateTreeFree
import Zip.Native.Wide

/-!
# Write-once cursor decode (fastloop spike — issue #2799)

**This is a benchmark-first spike.** It measures the ceiling of the
write-once-cursor architecture from issue #2799: instead of `output.push`ing
each literal (an out-of-line `lean_byte_array_push` with a capacity check, size
tag, and refcount that threads through the loop-carried recurrence), the decode
pre-extends the output buffer to its final size **once** and writes each literal
/ match at a cursor into that already-allocated space.

`goCur` is byte-for-byte `InflateBuf.goTreeFreeU` with the output side swapped:

  * literal write `output.push b` → `output.set!` at the `outPos` cursor,
  * back-reference `Inflate.copyLoop` (append) → an inline wide copy for
    non-overlapping matches up to eight bytes, with `ByteArray.copyWithinAt` as
    the general fallback (in-place, no realloc),

and the logical output length `output.size` (used by the distance / max-size
checks) → the `outPos` cursor. Everything on the **input** side — the `uget`
wide refill, the packed-table literal fast path, the `walkCanonical` long-code
fallback — is identical, so an A/B of `inflateFast` against the production
`Inflate.inflate` isolates exactly the per-symbol output-write cost (#2799's
"remaining half").

The equivalence to the reference decoder is now **proven**: both cursor loops
are `Zip.Spec.InflateFastCorrect.inflateFast_eq` / `inflateFastU_eq`, so on a
valid stream at the exact size they return exactly `Inflate.inflate`'s bytes.
The production dispatch `inflateSized` (below) uses the verified `uset` fastloop
when the caller supplies an exact, bounded size and falls back to `inflate`
otherwise; it is now wired into ZIP extraction (`Zip.Archive`, size from the
central-directory `uncompressedSize`), so `import Zip` does surface it. The A/B
driver `inflate-profile decode-fast` and the `inflateFast = inflate` conformance
test remain.

The fastloop is valid only on the **exact-size path**: the caller must pass a
`sizeHint` equal to the true decompressed length (the archive workloads: gzip
ISIZE, ZIP sizes). It pre-extends to `sizeHint`, rejects `sizeHint >
maxOutputSize` up front (the fastloop drops the per-symbol max-size check under
the margin), and errors unless the stream decodes to exactly `sizeHint` — the
exact-size contract is executable, not silently truncated, so a wrong hint is
caught and `inflateSized` falls back. The unknown-size chunked path is future
work in the tracking issue.
-/

namespace ByteArray

/-- Zero-filled `ByteArray` of size `n` (the pre-extended output buffer). The
    reference body `ByteArray.mk (Array.replicate n 0)` is the trusted
    specification of the `@[extern]`; the C allocates an `n`-byte scalar array
    and `memset`s it to zero. -/
@[extern "lean_zip_byte_array_presize"]
def presize (n : Nat) : ByteArray := ByteArray.mk (Array.replicate n 0)

/-- Reference model for `copyWithinAt`: the LZ77 forward-propagating copy at a
    cursor. Writes byte `destOff + k` as `a[destOff - distance + (k % distance)]`
    for `k ∈ [0, len)`, i.e. `a[destOff + k] = a[destOff + k - distance]`. Uses
    `set!` / `get!` so it is total (out-of-range indices clamp to a no-op), the
    same totality posture as `Inflate.copyLoopGo`. -/
def copyWithinAtGo (a : ByteArray) (destOff distance k len : Nat) : ByteArray :=
  if k < len then
    copyWithinAtGo (a.set! (destOff + k) (a.get! (destOff - distance + k % distance)))
      destOff distance (k + 1) len
  else a
termination_by len - k

/-- In-place LZ77 back-reference copy at a cursor: append-free analogue of
    `ByteArray.copyWithin` / `extendWithin` that writes `len` bytes starting at
    `destOff` (reading the periodic `distance`-byte window ending at `destOff`)
    into `a`'s already-allocated space, never growing `a`. The reference body is
    the trusted specification of the `@[extern]`; the C does it as a `memcpy`
    (non-overlapping) or a forward doubling smear (overlapping / RLE), mirroring
    `extend_within_ffi.c`. The explicit degenerate guard (`distance = 0`,
    `distance > destOff` so the window would underflow, or a write past `a.size`)
    returns `a` unchanged — matching the C exactly (`inflate_fast_ffi.c` returns
    `a` on the same predicates), so the extern agrees with the body on *every*
    input, not only the valid decoder path. Under the guard
    (`1 ≤ distance ≤ destOff`, `destOff + len ≤ a.size`) `copyWithinAtGo` reads
    only the fixed window `[destOff - distance, destOff)` (all indices below every
    written position), so it equals the C's forward smear byte for byte. -/
@[extern "lean_zip_byte_array_copy_within_at"]
def copyWithinAt (a : ByteArray) (destOff distance len : Nat) : ByteArray :=
  if distance = 0 ∨ distance > destOff ∨ destOff + len > a.size then a
  else copyWithinAtGo a destOff distance 0 len

/-- `USize` entry point for `copyWithinAt`. The reference body delegates after
    conversion; the native implementation receives all three offsets as raw
    machine words, avoiding `Nat` boxes in the decode hot loop. -/
@[extern "lean_zip_byte_array_copy_within_at_u"]
def copyWithinAtU (a : ByteArray) (destOff distance len : USize) : ByteArray :=
  a.copyWithinAt destOff.toNat distance.toNat len.toNat

/-- Copy a non-overlapping match of at most eight bytes with one wide load/store.
    The destination word is blended into the bytes above `len`, so the wide
    store changes exactly the logical match bytes. The `1 ≤ len ≤ 8`
    hypotheses are load-bearing at runtime: `UInt64` shifts are modulo 64, so
    an out-of-range length would not make this helper safely clamp. Limiting
    this path to one exact store preserves the fastloop's whole-buffer
    invariant; longer and overlapping matches use `copyWithinAtU`. -/
@[inline] def copyWithinAtShort (a : ByteArray) (destOff : USize)
    (distance len : USize) (_hdistance : 8 ≤ distance) (_hlenpos : 0 < len) (_hlen : len ≤ 8)
    (hwindow : distance ≤ destOff) (hroom : destOff.toNat + 8 ≤ a.size) : ByteArray :=
  let srcOff := destOff - distance
  let src := a.ugetUInt64LE srcOff (by
    rw [USize.toNat_sub_of_le _ _ hwindow]
    omega)
  let dst := a.ugetUInt64LE destOff hroom
  let mask := (0xffffffffffffffff : UInt64) >>> ((8 - len).toUInt64 <<< 3)
  a.usetUInt64LE destOff ((src &&& mask) ||| (dst &&& ~~~mask)) hroom

end ByteArray

namespace Zip.Native
open ZipCommon (BitReader)

namespace InflateBuf
open Zip.Native.HuffTree (DecodeTable LongDecode decodeSymCanon)

/-- Read `n` buffered bits while keeping the count and extracted value in
    native machine words. The extracted value is a `UInt16`, so callers must
    ensure `n ≤ 16`; the DEFLATE length/distance call sites use at most 13 bits.
    Callers only convert the remaining count when entering the Nat-based
    long-code decoder. -/
@[inline] def takeBitsU (bitBuf : UInt64) (cnt n : USize) :
    Except String (UInt16 × UInt64 × USize) :=
  if n > cnt then .error "BitReader: unexpected end of input"
  else
    let v := (bitBuf &&& ((1 <<< n.toUInt64) - 1)).toUInt16
    .ok (v, bitBuf >>> n.toUInt64, cnt - n)

/-- Runtime-side table fact needed to make the masked-store length contract
    explicit in `goCurU`'s definition. -/
private theorem lengthBase_pos (idx : Nat) (h : idx < Inflate.lengthBase.size) :
    0 < Inflate.lengthBase[idx].toNat := by
  have hkey : ∀ k : Fin Inflate.lengthBase.size, 0 < Inflate.lengthBase[k.val]!.toNat := by
    decide
  have hk := hkey ⟨idx, h⟩
  rwa [getElem!_pos Inflate.lengthBase idx h] at hk

/-- A positive `UInt16` base remains positive after native-width addition. -/
private theorem uint16_add_usize_pos (base extra : UInt16) (hbase : 0 < base.toNat) :
    0 < base.toUSize + extra.toUSize := by
  rw [USize.lt_iff_toNat_lt]
  rw [USize.toNat_add, UInt16.toNat_toUSize, UInt16.toNat_toUSize,
    Nat.mod_eq_of_lt (by
      have hb := UInt16.toNat_lt base
      have he := UInt16.toNat_lt extra
      exact Nat.lt_of_lt_of_le (by omega) USize.le_size)]
  exact Nat.lt_of_lt_of_le hbase (Nat.le_add_right ..)

set_option maxRecDepth 4096 in
/-- Write-once cursor copy of `goTreeFreeU` (issue #2799 spike). Identical input
    handling; the output side writes at the `outPos` cursor into the
    pre-extended `output` via `set!` / `copyWithinAt` instead of `push` /
    `copyLoop`. Returns the final cursor alongside the (unchanged-size) buffer.
    Well-founded on the same measure as `goTreeFreeU`. -/
def goCur (litTable distTable : DecodeTable) (litLD distLD : LongDecode)
    (maxBits : Nat) (data : ByteArray) (maxOut : Nat)
    (pos : USize) (bitBuf : UInt64) (cnt : USize)
    (hsz : data.size < USize.size)
    (hlp : litTable.packed.size = 2 ^ HuffTree.fastBits)
    (output : ByteArray) (outPos : USize) :
    Except String (ByteArray × USize × USize × UInt64 × USize) := do
  if hrc : cnt ≤ 56 ∧ pos < data.size.toUSize then
    goCur litTable distTable litLD distLD maxBits data maxOut
      (pos + 1)
      (bitBuf ||| ((data.uget pos (by
          have h := USize.lt_iff_toNat_lt.mp hrc.2
          rwa [toUSize_toNat_of_lt hsz] at h)).toUInt64 <<< cnt.toUInt64))
      (cnt + 8) hsz hlp output outPos
  else
  let e := litTable.entryAtU (bitBuf &&& 0x7FF).toUSize
    (by rw [hlp]; exact HuffTree.and_0x7FF_toUSize_toNat_lt bitBuf)
  if hlit : HuffTree.unpackLen e ≠ 0
      ∧ (HuffTree.unpackLen e).toUSize ≤ cnt
      ∧ HuffTree.unpackSym e < 256 then
    if outPos.toNat ≥ maxOut then throw "Inflate: output exceeds maximum size"
    else
      goCur litTable distTable litLD distLD maxBits data maxOut pos
        (bitBuf >>> (HuffTree.unpackLen e).toUInt64)
        (cnt - (HuffTree.unpackLen e).toUSize)
        hsz hlp
        (output.set! outPos.toNat (HuffTree.unpackSym e).toUInt8) (outPos + 1)
  else
  let cnt0 := cnt.toNat
  match decodeSymCanon litLD litTable maxBits bitBuf cnt.toNat with
  | .error e => .error e
  | .ok (sym, bitBuf, cnt', _used) =>
    if sym < 256 then
      if outPos.toNat ≥ maxOut then throw "Inflate: output exceeds maximum size"
      else if hnp : cnt0 ≤ cnt' then throw "Inflate: no progress in Huffman decode"
      else
        goCur litTable distTable litLD distLD maxBits data maxOut pos bitBuf
          cnt'.toUSize hsz hlp
          (output.set! outPos.toNat sym.toUInt8) (outPos + 1)
    else if sym == 256 then .ok (output, outPos, pos, bitBuf, cnt'.toUSize)
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
            else if hds : distance > outPos.toNat then
              throw s!"Inflate: distance {distance} exceeds output size {outPos.toNat}"
            else if outPos.toNat + length > maxOut then throw "Inflate: output exceeds maximum size"
            else if hnp : cnt0 ≤ cnt4 then throw "Inflate: no progress in Huffman decode"
            else
              let out := output.copyWithinAt outPos.toNat distance length
              goCur litTable distTable litLD distLD maxBits data maxOut pos bitBuf
                cnt4.toUSize hsz hlp out (outPos + length.toUSize)
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

set_option maxRecDepth 4096 in
/-- Branch-free fastloop variant of `goCur` (the actual #2799 shape), retained
    as the byte-refill reference twin used by the correctness proof for `goCurUW`.
    A single
    per-symbol margin guard `outPos + 299 ≤ output.size` gates the hot body, in
    which literal writes are proven-bounds `uset` (bound discharged from the
    margin, no per-literal bounds check) and the per-literal max-size check is
    gone (the margin implies it, given `output.size ≤ maxOut`). Non-overlapping
    matches of at most eight bytes use one inline masked wide store; general
    matches use the total `copyWithinAt`. When the margin fails — only in the
    final <299 output bytes — it delegates the rest of the block to the
    bounds-checked `goCur` (same buffer, no copy). This isolates the
    *branch-elision* increment over `goCur`. Same termination measure. -/
def goCurU (litTable distTable : DecodeTable) (litLD distLD : LongDecode)
    (maxBits : Nat) (data : ByteArray) (maxOut : Nat)
    (pos : USize) (bitBuf : UInt64) (cnt : USize)
    (hsz : data.size < USize.size)
    (hlp : litTable.packed.size = 2 ^ HuffTree.fastBits)
    (output : ByteArray) (outPos : USize) :
    Except String (ByteArray × USize × USize × UInt64 × USize) := do
  if hrc : cnt ≤ 56 ∧ pos < data.size.toUSize then
    goCurU litTable distTable litLD distLD maxBits data maxOut
      (pos + 1)
      (bitBuf ||| ((data.uget pos (by
          have h := USize.lt_iff_toNat_lt.mp hrc.2
          rwa [toUSize_toNat_of_lt hsz] at h)).toUInt64 <<< cnt.toUInt64))
      (cnt + 8) hsz hlp output outPos
  else if hm : outPos.toNat + 299 ≤ output.size then
    let e := litTable.entryAtU (bitBuf &&& 0x7FF).toUSize
      (by rw [hlp]; exact HuffTree.and_0x7FF_toUSize_toNat_lt bitBuf)
    if hlit : HuffTree.unpackLen e ≠ 0
        ∧ (HuffTree.unpackLen e).toUSize ≤ cnt
        ∧ HuffTree.unpackSym e < 256 then
      goCurU litTable distTable litLD distLD maxBits data maxOut pos
        (bitBuf >>> (HuffTree.unpackLen e).toUInt64)
        (cnt - (HuffTree.unpackLen e).toUSize)
        hsz hlp
        (output.uset outPos (HuffTree.unpackSym e).toUInt8 (by omega)) (outPos + 1)
    else
    let cnt0 := cnt.toNat
    match decodeSymCanon litLD litTable maxBits bitBuf cnt.toNat with
    | .error e => .error e
    | .ok (sym, bitBuf, cnt', _used) =>
      if sym < 256 then
        if hnp : cnt0 ≤ cnt' then throw "Inflate: no progress in Huffman decode"
        else
          goCurU litTable distTable litLD distLD maxBits data maxOut pos bitBuf
            cnt'.toUSize hsz hlp
            (output.uset outPos sym.toUInt8 (by omega)) (outPos + 1)
      else if sym == 256 then .ok (output, outPos, pos, bitBuf, cnt'.toUSize)
      else
      let idx := sym.toUSize - 257
      if h : idx ≥ 29 then throw s!"Inflate: invalid length code {sym}"
      else
        let base := Inflate.lengthBase.uget idx (by
          rw [Inflate.lengthBase_size]
          simpa using USize.lt_iff_toNat_lt.mp (USize.not_le.mp h))
        let extra := Inflate.lengthExtra.uget idx (by
          rw [Inflate.lengthExtra_size]
          simpa using USize.lt_iff_toNat_lt.mp (USize.not_le.mp h))
        let (extraBits, bitBuf, cnt'') ← takeBitsU bitBuf cnt'.toUSize extra.toUSize
        let length := base.toUSize + extraBits.toUSize
        match decodeSymCanon distLD distTable maxBits bitBuf cnt''.toNat with
        | .error e => .error e
        | .ok (distSym, bitBuf, cnt3, _dused) =>
          let dIdx := distSym.toUSize
          if hd : dIdx ≥ 30 then throw s!"Inflate: invalid distance code {distSym}"
          else
            let dBase := Inflate.distBase.uget dIdx (by
              rw [Inflate.distBase_size]
              simpa using USize.lt_iff_toNat_lt.mp (USize.not_le.mp hd))
            let dExtra := Inflate.distExtra.uget dIdx (by
              rw [Inflate.distExtra_size]
              simpa using USize.lt_iff_toNat_lt.mp (USize.not_le.mp hd))
            let (dExtraBits, bitBuf, cnt4) ← takeBitsU bitBuf cnt3.toUSize dExtra.toUSize
            let distance := dBase.toUSize + dExtraBits.toUSize
            if hz : distance = 0 then throw s!"Inflate: zero back-reference distance"
            else if hds : distance > outPos then
              throw s!"Inflate: distance {distance.toNat} exceeds output size {outPos.toNat}"
            else if hlen : length > 258 then throw "Inflate: length exceeds 258"
            else if hnp : cnt0 ≤ cnt4.toNat then throw "Inflate: no progress in Huffman decode"
            else
              let out := if hshort : 8 ≤ distance ∧ length ≤ 8 then
                output.copyWithinAtShort outPos distance length hshort.1
                  (uint16_add_usize_pos base extraBits
                    (lengthBase_pos idx.toNat (by
                      rw [Inflate.lengthBase_size]
                      simpa using USize.lt_iff_toNat_lt.mp (USize.not_le.mp h))))
                  hshort.2
                  (USize.not_lt.mp hds) (by omega)
                else
                  output.copyWithinAtU outPos distance length
              goCurU litTable distTable litLD distLD maxBits data maxOut pos bitBuf
                cnt4 hsz hlp out (outPos + length)
  else
    -- Tail (last <299 output bytes): finish the block with the bounds-checked
    -- `set!` loop over the same buffer — no copy, cost negligible.
    goCur litTable distTable litLD distLD maxBits data maxOut pos bitBuf cnt hsz hlp output outPos
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
    · omega

/-- Unboxed state produced by one input-margin refill probe. -/
structure WideRefillState where
  pos : USize
  bitBuf : UInt64
  cnt : USize
  didWide : Bool

/-- One libdeflate-style refill when eight bytes remain. The load deliberately
    remains unmasked: bits above `cnt` are genuine look-ahead bits and overlapping
    future loads OR the same stream bits back into the same positions. -/
@[inline] def wideRefillU (data : ByteArray) (pos : USize) (bitBuf : UInt64) (cnt : USize)
    (hsz : data.size < USize.size) : WideRefillState :=
  if hrcw : cnt ≤ 56 ∧ (8 : USize) ≤ data.size.toUSize ∧ pos ≤ data.size.toUSize - 8 then
    let k := (64 - cnt) >>> 3
    { pos := pos + k
      bitBuf := bitBuf ||| (data.ugetUInt64LE pos
        ((refillGuardWide_usize data pos cnt hsz).mp hrcw).2 <<< cnt.toUInt64)
      cnt := 64 - ((64 - cnt) &&& 7)
      didWide := true }
  else
    { pos := pos, bitBuf := bitBuf, cnt := cnt, didWide := false }

/-- A wide refill does not increase `goCurUW`'s termination measure. It advances
    `k` bytes and adds exactly `8k` counted bits, changing the measure by `-k`. -/
theorem wideRefillU_measure_le (data : ByteArray) (pos : USize) (bitBuf : UInt64) (cnt : USize)
    (hsz : data.size < USize.size) :
    let r := wideRefillU data pos bitBuf cnt hsz
    (data.size - r.pos.toNat) * 9 + r.cnt.toNat ≤
      (data.size - pos.toNat) * 9 + cnt.toNat := by
  simp only [wideRefillU]
  split
  · rename_i hrcw
    have hg := (refillGuardWide_usize data pos cnt hsz).mp hrcw
    have hcnt : cnt.toNat ≤ 56 := hg.1
    have hpos : pos.toNat + 8 ≤ data.size := hg.2
    have hk := wideRefillK_toNat cnt hcnt
    have hc := wideRefillCnt_toNat cnt hcnt
    have hpa : (pos + ((64 - cnt) >>> 3)).toNat = pos.toNat + (64 - cnt.toNat) / 8 := by
      rw [USize.toNat_add, hk]
      apply Nat.mod_eq_of_lt
      rw [← USize.size_eq_two_pow]
      omega
    simp only [hpa, hc]
    omega
  · simp

/-- Drop speculative look-ahead bits before handing the cold output-margin tail
    to the byte-at-a-time loop. The hot wide loop deliberately retains them. -/
@[inline] def trimBitBufU (bitBuf : UInt64) (cnt : USize) : UInt64 :=
  if cnt == 64 then bitBuf else bitBuf &&& ((1 <<< cnt.toUInt64) - 1)

set_option maxRecDepth 4096 in
/-- Word-at-a-time input-refill twin of `goCurU`. -/
def goCurUW (litTable distTable : DecodeTable) (litLD distLD : LongDecode)
    (maxBits : Nat) (data : ByteArray) (maxOut : Nat)
    (pos : USize) (bitBuf : UInt64) (cnt : USize)
    (hsz : data.size < USize.size)
    (hlp : litTable.packed.size = 2 ^ HuffTree.fastBits)
    (output : ByteArray) (outPos : USize) :
    Except String (ByteArray × USize × USize × UInt64 × USize) := do
  if hmt : outPos.toNat + 299 ≤ output.size then
  let r := wideRefillU data pos bitBuf cnt hsz
  have hwm := wideRefillU_measure_le data pos bitBuf cnt hsz
  let pos := r.pos
  let bitBuf := r.bitBuf
  let cnt := r.cnt
  let didWide := r.didWide
  if hrc : didWide = false ∧ cnt ≤ 56 ∧ pos < data.size.toUSize then
    goCurUW litTable distTable litLD distLD maxBits data maxOut
      (pos + 1)
      (bitBuf ||| ((data.uget pos (by
          have h := USize.lt_iff_toNat_lt.mp hrc.2.2
          rwa [toUSize_toNat_of_lt hsz] at h)).toUInt64 <<< cnt.toUInt64))
      (cnt + 8) hsz hlp output outPos
  else
    let e := litTable.entryAtU (bitBuf.toUSize &&& 0x7FF)
      (by rw [hlp]; exact HuffTree.toUSize_and_0x7FF_toNat_lt bitBuf)
    if hlit : HuffTree.unpackLen e ≠ 0
        ∧ (HuffTree.unpackLen e).toUSize ≤ cnt
        ∧ HuffTree.unpackSym e < 256 then
      goCurUW litTable distTable litLD distLD maxBits data maxOut pos
        (bitBuf >>> (HuffTree.unpackLen e).toUInt64)
        (cnt - (HuffTree.unpackLen e).toUSize)
        hsz hlp
        (output.uset outPos (HuffTree.unpackSym e).toUInt8 (by omega)) (outPos + 1)
    else
    let cnt0 := cnt.toNat
    match decodeSymCanon litLD litTable maxBits bitBuf cnt.toNat with
    | .error e => .error e
    | .ok (sym, bitBuf, cnt', _used) =>
      if sym < 256 then
        if hnp : cnt0 ≤ cnt' then throw "Inflate: no progress in Huffman decode"
        else
          goCurUW litTable distTable litLD distLD maxBits data maxOut pos bitBuf
            cnt'.toUSize hsz hlp
            (output.uset outPos sym.toUInt8 (by omega)) (outPos + 1)
      else if sym == 256 then
        .ok (output, outPos, pos, trimBitBufU bitBuf cnt'.toUSize, cnt'.toUSize)
      else
        let idx := sym.toUSize - 257
        if h : idx ≥ 29 then throw s!"Inflate: invalid length code {sym}"
        else
        let base := Inflate.lengthBase.uget idx (by
          rw [Inflate.lengthBase_size]
          simpa using USize.lt_iff_toNat_lt.mp (USize.not_le.mp h))
        let extra := Inflate.lengthExtra.uget idx (by
          rw [Inflate.lengthExtra_size]
          simpa using USize.lt_iff_toNat_lt.mp (USize.not_le.mp h))
        let (extraBits, bitBuf, cnt'') ← takeBitsU bitBuf cnt'.toUSize extra.toUSize
        let length := base.toUSize + extraBits.toUSize
        match decodeSymCanon distLD distTable maxBits bitBuf cnt''.toNat with
          | .error e => .error e
          | .ok (distSym, bitBuf, cnt3, _dused) =>
            let dIdx := distSym.toUSize
            if hd : dIdx ≥ 30 then throw s!"Inflate: invalid distance code {distSym}"
            else
              let dBase := Inflate.distBase.uget dIdx (by
                rw [Inflate.distBase_size]
                simpa using USize.lt_iff_toNat_lt.mp (USize.not_le.mp hd))
              let dExtra := Inflate.distExtra.uget dIdx (by
                rw [Inflate.distExtra_size]
                simpa using USize.lt_iff_toNat_lt.mp (USize.not_le.mp hd))
              let (dExtraBits, bitBuf, cnt4) ← takeBitsU bitBuf cnt3.toUSize dExtra.toUSize
              let distance := dBase.toUSize + dExtraBits.toUSize
              if hz : distance = 0 then throw s!"Inflate: zero back-reference distance"
              else if hds : distance > outPos then
                throw s!"Inflate: distance {distance.toNat} exceeds output size {outPos.toNat}"
              else if hlen : length > 258 then throw "Inflate: length exceeds 258"
              else if hnp : cnt0 ≤ cnt4.toNat then throw "Inflate: no progress in Huffman decode"
              else
                let out := if hshort : 8 ≤ distance ∧ length ≤ 8 then
                  output.copyWithinAtShort outPos distance length hshort.1
                    (uint16_add_usize_pos base extraBits
                      (lengthBase_pos idx.toNat (by
                        rw [Inflate.lengthBase_size]
                        simpa using USize.lt_iff_toNat_lt.mp (USize.not_le.mp h))))
                    hshort.2
                    (USize.not_lt.mp hds) (by omega)
                  else
                    output.copyWithinAtU outPos distance length
                goCurUW litTable distTable litLD distLD maxBits data maxOut pos bitBuf
                  cnt4 hsz hlp out (outPos + length)
  else
    goCur litTable distTable litLD distLD maxBits data maxOut pos (trimBitBufU bitBuf cnt) cnt
      hsz hlp output outPos
  termination_by (data.size - pos.toNat) * 9 + cnt.toNat
  decreasing_by
    all_goals
      simp_wf
      subst r
      subst pos
      subst cnt
      try subst bitBuf
      try subst didWide
      dsimp only at hwm
    · obtain ⟨_, hc, hp⟩ := hrc
      have hbig : (64 : Nat) < 2 ^ System.Platform.numBits :=
        USize.size_eq_two_pow ▸ Nat.lt_of_lt_of_le (by decide) USize.le_size
      have hpn : (wideRefillU data pos bitBuf cnt hsz).pos.toNat < data.size := by
        have h := USize.lt_iff_toNat_lt.mp hp; rwa [toUSize_toNat_of_lt hsz] at h
      have hcn : (wideRefillU data pos bitBuf cnt hsz).cnt.toNat ≤ 56 := by
        have h := USize.le_iff_toNat_le.mp hc
        rwa [USize.toNat_ofNat_of_lt (Nat.lt_of_lt_of_le (by decide) USize.le_size)] at h
      have hpa : ((wideRefillU data pos bitBuf cnt hsz).pos.toNat + 1) %
          2 ^ System.Platform.numBits =
          (wideRefillU data pos bitBuf cnt hsz).pos.toNat + 1 := by
        apply Nat.mod_eq_of_lt
        rw [← USize.size_eq_two_pow]
        omega
      have hca : ((wideRefillU data pos bitBuf cnt hsz).cnt.toNat + 8) %
          2 ^ System.Platform.numBits =
          (wideRefillU data pos bitBuf cnt hsz).cnt.toNat + 8 := by
        apply Nat.mod_eq_of_lt
        rw [← USize.size_eq_two_pow]
        have hbig' : (64 : Nat) < USize.size := USize.size_eq_two_pow ▸ hbig
        omega
      rw [hpa, hca]; omega
    · obtain ⟨hne, hle, _⟩ := hlit
      have hne' : (HuffTree.unpackLen e).toNat ≠ 0 := (uint8_ne_zero_iff_toNat _).mp hne
      have hlen : ((HuffTree.unpackLen e).toUSize).toNat = (HuffTree.unpackLen e).toNat :=
        UInt8.toNat_toUSize _
      have hsub : ((wideRefillU data pos bitBuf cnt hsz).cnt -
          (HuffTree.unpackLen e).toUSize).toNat =
          (wideRefillU data pos bitBuf cnt hsz).cnt.toNat -
            (HuffTree.unpackLen e).toNat := by
        rw [USize.toNat_sub_of_le _ _ hle, hlen]
      have hlecnt : (HuffTree.unpackLen e).toNat ≤
          (wideRefillU data pos bitBuf cnt hsz).cnt.toNat :=
        hlen ▸ USize.le_iff_toNat_le.mp hle
      rw [hsub]; omega
    · have hcsz : cnt0 < USize.size := by
        dsimp only [cnt0]
        exact USize.toNat_lt_two_pow_numBits _
      have hb : cnt'.toUSize.toNat = cnt' := toUSize_toNat_of_lt (by omega)
      rw [Nat.mod_eq_of_lt (by rw [← USize.size_eq_two_pow]; omega)]
      omega
    · omega

/-- Write `bytes[i]` at `output[outPos + i]` for `i ∈ [start, len)` via `set!`,
    by well-founded recursion. A `for i in [:len]` loop would compile to an opaque
    `forIn` that cannot be unfolded in proofs; this WF form lets the stored-block
    placement be characterised (`storedCopyLoop_extract` in the spec). -/
def storedCopyLoop (output bytes : ByteArray) (outPos start len : Nat) : ByteArray :=
  if start < len then
    storedCopyLoop (output.set! (outPos + start) (bytes.get! start)) bytes outPos (start + 1) len
  else output
termination_by len - start
decreasing_by omega

/-- Stored block at a cursor: bounds-check then `set!` the raw bytes at `outPos`
    (mirrors `Inflate.decodeStored`, which appends). Only the exact-size path, so
    the writes always land in bounds. -/
def decodeStoredCur (br : BitReader) (output : ByteArray) (outPos : Nat)
    (maxOut : Nat) : Except String (ByteArray × Nat × BitReader) := do
  let (len, br) ← br.readUInt16LE
  let (nlen, br) ← br.readUInt16LE
  if len ^^^ nlen != 0xFFFF then
    throw "Inflate: stored block length check failed"
  if outPos + len.toNat > maxOut then
    throw "Inflate: output exceeds maximum size"
  let (bytes, br) ← br.readBytes len.toNat
  return (storedCopyLoop output bytes outPos 0 len.toNat, outPos + len.toNat, br)

/-- Tree-free wide-buffer block decode at a cursor through `goCur` (the `set!`
    cursor). Direct call — no higher-order dispatch — so codegen matches the
    production `decodeHuffmanFastBufTables` shape (an `if useU then … else …`
    function selector de-specialises the loop and inflates the instruction count,
    contaminating the A/B). The `U` sibling below is the `uset` fastloop. Only the
    addressable (`br.data.size` fits `USize`) path; that always holds in memory. -/
def decodeHuffmanCurTables (br : BitReader) (output : ByteArray) (outPos : Nat)
    (litTable distTable : DecodeTable) (litLD distLD : LongDecode) (maxOut : Nat)
    (hlp : litTable.packed.size = 2 ^ HuffTree.fastBits) :
    Except String (ByteArray × Nat × BitReader) := do
  let (pos, bitBuf, cnt) := refill br.data br.pos 0 0
  let bitBuf := bitBuf >>> br.bitOff.toUInt64
  let cnt := cnt - br.bitOff
  if hsz : br.data.size.toUSize.toNat = br.data.size then
    let hlt : br.data.size < USize.size := by rw [← hsz]; exact USize.toNat_lt_two_pow_numBits _
    let (out, outPos', pos', bitBuf', cnt') ←
      goCur litTable distTable litLD distLD 15 br.data maxOut
        pos.toUSize bitBuf cnt.toUSize hlt hlp output outPos.toUSize
    let _ := bitBuf'
    let endbit := pos'.toNat * 8 - cnt'.toNat
    .ok (out, outPos'.toNat, { data := br.data, pos := endbit / 8, bitOff := endbit % 8 })
  else
    throw "Inflate: input too large for cursor decode"

/-- `decodeHuffmanCurTables` through the branch-free `uset` fastloop `goCurUW`,
    with word-at-a-time input refill behind an eight-byte margin. -/
def decodeHuffmanCurTablesU (br : BitReader) (output : ByteArray) (outPos : Nat)
    (litTable distTable : DecodeTable) (litLD distLD : LongDecode) (maxOut : Nat)
    (hlp : litTable.packed.size = 2 ^ HuffTree.fastBits) :
    Except String (ByteArray × Nat × BitReader) := do
  let (pos, bitBuf, cnt) := refill br.data br.pos 0 0
  let bitBuf := bitBuf >>> br.bitOff.toUInt64
  let cnt := cnt - br.bitOff
  if hsz : br.data.size.toUSize.toNat = br.data.size then
    let hlt : br.data.size < USize.size := by rw [← hsz]; exact USize.toNat_lt_two_pow_numBits _
    let (out, outPos', pos', bitBuf', cnt') ←
      goCurUW litTable distTable litLD distLD 15 br.data maxOut
        pos.toUSize bitBuf cnt.toUSize hlt hlp output outPos.toUSize
    let _ := bitBuf'
    let endbit := pos'.toNat * 8 - cnt'.toNat
    .ok (out, outPos'.toNat, { data := br.data, pos := endbit / 8, bitOff := endbit % 8 })
  else
    throw "Inflate: input too large for cursor decode"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- Tree-free block loop at a cursor (mirror of `Inflate.inflateLoopTreeFree`),
    threading the `outPos` write cursor, through the `set!` cursor. -/
def inflateLoopCur (br : BitReader) (output : ByteArray) (outPos : Nat)
    (maxOut dataSize : Nat) : Except String (ByteArray × Nat × Nat) := do
  let (bfinal, br₁) ← br.readBits 1
  let (btype, br₂) ← br₁.readBits 2
  let (output', outPos', br') ← match btype with
    | 0 => do
      let (o, p, b) ← decodeStoredCur br₂ output outPos maxOut
      pure (o, p, b)
    | 1 =>
      decodeHuffmanCurTables br₂ output outPos
        Inflate.fixedLitTF.1 Inflate.fixedDistTF.1 Inflate.fixedLitTF.2 Inflate.fixedDistTF.2 maxOut
        (HuffTree.buildTreeFreeWithCount_size Inflate.fixedLitLengths Inflate.fixedLitCount 15)
    | 2 => do
      let (litLens, distLens, br₃) ← Inflate.decodeDynamicLengthsOnly br₂
      let litCount := HuffTree.countLengthsFast litLens 15
      let distCount := HuffTree.countLengthsFast distLens 15
      let litTF := HuffTree.buildTreeFreeWithCount litLens litCount 15
      let distTF := HuffTree.buildTreeFreeWithCount distLens distCount 15
      decodeHuffmanCurTables br₃ output outPos litTF.1 distTF.1 litTF.2 distTF.2 maxOut
        (HuffTree.buildTreeFreeWithCount_size litLens litCount 15)
    | _ => throw s!"Inflate: reserved block type {btype}"
  if bfinal == 1 then
    return (output', outPos', br'.alignToByte.pos)
  else
    if _h₁ : br'.bitPos ≤ br.bitPos then
      throw "Inflate: no progress in inflate loop"
    else if _h₂ : dataSize * 8 < br'.bitPos then
      throw "Inflate: bit position out of range"
    else
      inflateLoopCur br' output' outPos' maxOut dataSize
  termination_by dataSize * 8 - br.bitPos
  decreasing_by all_goals omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- `inflateLoopCur` through the branch-free `uset` fastloop `goCurUW`. -/
def inflateLoopCurU (br : BitReader) (output : ByteArray) (outPos : Nat)
    (maxOut dataSize : Nat) : Except String (ByteArray × Nat × Nat) := do
  let (bfinal, br₁) ← br.readBits 1
  let (btype, br₂) ← br₁.readBits 2
  let (output', outPos', br') ← match btype with
    | 0 => do
      let (o, p, b) ← decodeStoredCur br₂ output outPos maxOut
      pure (o, p, b)
    | 1 =>
      decodeHuffmanCurTablesU br₂ output outPos
        Inflate.fixedLitTF.1 Inflate.fixedDistTF.1 Inflate.fixedLitTF.2 Inflate.fixedDistTF.2 maxOut
        (HuffTree.buildTreeFreeWithCount_size Inflate.fixedLitLengths Inflate.fixedLitCount 15)
    | 2 => do
      let (litLens, distLens, br₃) ← Inflate.decodeDynamicLengthsOnly br₂
      let litCount := HuffTree.countLengthsFast litLens 15
      let distCount := HuffTree.countLengthsFast distLens 15
      let litTF := HuffTree.buildTreeFreeWithCount litLens litCount 15
      let distTF := HuffTree.buildTreeFreeWithCount distLens distCount 15
      decodeHuffmanCurTablesU br₃ output outPos litTF.1 distTF.1 litTF.2 distTF.2 maxOut
        (HuffTree.buildTreeFreeWithCount_size litLens litCount 15)
    | _ => throw s!"Inflate: reserved block type {btype}"
  if bfinal == 1 then
    return (output', outPos', br'.alignToByte.pos)
  else
    if _h₁ : br'.bitPos ≤ br.bitPos then
      throw "Inflate: no progress in inflate loop"
    else if _h₂ : dataSize * 8 < br'.bitPos then
      throw "Inflate: bit position out of range"
    else
      inflateLoopCurU br' output' outPos' maxOut dataSize
  termination_by dataSize * 8 - br.bitPos
  decreasing_by all_goals omega

end InflateBuf

namespace Inflate

/-- **Fastloop spike (issue #2799), exact-size path only.** Inflate a raw DEFLATE
    stream by pre-extending the output to `sizeHint` and writing every literal /
    match at a cursor (write-once `set!` / `copyWithinAt`) rather than `push`. The
    caller MUST pass the true decompressed length as `sizeHint`. Not yet proven
    equal to the reference; used only for A/B profiling and the conformance test.
    See `Zip/Native/InflateFast.lean`. -/
def inflateRawFast (data : ByteArray) (startPos : Nat := 0)
    (maxOutputSize : Nat := 1024 * 1024 * 1024) (sizeHint : Nat := 0) :
    Except String (ByteArray × Nat) := do
  -- Accept-set guard: the buffer is presized to `sizeHint`, so a hint above the
  -- cap would let the cursor write past `maxOutputSize` (the fastloop drops the
  -- per-symbol max-size check under the margin). Reject it up front.
  if sizeHint > maxOutputSize then throw "Inflate: sizeHint exceeds maximum output size"
  let br : BitReader := { data, pos := startPos, bitOff := 0 }
  let (output, outPos, endPos) ←
    InflateBuf.inflateLoopCur br (ByteArray.presize sizeHint) 0 maxOutputSize data.size
  -- Executable exact-size contract: the stream must decode to exactly `sizeHint`
  -- (= `output.size`). Anything else is a wrong hint; error rather than return a
  -- silently truncated/over-allocated `.ok`.
  if outPos ≠ output.size then
    throw s!"Inflate: fast decode produced {outPos} bytes, sizeHint was {output.size}"
  return (output, endPos)

/-- `inflateRawFast` through the branch-free `uset` fastloop. -/
def inflateRawFastU (data : ByteArray) (startPos : Nat := 0)
    (maxOutputSize : Nat := 1024 * 1024 * 1024) (sizeHint : Nat := 0) :
    Except String (ByteArray × Nat) := do
  if sizeHint > maxOutputSize then throw "Inflate: sizeHint exceeds maximum output size"
  let br : BitReader := { data, pos := startPos, bitOff := 0 }
  let (output, outPos, endPos) ←
    InflateBuf.inflateLoopCurU br (ByteArray.presize sizeHint) 0 maxOutputSize data.size
  if outPos ≠ output.size then
    throw s!"Inflate: fast decode produced {outPos} bytes, sizeHint was {output.size}"
  return (output, endPos)

/-- `inflateRawFast` whole-buffer wrapper (spike): `set!`-cursor path. -/
def inflateFast (data : ByteArray) (maxOutputSize : Nat := 1024 * 1024 * 1024)
    (sizeHint : Nat := 0) : Except String ByteArray := do
  let (output, _) ← inflateRawFast data 0 maxOutputSize sizeHint
  return output

/-- `inflateRawFast` whole-buffer wrapper (spike): branch-free `uset` fastloop. -/
def inflateFastU (data : ByteArray) (maxOutputSize : Nat := 1024 * 1024 * 1024)
    (sizeHint : Nat := 0) : Except String ByteArray := do
  let (output, _) ← inflateRawFastU data 0 maxOutputSize sizeHint
  return output

/-- **Production fastloop dispatch.** When the caller knows the *exact*
    decompressed size and has bounded it (`exact = true`, `sizeHint > 0` — the
    ZIP local/central-directory `uncompressedSize`, the gzip ISIZE, both clamped
    to a presize cap by the caller), decode with the verified branch-free `uset`
    margin-split fastloop `inflateFastU`, which writes every byte once into the
    pre-extended buffer. It is proven to return exactly `inflate`'s bytes on a
    valid stream at the exact size (`Zip.Native.inflateSized_eq`, via
    `inflateFastU_eq`); on a wrong hint or a corrupt stream the fastloop rejects
    (its exact-size contract) and we fall back to the push-based production
    `inflate`, so the result never differs from `inflate` for accepted input and
    any downstream checksum still guards a mismatch. Without an exact bounded
    size we decode with `inflate` directly, keeping `sizeHint` as its inert
    capacity hint. -/
def inflateSized (data : ByteArray) (maxOutputSize : Nat := 1024 * 1024 * 1024)
    (sizeHint : Nat := 0) (exact : Bool := false) : Except String ByteArray :=
  if exact && sizeHint > 0 then
    match inflateFastU data maxOutputSize sizeHint with
    | .ok out => .ok out
    | .error _ => inflate data maxOutputSize sizeHint
  else
    inflate data maxOutputSize sizeHint

/-- **Production fastloop dispatch, raw offset form.** The `inflateRaw` counterpart
    of `inflateSized`: it decodes a DEFLATE stream starting at byte offset `startPos`
    and, alongside the bytes, returns the byte-aligned position after the last block
    (`endPos`), which a container decoder needs to locate the trailer / next member.
    When the caller knows the *exact* decompressed size and has bounded it
    (`exact = true`, `sizeHint > 0` — for gzip, the trailer `ISIZE` of a single-member
    stream, clamped to a presize cap), decode with the verified branch-free `uset`
    fastloop `inflateRawFastU`; on a wrong hint or a corrupt stream the fastloop
    rejects (its exact-size contract) and we fall back to the push-based production
    `inflateRaw`. It is proven equal to `inflateRaw` for every `USize`-representable
    input (`Zip.Native.inflateRawSized_agrees`), so it never changes the decoded
    bytes or `endPos`. Without an exact bounded size we decode with `inflateRaw`
    directly. -/
def inflateRawSized (data : ByteArray) (startPos : Nat := 0)
    (maxOutputSize : Nat := 1024 * 1024 * 1024) (sizeHint : Nat := 0)
    (exact : Bool := false) : Except String (ByteArray × Nat) :=
  if exact && sizeHint > 0 then
    match inflateRawFastU data startPos maxOutputSize sizeHint with
    | .ok r => .ok r
    | .error _ => inflateRaw data startPos maxOutputSize
  else
    inflateRaw data startPos maxOutputSize

end Inflate
end Zip.Native
