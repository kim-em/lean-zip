/-
  Native Level 0 roundtrip: inflate (deflateStoredPure data) = .ok data

  Proves that the native DEFLATE decompressor correctly round-trips data
  encoded as stored (uncompressed) blocks. This is the simplest possible
  native roundtrip — no Huffman encoding, no LZ77 matching.

  ## Status
  - `deflateStoredPure` definition: complete
  - `readBits_1_at_0`: proved
  - `readBits_2_at_1`: proved (bv_decide for bitvector identity)
  - `readUInt16LE_at_aligned`: proved
  - `uint16_le_roundtrip`: proved (bv_decide)
  - `uint16_xor_complement`: proved (bv_decide)
  - `readBytes_at_aligned`: proved
  - `decodeStored_on_block`: proved (composing the above)
  - `readUInt16LE_align`: proved
  - `decodeStored_align`: proved
  - `inflateLoop_final_stored`: proved (composing all the above)
  - `fromLengths_*_ok`: sorry (Array.any is kernel-opaque)
  - `inflate_deflateStoredPure`: sorry (needs fromLengths + multi-block induction)

  ## Proof approach
  The roundtrip proof requires tracing through the native inflate pipeline
  on the specific byte sequence produced by deflateStoredPure:
  1. inflate → inflateRaw → fromLengths (builds Huffman trees, unused for stored blocks)
  2. inflateLoop reads BFINAL (1 bit), BTYPE (2 bits), dispatches to decodeStored
  3. decodeStored: alignToByte → readUInt16LE (LEN) → readUInt16LE (NLEN) → readBytes
  4. If multi-block, inflateLoop recurses

  Key difficulty: ByteArray indexing through concatenation boundaries,
  and converting between `getElem!` (runtime) and `getElem` (proof-friendly).
-/
import Zip.Native.Inflate
import Zip.Native.Deflate
import Std.Tactic.BVDecide

namespace Zip.Spec.DeflateStoredCorrect

open Zip.Native

/-- Pure recursive version of deflateStored for proof purposes.
    Encodes data as stored DEFLATE blocks starting from position `pos`.
    Each block has at most 65535 data bytes. The last block has BFINAL=1.
    When `pos ≥ data.size`, produces a single final empty block. -/
def deflateStoredPure (data : ByteArray) (pos : Nat := 0) : ByteArray :=
  let blockSize := min (data.size - pos) 65535
  if h : pos + blockSize ≥ data.size then
    let len := blockSize.toUInt16
    let nlen := len ^^^ 0xFFFF
    ByteArray.mk #[0x01, (len &&& 0xFF).toUInt8,
      ((len >>> 8) &&& 0xFF).toUInt8, (nlen &&& 0xFF).toUInt8,
      ((nlen >>> 8) &&& 0xFF).toUInt8] ++ data.extract pos (pos + blockSize)
  else
    let len := blockSize.toUInt16
    let nlen := len ^^^ 0xFFFF
    let hdr := ByteArray.mk #[0x00, (len &&& 0xFF).toUInt8,
      ((len >>> 8) &&& 0xFF).toUInt8, (nlen &&& 0xFF).toUInt8,
      ((nlen >>> 8) &&& 0xFF).toUInt8]
    (hdr ++ data.extract pos (pos + blockSize)) ++
      deflateStoredPure data (pos + blockSize)
termination_by data.size - pos
decreasing_by omega

-- Sanity checks: round-trip through native inflate
#eval do
  let data := ByteArray.mk #[1, 2, 3, 4, 5]
  let compressed := deflateStoredPure data
  match Inflate.inflate compressed with
  | .ok result => return result == data
  | .error _ => return false

#eval do
  let data := ByteArray.empty
  let compressed := deflateStoredPure data
  match Inflate.inflate compressed with
  | .ok result => return result == data
  | .error _ => return false

-- Sanity check: multi-block round-trip (data > 65535 bytes)
#eval do
  let data := ByteArray.mk (.replicate 100000 42)
  let compressed := deflateStoredPure data
  match Inflate.inflate compressed with
  | .ok result => return result == data
  | .error _ => return false

/-! ## fromLengths succeeds on fixed codes

These are computationally verified by the #eval checks above.
Array.any is opaque to the kernel evaluator, making direct proof difficult.
Approach tried: converting to List via toList + mem_replicate, which works
for the first guard (all lengths ≤ 15) but the Kraft inequality computation
also involves List.foldl on a large list which doesn't reduce. -/

theorem fromLengths_fixedDist_ok :
    ∃ t, HuffTree.fromLengths Inflate.fixedDistLengths = .ok t := by
  unfold HuffTree.fromLengths Inflate.fixedDistLengths
  -- Guard 1: no code length > 15 (convert Array.any to List.any for kernel evaluation)
  rw [show ((Array.replicate 32 (5 : UInt8)).any fun l => decide (l.toNat > 15)) = false from by
    rw [← Array.any_toList]; decide]
  simp only [Bool.false_eq_true, ↓reduceIte]
  -- Guard 2: Kraft inequality (List.foldl is kernel-reducible)
  have h2 : ¬(List.foldl (fun acc l => acc + 2 ^ (15 - l)) 0
    (List.filter (fun x => x != 0)
      (List.map UInt8.toNat (Array.replicate 32 (5 : UInt8)).toList)) > 2 ^ 15) := by decide
  simp only [h2, ↓reduceIte]
  exact ⟨_, rfl⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
theorem fromLengths_fixedLit_ok :
    ∃ t, HuffTree.fromLengths Inflate.fixedLitLengths = .ok t := by
  unfold HuffTree.fromLengths Inflate.fixedLitLengths
  -- Guard 1: no code length > 15
  rw [show ((Array.replicate 144 (8 : UInt8) ++ .replicate 112 9 ++
    .replicate 24 7 ++ .replicate 8 8).any fun l => decide (l.toNat > 15)) = false from by
    rw [← Array.any_toList]; decide]
  simp only [Bool.false_eq_true, ↓reduceIte]
  -- Guard 2: Kraft inequality
  have h2 : ¬(List.foldl (fun acc l => acc + 2 ^ (15 - l)) 0
    (List.filter (fun x => x != 0)
      (List.map UInt8.toNat (Array.replicate 144 (8 : UInt8) ++ .replicate 112 9 ++
        .replicate 24 7 ++ .replicate 8 8).toList)) > 2 ^ 15) := by decide
  simp only [h2, ↓reduceIte]
  exact ⟨_, rfl⟩

/-! ## BitReader operation lemmas for stored block format -/

/-- Reading 1 bit from a byte at bitOff 0 returns the LSB. -/
theorem readBits_1_at_0 (data : ByteArray) (pos : Nat)
    (hpos : pos < data.size) :
    BitReader.readBits { data, pos, bitOff := 0 } 1 =
    .ok ((data[pos].toUInt32 &&& 1),
         { data, pos, bitOff := 1 }) := by
  unfold BitReader.readBits BitReader.readBits.go
  simp only [BitReader.readBit, show ¬(pos ≥ data.size) from by omega,
    ↓reduceIte, show ¬(0 + 1 ≥ 8) from by omega,
    bind, Except.bind]
  unfold BitReader.readBits.go
  simp only [Except.ok.injEq, Prod.mk.injEq]
  rw [getElem!_pos data pos hpos]
  constructor
  · simp [UInt32.shiftRight_zero, UInt32.shiftLeft_zero, UInt32.zero_or]
  · simp

/-- Reading 2 bits starting at bitOff 1 within the same byte.
    Returns bits 1-2 of the byte as a 2-bit value.
    Approach tried: unfolding readBits.go twice, reducing readBit at each step.
    Remaining: bitvector arithmetic identity
    (0 ||| (((x >>> 1) &&& 1) <<< 0)) ||| (((x >>> 2) &&& 1) <<< 1) = (x >>> 1) &&& 3 -/
theorem readBits_2_at_1 (data : ByteArray) (pos : Nat)
    (hpos : pos < data.size) :
    BitReader.readBits { data, pos, bitOff := 1 } 2 =
    .ok (((data[pos].toUInt32 >>> 1) &&& 3),
         { data, pos, bitOff := 3 }) := by
  unfold BitReader.readBits BitReader.readBits.go
  simp only [BitReader.readBit, show ¬(pos ≥ data.size) from by omega,
    ↓reduceIte, show ¬(1 + 1 ≥ 8) from by omega,
    bind, Except.bind]
  unfold BitReader.readBits.go
  simp only [BitReader.readBit, show ¬(pos ≥ data.size) from by omega,
    ↓reduceIte, show ¬(2 + 1 ≥ 8) from by omega,
    bind, Except.bind]
  unfold BitReader.readBits.go
  rw [getElem!_pos data pos hpos]
  simp only [Except.ok.injEq, Prod.mk.injEq]
  constructor
  · simp [UInt32.shiftLeft_zero, UInt32.zero_or]
    generalize data[pos].toUInt32 = x
    bv_decide
  · simp

/-! ## Helper lemmas for readUInt16LE and readBytes -/

/-- Reading UInt16LE at byte-aligned position succeeds. -/
theorem readUInt16LE_at_aligned (data : ByteArray) (pos : Nat)
    (hpos : pos + 2 ≤ data.size) :
    BitReader.readUInt16LE { data, pos, bitOff := 0 } =
    .ok (data[pos]!.toUInt16 ||| (data[pos + 1]!.toUInt16 <<< 8),
         { data, pos := pos + 2, bitOff := 0 }) := by
  unfold BitReader.readUInt16LE BitReader.alignToByte
  simp only [show ((0 : Nat) == 0) = true from rfl, ↓reduceIte,
    show ¬(pos + 2 > data.size) from by omega]

/-- LE encoding/decoding roundtrip for UInt16. -/
theorem uint16_le_roundtrip (v : UInt16) :
    ((v &&& 0xFF).toUInt8).toUInt16 ||| (((v >>> 8) &&& 0xFF).toUInt8).toUInt16 <<< 8 = v := by
  bv_decide

/-- UInt16 XOR self-inverse: a ^^^ (a ^^^ 0xFFFF) = 0xFFFF. -/
theorem uint16_xor_complement (a : UInt16) : a ^^^ (a ^^^ 0xFFFF) = 0xFFFF := by
  bv_decide

/-- Reading readBytes at byte-aligned position succeeds. -/
theorem readBytes_at_aligned (data : ByteArray) (pos n : Nat)
    (hpos : pos + n ≤ data.size) :
    BitReader.readBytes { data, pos, bitOff := 0 } n =
    .ok (data.extract pos (pos + n), { data, pos := pos + n, bitOff := 0 }) := by
  unfold BitReader.readBytes BitReader.alignToByte
  simp only [show ((0 : Nat) == 0) = true from rfl, ↓reduceIte,
    show ¬(pos + n > data.size) from by omega]

/-! ## decodeStored on properly formatted block data -/

/-- The decodeStored function on properly formatted stored block data
    succeeds and returns the block data.
    Precondition: the BitReader is byte-aligned at the LEN field. -/
theorem decodeStored_on_block (compressed : ByteArray) (brPos : Nat)
    (blockLen : Nat) (hlen : blockLen ≤ 65535)
    (output : ByteArray) (maxOutputSize : Nat)
    (hfit : output.size + blockLen ≤ maxOutputSize)
    (hdata_size : brPos + 4 + blockLen ≤ compressed.size)
    (hlen_lo : compressed[brPos]'(by omega) =
      (blockLen.toUInt16 &&& 0xFF).toUInt8)
    (hlen_hi : compressed[brPos + 1]'(by omega) =
      ((blockLen.toUInt16 >>> 8) &&& 0xFF).toUInt8)
    (hnlen_lo : compressed[brPos + 2]'(by omega) =
      ((blockLen.toUInt16 ^^^ 0xFFFF) &&& 0xFF).toUInt8)
    (hnlen_hi : compressed[brPos + 3]'(by omega) =
      (((blockLen.toUInt16 ^^^ 0xFFFF) >>> 8) &&& 0xFF).toUInt8) :
    Inflate.decodeStored
      { data := compressed, pos := brPos, bitOff := 0 } output maxOutputSize =
    .ok (output ++ compressed.extract (brPos + 4) (brPos + 4 + blockLen),
         { data := compressed, pos := brPos + 4 + blockLen, bitOff := 0 }) := by
  -- Step 1: readUInt16LE for LEN
  have hru1 := readUInt16LE_at_aligned compressed brPos (by omega)
  rw [getElem!_pos compressed brPos (by omega),
      getElem!_pos compressed (brPos + 1) (by omega)] at hru1
  rw [hlen_lo, hlen_hi] at hru1
  rw [uint16_le_roundtrip] at hru1
  -- Step 2: readUInt16LE for NLEN
  have hru2 := readUInt16LE_at_aligned compressed (brPos + 2) (by omega)
  rw [getElem!_pos compressed (brPos + 2) (by omega),
      getElem!_pos compressed (brPos + 2 + 1) (by omega)] at hru2
  rw [hnlen_lo, hnlen_hi] at hru2
  rw [uint16_le_roundtrip] at hru2
  -- Step 3: blockLen.toUInt16.toNat = blockLen
  have hbl_toNat : blockLen.toUInt16.toNat = blockLen := by
    simp [Nat.mod_eq_of_lt (show blockLen < 65536 from by omega)]
  -- Step 4: readBytes for block data
  have hrb := readBytes_at_aligned compressed (brPos + 4) blockLen (by omega)
  -- Step 5: Compose everything
  simp only [Inflate.decodeStored, bind, Except.bind, hru1, hru2]
  -- XOR check: a ^^^ (a ^^^ 0xFFFF) = 0xFFFF
  rw [uint16_xor_complement]
  -- 65535 != 65535 = false (Bool)
  simp only [show ((65535 : UInt16) != 65535) = false from by decide,
    Bool.false_eq_true, ↓reduceIte]
  -- pure PUnit.unit reduces
  simp only [pure, Except.pure]
  -- Size check (Prop-based if)
  rw [hbl_toNat]
  simp only [show ¬(output.size + blockLen > maxOutputSize) from by omega, ↓reduceIte]
  -- readBytes
  have hrb' := readBytes_at_aligned compressed (brPos + 2 + 2) blockLen (by omega)
  simp only [hrb']

/-- readUInt16LE with non-zero bitOff aligns to next byte first. -/
theorem readUInt16LE_align (data : ByteArray) (pos bitOff : Nat)
    (hbo : bitOff ≠ 0) :
    BitReader.readUInt16LE { data, pos, bitOff } =
    BitReader.readUInt16LE { data, pos := pos + 1, bitOff := 0 } := by
  unfold BitReader.readUInt16LE BitReader.alignToByte
  have hbo' : (bitOff == 0) = false := by
    cases heq : bitOff == 0 <;> simp_all [beq_iff_eq]
  simp only [show ((0 : Nat) == 0) = true from rfl, hbo',
    Bool.false_eq_true, ↓reduceIte]

/-- decodeStored with non-zero bitOff aligns to the next byte. -/
theorem decodeStored_align (compressed : ByteArray) (brPos bitOff : Nat)
    (hbo : bitOff ≠ 0) (output : ByteArray) (maxOutputSize : Nat) :
    Inflate.decodeStored { data := compressed, pos := brPos, bitOff } output maxOutputSize =
    Inflate.decodeStored { data := compressed, pos := brPos + 1, bitOff := 0 } output maxOutputSize := by
  simp only [Inflate.decodeStored, bind, Except.bind,
    readUInt16LE_align compressed brPos bitOff hbo]

/-! ## inflateLoop processes stored blocks -/

/-- inflateLoop correctly processes a single final stored block.
    The block starts at brPos with header byte 0x01 (BFINAL=1, BTYPE=00),
    followed by LEN/NLEN/data starting at brPos+1.
    This combines readBits_1_at_0 (BFINAL), readBits_2_at_1 (BTYPE),
    and decodeStored_on_block. -/
theorem inflateLoop_final_stored (compressed : ByteArray) (brPos : Nat)
    (blockLen : Nat) (hlen : blockLen ≤ 65535)
    (output : ByteArray) (maxOutputSize : Nat)
    (fixedLit fixedDist : HuffTree) (fuel : Nat) (hfuel : fuel ≥ 1)
    (hfit : output.size + blockLen ≤ maxOutputSize)
    (hpos : brPos < compressed.size)
    (hhdr : compressed[brPos] = 0x01)
    (hdata_size : brPos + 5 + blockLen ≤ compressed.size)
    (hlen_lo : compressed[brPos + 1]'(by omega) =
      (blockLen.toUInt16 &&& 0xFF).toUInt8)
    (hlen_hi : compressed[brPos + 2]'(by omega) =
      ((blockLen.toUInt16 >>> 8) &&& 0xFF).toUInt8)
    (hnlen_lo : compressed[brPos + 3]'(by omega) =
      ((blockLen.toUInt16 ^^^ 0xFFFF) &&& 0xFF).toUInt8)
    (hnlen_hi : compressed[brPos + 4]'(by omega) =
      (((blockLen.toUInt16 ^^^ 0xFFFF) >>> 8) &&& 0xFF).toUInt8) :
    Inflate.inflateLoop
      { data := compressed, pos := brPos, bitOff := 0 } output
      fixedLit fixedDist maxOutputSize fuel =
    .ok (output ++ compressed.extract (brPos + 5) (brPos + 5 + blockLen),
         brPos + 5 + blockLen) := by
  -- fuel ≥ 1, so fuel = fuel' + 1 for some fuel'
  obtain ⟨fuel', rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
  -- Unfold inflateLoop at fuel' + 1
  unfold Inflate.inflateLoop
  simp only [bind, Except.bind]
  -- Step 1: readBits 1 (BFINAL)
  rw [readBits_1_at_0 compressed brPos hpos]
  simp only [bind, Except.bind]
  -- Step 2: readBits 2 (BTYPE)
  rw [readBits_2_at_1 compressed brPos hpos]
  simp only [bind, Except.bind]
  -- Step 3: From hhdr, compute bfinal and btype
  rw [hhdr]
  -- 0x01.toUInt32 &&& 1 = 1 (bfinal) and (0x01.toUInt32 >>> 1) &&& 3 = 0 (btype)
  simp only [show (0x01 : UInt8).toUInt32 &&& 1 = 1 from by decide,
    show ((0x01 : UInt8).toUInt32 >>> 1) &&& 3 = 0 from by decide]
  -- decodeStored with bitOff = 3 aligns to brPos + 1
  rw [decodeStored_align compressed brPos 3 (by omega)]
  -- Apply decodeStored_on_block at position brPos + 1
  rw [decodeStored_on_block compressed (brPos + 1) blockLen hlen output maxOutputSize
    hfit (by omega) hlen_lo hlen_hi hnlen_lo hnlen_hi]
  -- bfinal == 1 is true, alignToByte is identity at bitOff=0
  have h_beq : ((1 : UInt32) == 1) = true := by decide
  simp only [h_beq, ↓reduceIte, BitReader.alignToByte,
    show ((0 : Nat) == 0) = true from rfl, pure, Except.pure]

/-- inflateLoop correctly processes a single non-final stored block.
    The block starts at brPos with header byte 0x00 (BFINAL=0, BTYPE=00).
    After processing, inflateLoop recurses with the output extended and
    the BitReader advanced past the block data, with fuel decremented by 1. -/
theorem inflateLoop_nonfinal_stored (compressed : ByteArray) (brPos : Nat)
    (blockLen : Nat) (hlen : blockLen ≤ 65535)
    (output : ByteArray) (maxOutputSize : Nat)
    (fixedLit fixedDist : HuffTree) (fuel : Nat)
    (hfit : output.size + blockLen ≤ maxOutputSize)
    (hpos : brPos < compressed.size)
    (hhdr : compressed[brPos] = 0x00)
    (hdata_size : brPos + 5 + blockLen ≤ compressed.size)
    (hlen_lo : compressed[brPos + 1]'(by omega) =
      (blockLen.toUInt16 &&& 0xFF).toUInt8)
    (hlen_hi : compressed[brPos + 2]'(by omega) =
      ((blockLen.toUInt16 >>> 8) &&& 0xFF).toUInt8)
    (hnlen_lo : compressed[brPos + 3]'(by omega) =
      ((blockLen.toUInt16 ^^^ 0xFFFF) &&& 0xFF).toUInt8)
    (hnlen_hi : compressed[brPos + 4]'(by omega) =
      (((blockLen.toUInt16 ^^^ 0xFFFF) >>> 8) &&& 0xFF).toUInt8) :
    Inflate.inflateLoop
      { data := compressed, pos := brPos, bitOff := 0 } output
      fixedLit fixedDist maxOutputSize (fuel + 1) =
    Inflate.inflateLoop
      { data := compressed, pos := brPos + 5 + blockLen, bitOff := 0 }
      (output ++ compressed.extract (brPos + 5) (brPos + 5 + blockLen))
      fixedLit fixedDist maxOutputSize fuel := by
  -- Unfold inflateLoop only on the LHS (fuel + 1 → body with fuel)
  conv => lhs; unfold Inflate.inflateLoop
  simp only [bind, Except.bind]
  -- Step 1: readBits 1 (BFINAL)
  rw [readBits_1_at_0 compressed brPos hpos]
  simp only [bind, Except.bind]
  -- Step 2: readBits 2 (BTYPE)
  rw [readBits_2_at_1 compressed brPos hpos]
  simp only [bind, Except.bind]
  -- Step 3: From hhdr, compute bfinal and btype
  rw [hhdr]
  simp only [show (0x00 : UInt8).toUInt32 &&& 1 = 0 from by decide,
    show ((0x00 : UInt8).toUInt32 >>> 1) &&& 3 = 0 from by decide]
  -- decodeStored with bitOff = 3 aligns to brPos + 1
  rw [decodeStored_align compressed brPos 3 (by omega)]
  -- Apply decodeStored_on_block at position brPos + 1
  rw [decodeStored_on_block compressed (brPos + 1) blockLen hlen output maxOutputSize
    hfit (by omega) hlen_lo hlen_hi hnlen_lo hnlen_hi]
  -- bfinal == 1 is false (bfinal = 0), so inflateLoop recurses
  have h_beq : ((0 : UInt32) == 1) = false := by decide
  simp only [h_beq, Bool.false_eq_true, ↓reduceIte]

/-! ## Helper lemmas for ByteArray indexing into pfx ++ (hdr ++ rest) -/

/-- Accessing byte at position pfx.size + k in pfx ++ (hdr ++ rest)
    gives hdr[k] when k < hdr.size. -/
private theorem getElem_pfx_hdr (pfx hdr rest : ByteArray) (k : Nat)
    (hk : k < hdr.size) (h : pfx.size + k < (pfx ++ (hdr ++ rest)).size) :
    (pfx ++ (hdr ++ rest))[pfx.size + k] = hdr[k] := by
  rw [ByteArray.getElem_append_right (by omega)]
  simp only [show pfx.size + k - pfx.size = k from by omega]
  exact ByteArray.getElem_append_left hk

/-! ## Main roundtrip theorem -/

/-- inflateLoop correctly processes all stored blocks produced by
    deflateStoredPure, with an arbitrary prefix prepended to the compressed data.
    The prefix parameterization handles relocation: after processing each block,
    the prefix grows by one block, and the IH naturally applies. -/
private theorem inflateLoop_deflateStored (data : ByteArray) (pos : Nat)
    (hpos : pos ≤ data.size) (h_size : data.size ≤ 256 * 1024 * 1024)
    (pfx output : ByteArray) (fixedLit fixedDist : HuffTree)
    (fuel maxOutputSize : Nat)
    (h_fuel : fuel ≥ (data.size - pos + 65534) / 65535)
    (h_fit : output.size + (data.size - pos) ≤ maxOutputSize) :
    ∃ endPos, Inflate.inflateLoop
      { data := pfx ++ deflateStoredPure data pos, pos := pfx.size, bitOff := 0 }
      output fixedLit fixedDist maxOutputSize fuel =
    .ok (output ++ data.extract pos data.size, endPos) := by
  sorry

/-- Native Level 0 roundtrip: compressing with stored blocks then
    decompressing with the native inflate recovers the original data.
    The size constraint ensures the default maxOutputSize (256 MiB) suffices
    and the default fuel (10001 blocks) covers the input. -/
theorem inflate_deflateStoredPure (data : ByteArray)
    (h : data.size ≤ 256 * 1024 * 1024) :
    Inflate.inflate (deflateStoredPure data) = .ok data := by
  sorry

end Zip.Spec.DeflateStoredCorrect
