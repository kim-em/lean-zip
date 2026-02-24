/-
  Native Level 0 roundtrip: inflate (deflateStoredPure data) = .ok data

  Proves that the native DEFLATE decompressor correctly round-trips data
  encoded as stored (uncompressed) blocks. This is the simplest possible
  native roundtrip — no Huffman encoding, no LZ77 matching.

  The roundtrip proof traces through the native inflate pipeline
  on the specific byte sequence produced by deflateStoredPure:
  1. inflate → inflateRaw → fromLengths (builds Huffman trees, unused for stored blocks)
  2. inflateLoop reads BFINAL (1 bit), BTYPE (2 bits), dispatches to decodeStored
  3. decodeStored: alignToByte → readUInt16LE (LEN) → readUInt16LE (NLEN) → readBytes
  4. If multi-block, inflateLoop recurses with strong induction on remaining data
-/
import Zip.Native.Inflate
import Zip.Native.Deflate
import ZipForStd.ByteArray
import Std.Tactic.BVDecide

namespace Zip.Spec.DeflateStoredCorrect

open Zip.Native

/-- Pure recursive version of deflateStored for proof purposes.
    Encodes data as stored DEFLATE blocks starting from position `pos`.
    Each block has at most 65535 data bytes. The last block has BFINAL=1.
    When `pos ≥ data.size`, produces a single final empty block. -/
def deflateStoredPure (data : ByteArray) (pos : Nat := 0) : ByteArray :=
  let blockSize := min (data.size - pos) 65535
  if _ : pos + blockSize ≥ data.size then
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

/-! ## fromLengths succeeds on fixed codes

Array.any is opaque to the kernel evaluator, so we rewrite through List.any
for the first guard and List.foldl for the Kraft inequality guard. -/

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
    Returns bits 1-2 of the byte as a 2-bit value. -/
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

set_option linter.unusedSimpArgs false in
/-- inflateLoop correctly processes a single final stored block.
    The block starts at brPos with header byte 0x01 (BFINAL=1, BTYPE=00),
    followed by LEN/NLEN/data starting at brPos+1. -/
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

set_option linter.unusedSimpArgs false in
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

/-! ## Helper lemmas for ByteArray operations on concatenated arrays -/

/-- Accessing byte at position pfx.size + k in pfx ++ (hdr ++ rest)
    gives hdr[k] when k < hdr.size. -/
private theorem getElem_pfx_hdr (pfx hdr rest : ByteArray) (k : Nat)
    (hk : k < hdr.size) (h : pfx.size + k < (pfx ++ (hdr ++ rest)).size) :
    (pfx ++ (hdr ++ rest))[pfx.size + k] = hdr[k] := by
  rw [ByteArray.getElem_append_right (by omega)]
  simp only [show pfx.size + k - pfx.size = k from by omega]
  exact ByteArray.getElem_append_left hk

private theorem getElem_pfx_hdr_zero (pfx hdr rest : ByteArray)
    (hk : 0 < hdr.size) (h : pfx.size < (pfx ++ (hdr ++ rest)).size) :
    (pfx ++ (hdr ++ rest))[pfx.size] = hdr[0] := by
  have := getElem_pfx_hdr pfx hdr rest 0 hk (by omega)
  simp at this; exact this

/-! ## Stored block header abstraction -/

/-- 5-byte stored block header: BFINAL flag, LEN (LE), NLEN (LE). -/
private def storedBlockHdr (blockLen : Nat) (isFinal : Bool) : ByteArray :=
  ByteArray.mk #[if isFinal then 0x01 else 0x00,
    (blockLen.toUInt16 &&& 0xFF).toUInt8,
    ((blockLen.toUInt16 >>> 8) &&& 0xFF).toUInt8,
    ((blockLen.toUInt16 ^^^ 0xFFFF) &&& 0xFF).toUInt8,
    (((blockLen.toUInt16 ^^^ 0xFFFF) >>> 8) &&& 0xFF).toUInt8]

@[simp] private theorem storedBlockHdr_size : (storedBlockHdr n b).size = 5 := rfl

/-! ## Decomposition lemmas for deflateStoredPure -/

/-- In the final case, deflateStoredPure produces storedBlockHdr ++ block data. -/
private theorem deflateStoredPure_eq_final (data : ByteArray) (pos : Nat)
    (hpos : pos ≤ data.size) (h_final : data.size - pos ≤ 65535) :
    deflateStoredPure data pos =
      storedBlockHdr (data.size - pos) true ++ data.extract pos data.size := by
  unfold deflateStoredPure storedBlockHdr
  simp only [show min (data.size - pos) 65535 = data.size - pos from by omega]
  rw [dif_pos (show pos + (data.size - pos) ≥ data.size from by omega)]
  simp only [show pos + (data.size - pos) = data.size from by omega, ↓reduceIte]

/-- In the non-final case, deflateStoredPure produces header ++ 65535-byte block ++ rest. -/
private theorem deflateStoredPure_eq_nonfinal (data : ByteArray) (pos : Nat)
    (hpos : pos ≤ data.size) (h_nonfinal : ¬(data.size - pos ≤ 65535)) :
    deflateStoredPure data pos =
      (storedBlockHdr 65535 false ++ data.extract pos (pos + 65535)) ++
        deflateStoredPure data (pos + 65535) := by
  conv => lhs; unfold deflateStoredPure
  have hneg : ¬(pos + 65535 ≥ data.size) := by omega
  simp only [show min (data.size - pos) 65535 = 65535 from by omega,
    dif_neg hneg, storedBlockHdr, Bool.false_eq_true, ↓reduceIte]

/-! ## Main roundtrip theorem -/

/-- Final block case of inflateLoop_deflateStored. -/
private theorem inflateLoop_deflateStored_final (data : ByteArray) (pos : Nat)
    (hpos : pos ≤ data.size)
    (pfx output : ByteArray) (fixedLit fixedDist : HuffTree)
    (fuel maxOutputSize : Nat)
    (h_fuel : fuel ≥ (data.size - pos + 65535) / 65535)
    (h_fit : output.size + (data.size - pos) ≤ maxOutputSize)
    (h_final : data.size - pos ≤ 65535) :
    ∃ endPos, Inflate.inflateLoop
      { data := pfx ++ deflateStoredPure data pos, pos := pfx.size, bitOff := 0 }
      output fixedLit fixedDist maxOutputSize fuel =
    .ok (output ++ data.extract pos data.size, endPos) := by
  rw [deflateStoredPure_eq_final data pos hpos h_final]
  refine ⟨pfx.size + 5 + (data.size - pos), ?_⟩
  have h_loop := inflateLoop_final_stored
    (pfx ++ (storedBlockHdr (data.size - pos) true ++ data.extract pos data.size))
    pfx.size (data.size - pos) (by omega) output maxOutputSize fixedLit fixedDist fuel
    (by omega) h_fit
    (by simp [ByteArray.size_append, ByteArray.size_extract]; omega)
    (by rw [getElem_pfx_hdr_zero _ _ _ (by simp) (by simp [ByteArray.size_append]; omega)]; rfl)
    (by simp [ByteArray.size_append, ByteArray.size_extract]; omega)
    (by rw [getElem_pfx_hdr _ _ _ 1 (by simp) (by simp [ByteArray.size_append]; omega)]; rfl)
    (by rw [getElem_pfx_hdr _ _ _ 2 (by simp) (by simp [ByteArray.size_append]; omega)]; rfl)
    (by rw [getElem_pfx_hdr _ _ _ 3 (by simp) (by simp [ByteArray.size_append]; omega)]; rfl)
    (by rw [getElem_pfx_hdr _ _ _ 4 (by simp) (by simp [ByteArray.size_append]; omega)]; rfl)
  rw [h_loop]; congr 1; congr 1
  rw [ByteArray.extract_append_ge _ _ _ _ (by omega)]
  simp only [show pfx.size + 5 - pfx.size = 5 from by omega,
    show pfx.size + 5 + (data.size - pos) - pfx.size = 5 + (data.size - pos) from by omega]
  rw [ByteArray.extract_append_ge _ _ _ _ (by simp : (5 : Nat) ≥ (storedBlockHdr (data.size - pos) true).size)]
  simp only [show (5 : Nat) - (storedBlockHdr (data.size - pos) true).size = 0 from by simp,
    show 5 + (data.size - pos) - (storedBlockHdr (data.size - pos) true).size =
      data.size - pos from by simp]
  congr 1
  rw [show data.size - pos = (data.extract pos data.size).size from by
    simp [ByteArray.size_extract]]
  exact ByteArray.extract_zero_size

/-- Step through one non-final stored block via inflateLoop_nonfinal_stored. -/
private theorem inflateLoop_nonfinal_step (data : ByteArray) (pos : Nat)
    (_ : pos ≤ data.size) (pfx output : ByteArray) (fixedLit fixedDist : HuffTree)
    (fuel' maxOutputSize : Nat)
    (h_fit : output.size + (data.size - pos) ≤ maxOutputSize)
    (_ : ¬(data.size - pos ≤ 65535))
    (_ : pos + 65535 ≤ data.size)
    (h_block_sz : (data.extract pos (pos + 65535)).size = 65535) :
    Inflate.inflateLoop
      { data := pfx ++ (storedBlockHdr 65535 false ++
          (data.extract pos (pos + 65535) ++ deflateStoredPure data (pos + 65535))),
        pos := pfx.size, bitOff := 0 }
      output fixedLit fixedDist maxOutputSize (fuel' + 1) =
    Inflate.inflateLoop
      { data := pfx ++ (storedBlockHdr 65535 false ++
          (data.extract pos (pos + 65535) ++ deflateStoredPure data (pos + 65535))),
        pos := pfx.size + 5 + 65535, bitOff := 0 }
      (output ++ (pfx ++ (storedBlockHdr 65535 false ++
          (data.extract pos (pos + 65535) ++ deflateStoredPure data (pos + 65535)))).extract
        (pfx.size + 5) (pfx.size + 5 + 65535))
      fixedLit fixedDist maxOutputSize fuel' := by
  have h_comp_sz : (pfx ++ (storedBlockHdr 65535 false ++
      (data.extract pos (pos + 65535) ++ deflateStoredPure data (pos + 65535)))).size ≥
      pfx.size + 5 + 65535 := by
    simp only [ByteArray.size_append, storedBlockHdr_size, h_block_sz]; omega
  exact inflateLoop_nonfinal_stored
    (pfx ++ (storedBlockHdr 65535 false ++
      (data.extract pos (pos + 65535) ++ deflateStoredPure data (pos + 65535))))
    pfx.size 65535 (by omega)
    output maxOutputSize fixedLit fixedDist fuel' (by omega)
    (by omega)
    (by rw [getElem_pfx_hdr_zero _ _ _ (by simp) (by omega)]; rfl)
    (by omega)
    (by rw [getElem_pfx_hdr _ _ _ 1 (by simp) (by omega)]; rfl)
    (by rw [getElem_pfx_hdr _ _ _ 2 (by simp) (by omega)]; rfl)
    (by rw [getElem_pfx_hdr _ _ _ 3 (by simp) (by omega)]; rfl)
    (by rw [getElem_pfx_hdr _ _ _ 4 (by simp) (by omega)]; rfl)

/-- After stepping one block, simplify the extracted block and restructure for IH. -/
private theorem inflateLoop_nonfinal_after_step (data : ByteArray) (pos : Nat)
    (pfx output : ByteArray) (fixedLit fixedDist : HuffTree)
    (fuel' maxOutputSize : Nat)
    (_ : (data.extract pos (pos + 65535)).size = 65535)
    (h_pos65535 : pos + 65535 ≤ data.size)
    (h_pfx'_sz : (pfx ++ (storedBlockHdr 65535 false ++
        data.extract pos (pos + 65535))).size = pfx.size + 5 + 65535)
    (endPos : Nat)
    (h_ih : Inflate.inflateLoop
      { data := pfx ++ (storedBlockHdr 65535 false ++ data.extract pos (pos + 65535)) ++
          deflateStoredPure data (pos + 65535),
        pos := (pfx ++ (storedBlockHdr 65535 false ++ data.extract pos (pos + 65535))).size,
        bitOff := 0 }
      (output ++ data.extract pos (pos + 65535)) fixedLit fixedDist maxOutputSize fuel' =
    .ok (output ++ data.extract pos (pos + 65535) ++ data.extract (pos + 65535) data.size,
      endPos)) :
    Inflate.inflateLoop
      { data := (pfx ++ (storedBlockHdr 65535 false ++ data.extract pos (pos + 65535))) ++
          deflateStoredPure data (pos + 65535),
        pos := pfx.size + 5 + 65535,
        bitOff := 0 }
      (output ++ data.extract pos (pos + 65535))
      fixedLit fixedDist maxOutputSize fuel' =
    .ok (output ++ data.extract pos data.size, endPos) := by
  rw [← h_pfx'_sz, h_ih, ByteArray.append_assoc,
      ByteArray.extract_append_extract]
  simp [Nat.min_eq_left (Nat.le_add_right pos 65535),
        Nat.max_eq_right h_pos65535]

/-- Restructure data and output after stepping one block.
    Combines extract_block + reassoc so _nonfinal_proof has fewer rw steps. -/
private theorem nonfinal_step_restructure (data : ByteArray) (pos : Nat)
    (pfx output : ByteArray) (fixedLit fixedDist : HuffTree)
    (fuel' maxOutputSize : Nat)
    (h_block_sz : (data.extract pos (pos + 65535)).size = 65535) :
    Inflate.inflateLoop
      { data := pfx ++ (storedBlockHdr 65535 false ++
          (data.extract pos (pos + 65535) ++ deflateStoredPure data (pos + 65535))),
        pos := pfx.size + 5 + 65535, bitOff := 0 }
      (output ++ (pfx ++ (storedBlockHdr 65535 false ++
          (data.extract pos (pos + 65535) ++ deflateStoredPure data (pos + 65535)))).extract
        (pfx.size + 5) (pfx.size + 5 + 65535))
      fixedLit fixedDist maxOutputSize fuel' =
    Inflate.inflateLoop
      { data := (pfx ++ (storedBlockHdr 65535 false ++ data.extract pos (pos + 65535))) ++
          deflateStoredPure data (pos + 65535),
        pos := pfx.size + 5 + 65535,
        bitOff := 0 }
      (output ++ data.extract pos (pos + 65535))
      fixedLit fixedDist maxOutputSize fuel' := by
  generalize deflateStoredPure data (pos + 65535) = rest
  -- Inline nonfinal_extract_block: extract block data from compressed stream
  have h_extract : (pfx ++ (storedBlockHdr 65535 false ++
      ((data.extract pos (pos + 65535)) ++ rest))).extract
      (pfx.size + 5) (pfx.size + 5 + 65535) = data.extract pos (pos + 65535) := by
    rw [ByteArray.extract_append_ge _ _ _ _ (by omega)]
    simp only [show pfx.size + 5 - pfx.size = 5 from by omega,
      show pfx.size + 5 + 65535 - pfx.size = 65540 from by omega]
    rw [ByteArray.extract_append_ge _ _ _ _ (by simp : (5 : Nat) ≥ (storedBlockHdr 65535 false).size)]
    simp only [show (5 : Nat) - (storedBlockHdr 65535 false).size = 0 from by simp,
      show (65540 : Nat) - (storedBlockHdr 65535 false).size = 65535 from by simp]
    have h := ByteArray.extract_append_left (data.extract pos (pos + 65535)) rest
    rw [h_block_sz] at h; exact h
  rw [h_extract]
  -- Inline nonfinal_reassoc: restructure concatenation
  have : storedBlockHdr 65535 false ++ ((data.extract pos (pos + 65535)) ++ rest) =
      (storedBlockHdr 65535 false ++ data.extract pos (pos + 65535)) ++ rest :=
    ByteArray.append_assoc.symm
  rw [this, ← ByteArray.append_assoc]

/-- First half of the nonfinal chain: unfold deflateStoredPure + step one block +
    restructure data. Goes from the original inflateLoop goal to the restructured
    intermediate state (no h_ih needed). -/
private theorem nonfinal_chain_first_half (data : ByteArray) (pos : Nat)
    (hpos : pos ≤ data.size)
    (pfx output : ByteArray) (fixedLit fixedDist : HuffTree)
    (fuel' maxOutputSize : Nat)
    (h_fit : output.size + (data.size - pos) ≤ maxOutputSize)
    (h_final : ¬(data.size - pos ≤ 65535))
    (h_pos65535 : pos + 65535 ≤ data.size)
    (h_block_sz : (data.extract pos (pos + 65535)).size = 65535) :
    Inflate.inflateLoop
      { data := pfx ++ deflateStoredPure data pos, pos := pfx.size, bitOff := 0 }
      output fixedLit fixedDist maxOutputSize (fuel' + 1) =
    Inflate.inflateLoop
      { data := (pfx ++ (storedBlockHdr 65535 false ++ data.extract pos (pos + 65535))) ++
          deflateStoredPure data (pos + 65535),
        pos := pfx.size + 5 + 65535,
        bitOff := 0 }
      (output ++ data.extract pos (pos + 65535))
      fixedLit fixedDist maxOutputSize fuel' := by
  -- Unfold deflateStoredPure (was nonfinal_unfold_goal)
  rw [deflateStoredPure_eq_nonfinal data pos hpos h_final, ByteArray.append_assoc]
  -- Step one block + restructure (was inflateLoop_nonfinal_step.trans nonfinal_step_restructure)
  exact (inflateLoop_nonfinal_step data pos hpos pfx output fixedLit fixedDist
    fuel' maxOutputSize h_fit h_final h_pos65535 h_block_sz).trans
    (nonfinal_step_restructure data pos pfx output fixedLit fixedDist
      fuel' maxOutputSize h_block_sz)

/-- Apply the induction hypothesis for the non-final case. -/
private theorem inflateLoop_deflateStored_apply_ih (data : ByteArray) (pos : Nat)
    (pfx output : ByteArray) (fixedLit fixedDist : HuffTree)
    (fuel' maxOutputSize : Nat)
    (h_pos65535 : pos + 65535 ≤ data.size)
    (h_block_sz : (data.extract pos (pos + 65535)).size = 65535)
    (h_fuel : fuel' + 1 ≥ (data.size - pos + 65535) / 65535)
    (h_fit : output.size + (data.size - pos) ≤ maxOutputSize)
    (_ : ¬(data.size - pos ≤ 65535))
    (ih : ∀ (pos' : Nat), pos' ≤ data.size →
      ∀ (pfx' output' : ByteArray) (fuel' : Nat),
      fuel' ≥ (data.size - pos' + 65535) / 65535 →
      output'.size + (data.size - pos') ≤ maxOutputSize →
      data.size - pos' < data.size - pos →
      ∃ endPos, Inflate.inflateLoop
        { data := pfx' ++ deflateStoredPure data pos', pos := pfx'.size, bitOff := 0 }
        output' fixedLit fixedDist maxOutputSize fuel' =
      .ok (output' ++ data.extract pos' data.size, endPos)) :
    ∃ endPos, Inflate.inflateLoop
      { data := pfx ++ (storedBlockHdr 65535 false ++ data.extract pos (pos + 65535)) ++
          deflateStoredPure data (pos + 65535),
        pos := (pfx ++ (storedBlockHdr 65535 false ++ data.extract pos (pos + 65535))).size,
        bitOff := 0 }
      (output ++ data.extract pos (pos + 65535)) fixedLit fixedDist maxOutputSize fuel' =
    .ok (output ++ data.extract pos (pos + 65535) ++ data.extract (pos + 65535) data.size,
      endPos) := by
  have h_fuel' : fuel' ≥ (data.size - (pos + 65535) + 65535) / 65535 := by
    have : data.size - (pos + 65535) + 65535 = data.size - pos := by omega
    rw [this]; have := Nat.add_div_right (data.size - pos) (by omega : 0 < 65535); omega
  exact ih (pos + 65535) (by omega)
    (pfx ++ (storedBlockHdr 65535 false ++ data.extract pos (pos + 65535)))
    (output ++ data.extract pos (pos + 65535)) fuel' h_fuel'
    (by simp only [ByteArray.size_append, h_block_sz]; omega) (by omega)

/-- Non-final case: takes IH result as bundle. Destructures and applies chain in term mode.
    The chain application (first_half.trans after_step) is inline rather than via a separate
    theorem call, avoiding the additional layer that triggers kernel deep recursion. -/
private theorem inflateLoop_deflateStored_nonfinal_all (data : ByteArray) (pos : Nat)
    (hpos : pos ≤ data.size)
    (pfx output : ByteArray) (fixedLit fixedDist : HuffTree)
    (fuel' maxOutputSize : Nat)
    (h_fit : output.size + (data.size - pos) ≤ maxOutputSize)
    (h_final : ¬(data.size - pos ≤ 65535))
    (h_pos65535 : pos + 65535 ≤ data.size)
    (h_block_sz : (data.extract pos (pos + 65535)).size = 65535)
    (h_pfx'_sz : (pfx ++ (storedBlockHdr 65535 false ++
        data.extract pos (pos + 65535))).size = pfx.size + 5 + 65535)
    (h_ih_bundle : ∃ endPos, Inflate.inflateLoop
      { data := pfx ++ (storedBlockHdr 65535 false ++ data.extract pos (pos + 65535)) ++
          deflateStoredPure data (pos + 65535),
        pos := (pfx ++ (storedBlockHdr 65535 false ++ data.extract pos (pos + 65535))).size,
        bitOff := 0 }
      (output ++ data.extract pos (pos + 65535)) fixedLit fixedDist maxOutputSize fuel' =
    .ok (output ++ data.extract pos (pos + 65535) ++ data.extract (pos + 65535) data.size,
      endPos)) :
    ∃ endPos, Inflate.inflateLoop
      { data := pfx ++ deflateStoredPure data pos, pos := pfx.size, bitOff := 0 }
      output fixedLit fixedDist maxOutputSize (fuel' + 1) =
    .ok (output ++ data.extract pos data.size, endPos) :=
  h_ih_bundle.casesOn fun endPos h_ih =>
    ⟨endPos,
      (nonfinal_chain_first_half data pos hpos pfx output fixedLit fixedDist
        fuel' maxOutputSize h_fit h_final h_pos65535 h_block_sz).trans
      (inflateLoop_nonfinal_after_step data pos pfx output fixedLit fixedDist
        fuel' maxOutputSize h_block_sz h_pos65535 h_pfx'_sz endPos h_ih)⟩

private theorem inflateLoop_deflateStored (data : ByteArray) (pos : Nat)
    (hpos : pos ≤ data.size)
    (pfx output : ByteArray) (fixedLit fixedDist : HuffTree)
    (fuel maxOutputSize : Nat)
    (h_fuel : fuel ≥ (data.size - pos + 65535) / 65535)
    (h_fit : output.size + (data.size - pos) ≤ maxOutputSize) :
    ∃ endPos, Inflate.inflateLoop
      { data := pfx ++ deflateStoredPure data pos, pos := pfx.size, bitOff := 0 }
      output fixedLit fixedDist maxOutputSize fuel =
    .ok (output ++ data.extract pos data.size, endPos) := by
  -- Strong induction on remaining data size
  suffices ∀ n pos (hpos : pos ≤ data.size) pfx output fuel,
      data.size - pos = n →
      fuel ≥ (n + 65535) / 65535 →
      output.size + n ≤ maxOutputSize →
      ∃ endPos, Inflate.inflateLoop
        { data := pfx ++ deflateStoredPure data pos, pos := pfx.size, bitOff := 0 }
        output fixedLit fixedDist maxOutputSize fuel =
      .ok (output ++ data.extract pos data.size, endPos) from
    this _ pos hpos pfx output fuel rfl h_fuel h_fit
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro pos hpos pfx output fuel h_eq h_fuel h_fit
  rw [← h_eq] at h_fuel h_fit
  by_cases h_final : data.size - pos ≤ 65535
  · exact inflateLoop_deflateStored_final data pos hpos pfx output fixedLit fixedDist
      fuel maxOutputSize h_fuel h_fit h_final
  · rw [show fuel = (fuel - 1) + 1 from by omega]
    exact inflateLoop_deflateStored_nonfinal_all data pos hpos pfx output fixedLit fixedDist
      (fuel - 1) maxOutputSize h_fit h_final
      (by omega)
      (by rw [ByteArray.size_extract, Nat.min_eq_left (by omega : pos + 65535 ≤ data.size)]; omega)
      (by simp only [ByteArray.size_append, storedBlockHdr_size,
        ByteArray.size_extract, Nat.min_eq_left (by omega : pos + 65535 ≤ data.size)]; omega)
      (inflateLoop_deflateStored_apply_ih data pos pfx output fixedLit fixedDist
        (fuel - 1) maxOutputSize (by omega)
        (by rw [ByteArray.size_extract, Nat.min_eq_left (by omega : pos + 65535 ≤ data.size)]; omega)
        (by omega) h_fit h_final
        (fun pos' hpos' pfx' output' fuel' hfuel' hfit' hlt =>
          ih (data.size - pos') (by omega) pos' hpos' pfx' output' fuel' rfl hfuel' hfit'))

/-- Native Level 0 roundtrip: compressing with stored blocks then
    decompressing with the native inflate recovers the original data.
    The size constraint ensures the default maxOutputSize (256 MiB) suffices
    and the default fuel (10001 blocks) covers the input. -/
theorem inflate_deflateStoredPure (data : ByteArray)
    (h : data.size ≤ 256 * 1024 * 1024) :
    Inflate.inflate (deflateStoredPure data) = .ok data := by
  simp only [Inflate.inflate, Inflate.inflateRaw, bind, Except.bind]
  -- Handle fromLengths calls
  have ⟨fixedLit, hfl⟩ := fromLengths_fixedLit_ok
  have ⟨fixedDist, hfd⟩ := fromLengths_fixedDist_ok
  simp only [hfl, hfd]
  -- Apply the main loop theorem
  have ⟨endPos, hloop⟩ := inflateLoop_deflateStored data 0 (by omega)
    ByteArray.empty ByteArray.empty fixedLit fixedDist 10001 (256 * 1024 * 1024)
    (by omega) (by simp [ByteArray.size_empty]; omega)
  simp only [ByteArray.empty_append, ByteArray.size_empty] at hloop
  rw [ByteArray.extract_zero_size] at hloop
  rw [hloop]
  simp [pure, Except.pure]

end Zip.Spec.DeflateStoredCorrect
