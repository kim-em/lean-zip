import Zip.Spec.Deflate
import Zip.Native.Inflate

/-!
# DEFLATE Decompressor Correctness

States the main correctness theorem: the native pure-Lean DEFLATE
decompressor (`Zip.Native.Inflate.inflateRaw`) agrees with the formal
bitstream specification (`Deflate.Spec.decode`).

The proof is decomposed into layers matching the decode pipeline:
1. **Bitstream layer**: `BitReader` operations correspond to `bytesToBits` + `readBitsLSB`
2. **Huffman layer**: `HuffTree.decode` corresponds to `Huffman.Spec.decode`
3. **LZ77 layer**: the native copy loop corresponds to `resolveLZ77`
4. **Block layer**: each block type decodes identically
5. **Stream layer**: the block sequence produces the same output
-/

/-! ## Bitstream correspondence

A `BitReader` at position `(pos, bitOff)` in a `ByteArray` corresponds
to the bit list `(bytesToBits data).drop (pos * 8 + bitOff)`.
-/

/-- The spec-level bit list corresponding to a `BitReader`'s current position. -/
def Zip.Native.BitReader.toBits (br : Zip.Native.BitReader) : List Bool :=
  (Deflate.Spec.bytesToBits br.data).drop (br.pos * 8 + br.bitOff)

namespace Deflate.Correctness

/-! ### Helper lemmas for flatMap with uniform-length functions -/

/-- Dropping `n * k` elements from a flatMap with uniform-length-`k` outputs
    skips exactly `n` segments. -/
private theorem flatMap_drop_mul {α β : Type} (l : List α) (f : α → List β)
    (k n : Nat) (hk : ∀ a ∈ l, (f a).length = k) :
    (l.flatMap f).drop (n * k) = (l.drop n).flatMap f := by
  induction n generalizing l with
  | zero => simp
  | succ m ih =>
    cases l with
    | nil => simp
    | cons a rest =>
      simp only [List.flatMap_cons, List.drop_succ_cons]
      have hlen := hk a (List.mem_cons_self ..)
      have hk_eq : (m + 1) * k = (f a).length + m * k := by
        rw [Nat.succ_mul, hlen, Nat.add_comm]
      rw [hk_eq, ← List.drop_drop, List.drop_left]
      exact ih rest (fun b hb => hk b (List.mem_cons_of_mem _ hb))

/-- Dropping within the first segment of a flatMap. -/
private theorem flatMap_cons_drop {α β : Type} (a : α) (rest : List α)
    (f : α → List β) (off : Nat) (hoff : off ≤ (f a).length) :
    ((a :: rest).flatMap f).drop off = (f a).drop off ++ rest.flatMap f :=
  List.drop_append_of_le_length hoff

/-- Dropping `off` elements from `List.ofFn (n := n) f` gives a list
    headed by `f ⟨off, _⟩` when `off < n`. -/
private theorem ofFn_drop_head {n : Nat} {f : Fin n → β} {off : Nat}
    (hoff : off < n) :
    ∃ rest, (List.ofFn f).drop off = f ⟨off, hoff⟩ :: rest := by
  have hlen : off < (List.ofFn f).length := by simp; exact hoff
  rw [List.drop_eq_getElem_cons hlen, List.getElem_ofFn]
  exact ⟨_, rfl⟩

/-- `byteToBits` dropped by `off < 8` starts with `testBit off`. -/
private theorem byteToBits_drop_head (b : UInt8) (off : Nat) (hoff : off < 8) :
    ∃ rest, (Deflate.Spec.bytesToBits.byteToBits b).drop off =
      b.toNat.testBit off :: rest := by
  exact ofFn_drop_head hoff

/-- The key structural lemma: `bytesToBits data` dropped by `pos * 8 + off`
    starts with `data[pos].toNat.testBit off`. -/
private theorem bytesToBits_drop_testBit (data : ByteArray) (pos off : Nat)
    (hpos : pos < data.size) (hoff : off < 8) :
    ∃ rest, (Deflate.Spec.bytesToBits data).drop (pos * 8 + off) =
      data[pos].toNat.testBit off :: rest := by
  simp only [Deflate.Spec.bytesToBits]
  -- Step 1: split drop (pos * 8 + off) into drop off ∘ drop (pos * 8)
  rw [← List.drop_drop]
  -- Step 2: drop (pos * 8) skips pos complete 8-bit segments
  rw [flatMap_drop_mul data.data.toList _ 8 pos
    (fun b _ => Deflate.Spec.bytesToBits.byteToBits_length b)]
  -- Step 3: data.data.toList.drop pos = data[pos] :: tail
  have hlen : pos < data.data.toList.length := by
    rw [Array.length_toList]; exact hpos
  rw [List.drop_eq_getElem_cons hlen]
  -- Step 4: drop off within first segment
  rw [flatMap_cons_drop _ _ _ off
    (by rw [Deflate.Spec.bytesToBits.byteToBits_length]; omega)]
  -- Step 5: head of (byteToBits data[pos]).drop off is testBit off
  have heq : data.data.toList[pos] = data[pos] := by
    simp [Array.getElem_toList]; rfl
  obtain ⟨tail, htail⟩ := byteToBits_drop_head (data.data.toList[pos]) off hoff
  rw [htail, heq]; exact ⟨_, rfl⟩

/-! ### Bit-value correspondence -/

private theorem shift_and_one_eq_testBit (n i : Nat) :
    (n >>> i) &&& 1 = if n.testBit i then 1 else 0 := by
  simp only [Nat.testBit, Nat.and_comm (n >>> i) 1, Nat.one_and_eq_mod_two, bne_iff_ne]
  split <;> omega

private theorem uint32_bit_eq_testBit (byte : UInt8) (off : Nat) (hoff : off < 8) :
    ((byte.toUInt32 >>> off.toUInt32) &&& 1) =
      if byte.toNat.testBit off then 1 else 0 := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_and, UInt32.toNat_shiftRight, UInt8.toNat_toUInt32]
  have hoff_eq : off.toUInt32.toNat % 32 = off := by simp [Nat.toUInt32]; omega
  rw [hoff_eq]
  have : UInt32.toNat 1 = 1 := by decide
  rw [this, shift_and_one_eq_testBit]
  split <;> simp

private theorem list_drop_cons_tail {l : List α} {a : α} {rest : List α} {n : Nat}
    (h : l.drop n = a :: rest) : rest = l.drop (n + 1) := by
  have : l.drop (n + 1) = (l.drop n).drop 1 := by rw [List.drop_drop, Nat.add_comm]
  rw [this, h, List.drop_one, List.tail_cons]

/-- `readBit` preserves the well-formedness invariant `bitOff < 8`. -/
theorem readBit_wf (br : Zip.Native.BitReader) (bit : UInt32)
    (br' : Zip.Native.BitReader) (hwf : br.bitOff < 8)
    (h : br.readBit = .ok (bit, br')) : br'.bitOff < 8 := by
  simp only [Zip.Native.BitReader.readBit] at h
  split at h
  · simp at h
  · split at h <;> simp only [Except.ok.injEq, Prod.mk.injEq] at h
    · obtain ⟨_, rfl⟩ := h; simp
    · obtain ⟨_, rfl⟩ := h; simp; omega

/-! ### readBit correspondence -/

/-- Reading a single bit from the `BitReader` corresponds to consuming
    the head of the corresponding bit list. Requires `bitOff < 8`. -/
theorem readBit_toBits (br : Zip.Native.BitReader)
    (bit : UInt32) (br' : Zip.Native.BitReader)
    (hwf : br.bitOff < 8)
    (h : br.readBit = .ok (bit, br')) :
    ∃ b rest,
      br.toBits = b :: rest ∧
      br'.toBits = rest ∧
      bit = if b then 1 else 0 := by
  -- Unfold readBit; the error case is impossible since h says it succeeded
  simp only [Zip.Native.BitReader.readBit] at h
  split at h
  · simp at h
  · rename_i hpos
    -- hpos : ¬(br.pos ≥ br.data.size), so br.pos < br.data.size
    have hpos' : br.pos < br.data.size := by omega
    -- Get the bit list structure from bytesToBits_drop_testBit
    obtain ⟨rest, hrest⟩ := bytesToBits_drop_testBit br.data br.pos br.bitOff hpos' hwf
    have hrest_eq : rest =
        (Deflate.Spec.bytesToBits br.data).drop (br.pos * 8 + br.bitOff + 1) :=
      list_drop_cons_tail hrest
    -- The bit read by readBit matches data[pos]! which equals data[pos]
    have hget : br.data[br.pos]! = br.data[br.pos] := by simp [hpos']
    refine ⟨br.data[br.pos].toNat.testBit br.bitOff, rest, hrest, ?_, ?_⟩
    · -- br'.toBits = rest
      split at h <;> simp only [Except.ok.injEq, Prod.mk.injEq] at h
      · obtain ⟨_, rfl⟩ := h
        simp only [Zip.Native.BitReader.toBits, hrest_eq]; congr 1; omega
      · obtain ⟨_, rfl⟩ := h
        simp only [Zip.Native.BitReader.toBits, hrest_eq]; congr 1
    · -- bit = if testBit then 1 else 0 (same in both bitOff cases)
      split at h <;> simp only [Except.ok.injEq, Prod.mk.injEq] at h
      all_goals (obtain ⟨rfl, _⟩ := h; rw [hget];
                 exact uint32_bit_eq_testBit br.data[br.pos] br.bitOff hwf)

/-- Reading `n` bits via `BitReader.readBits` corresponds to
    `readBitsLSB n` on the spec bit list.
    Requires `bitOff < 8` (well-formedness) and `n ≤ 32` (UInt32 shift
    correctness — native `readBits.go` uses `bit <<< shift.toUInt32`
    where `UInt32.shiftLeft` reduces shift mod 32). -/
theorem readBits_toBits (br : Zip.Native.BitReader)
    (n : Nat) (val : UInt32) (br' : Zip.Native.BitReader)
    (hwf : br.bitOff < 8) (hn : n ≤ 32)
    (h : br.readBits n = .ok (val, br')) :
    ∃ rest,
      Deflate.Spec.readBitsLSB n br.toBits = some (val.toNat, rest) ∧
      br'.toBits = rest := by
  sorry

/-! ## Huffman decode correspondence -/

/-- A `HuffTree` built from code lengths decodes the same symbol as the
    spec's `Huffman.Spec.decode` on the corresponding code table.
    Requires `bitOff < 8` because the proof traces through individual
    `readBit` calls via `readBit_toBits`. -/
theorem huffTree_decode_correct (lengths : Array UInt8)
    (tree : Zip.Native.HuffTree) (br : Zip.Native.BitReader)
    (sym : UInt16) (br' : Zip.Native.BitReader)
    (hwf : br.bitOff < 8)
    (htree : Zip.Native.HuffTree.fromLengths lengths = .ok tree)
    (hdecode : tree.decode br = .ok (sym, br')) :
    let specLengths := lengths.toList.map UInt8.toNat
    let specCodes := Huffman.Spec.allCodes specLengths
    let specTable := specCodes.map fun (s, cw) => (cw, s)
    ∃ rest,
      Huffman.Spec.decode specTable br.toBits = some (sym.toNat, rest) ∧
      br'.toBits = rest := by
  sorry

/-! ## Main correctness theorem -/

/-- **Main theorem**: If the native DEFLATE decompressor succeeds, then
    the formal specification also succeeds and produces the same output.

    The native decompressor `inflateRaw` processes a `ByteArray` starting
    at byte offset `startPos`, reads DEFLATE blocks until a final block,
    and returns the decompressed data with the ending byte position.

    The spec `decode` converts the same data to a bit list via
    `bytesToBits`, decodes blocks according to RFC 1951, and returns
    the decompressed output as a `List UInt8`.

    The existential over `fuel` accounts for the fuel-based termination
    in the spec's decode function. The native implementation uses bounded
    loops (at most 10001 blocks) that correspond to the spec's fuel. -/
theorem inflate_correct (data : ByteArray) (startPos maxOutputSize : Nat)
    (result : ByteArray) (endPos : Nat)
    (h : Zip.Native.Inflate.inflateRaw data startPos maxOutputSize =
      .ok (result, endPos)) :
    ∃ fuel,
      Deflate.Spec.decode
        ((Deflate.Spec.bytesToBits data).drop (startPos * 8)) fuel =
        some result.data.toList := by
  sorry

/-- Corollary: `inflate` (which starts at position 0) agrees with
    `decodeBytes` (which also starts at position 0). -/
theorem inflate_correct' (data : ByteArray) (maxOutputSize : Nat)
    (result : ByteArray)
    (h : Zip.Native.Inflate.inflate data maxOutputSize = .ok result) :
    ∃ fuel,
      Deflate.Spec.decode (Deflate.Spec.bytesToBits data) fuel =
        some result.data.toList := by
  sorry

end Deflate.Correctness
