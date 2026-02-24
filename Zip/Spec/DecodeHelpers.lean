import Zip.Spec.HuffmanCorrect
import Zip.Spec.BitstreamComplete

/-!
# Decode Helper Lemmas

Well-formedness/position invariants, table correspondence lemmas, and
copy loop helpers used by both the forward (DecodeCorrect) and reverse
(completeness) proofs of DEFLATE block-level decode.

Extracted from DecodeCorrect.lean to keep file sizes manageable.
-/

namespace Deflate.Correctness

/-! ## Well-formedness and position invariants -/

/-- `HuffTree.decode` preserves the well-formedness invariant `bitOff < 8`. -/
theorem decode_wf (tree : Zip.Native.HuffTree)
    (br : Zip.Native.BitReader) (sym : UInt16) (br' : Zip.Native.BitReader)
    (hwf : br.bitOff < 8)
    (h : tree.decode br = .ok (sym, br')) : br'.bitOff < 8 := by
  have hgo : Zip.Native.HuffTree.decode.go tree br 0 = .ok (sym, br') := by
    simp only [Zip.Native.HuffTree.decode] at h; exact h
  exact (Deflate.Correctness.decode_go_decodeBits tree br 0 sym br' hwf hgo).2

/-- `readBit` preserves the position invariant `bitOff = 0 ∨ pos < data.size`. -/
private theorem readBit_pos_inv (br : Zip.Native.BitReader)
    (bit : UInt32) (br' : Zip.Native.BitReader)
    (h : br.readBit = .ok (bit, br')) :
    br'.bitOff = 0 ∨ br'.pos < br'.data.size := by
  simp only [Zip.Native.BitReader.readBit] at h
  split at h
  · simp at h
  · rename_i hpos
    split at h <;> simp only [Except.ok.injEq, Prod.mk.injEq] at h
    · obtain ⟨_, rfl⟩ := h; simp_all
    · obtain ⟨_, rfl⟩ := h; simp; omega

/-- `readBits.go` preserves the position invariant. -/
private theorem readBits_go_pos_inv (br : Zip.Native.BitReader)
    (acc : UInt32) (shift k : Nat) (val : UInt32)
    (br' : Zip.Native.BitReader)
    (hwf : br.bitOff < 8)
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (h : Zip.Native.BitReader.readBits.go br acc shift k = .ok (val, br')) :
    br'.bitOff = 0 ∨ br'.pos < br'.data.size := by
  induction k generalizing br acc shift with
  | zero =>
    simp only [Zip.Native.BitReader.readBits.go] at h
    obtain ⟨_, rfl⟩ := Except.ok.inj h; exact hpos
  | succ k ih =>
    simp only [Zip.Native.BitReader.readBits.go, bind, Except.bind] at h
    cases hrd : br.readBit with
    | error e => simp [hrd] at h
    | ok p =>
      obtain ⟨bit, br₁⟩ := p
      simp only [hrd] at h
      exact ih br₁ _ _ (readBit_wf br bit br₁ hwf hrd)
        (readBit_pos_inv br bit br₁ hrd) h

/-- `readBits` preserves the position invariant. -/
theorem readBits_pos_inv (br : Zip.Native.BitReader)
    (n : Nat) (val : UInt32) (br' : Zip.Native.BitReader)
    (hwf : br.bitOff < 8)
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (h : br.readBits n = .ok (val, br')) :
    br'.bitOff = 0 ∨ br'.pos < br'.data.size := by
  simp only [Zip.Native.BitReader.readBits] at h
  exact readBits_go_pos_inv br 0 0 n val br' hwf hpos h

/-- `HuffTree.decode.go` preserves the position invariant. -/
private theorem decode_go_pos_inv (tree : Zip.Native.HuffTree)
    (br : Zip.Native.BitReader) (n : Nat) (sym : UInt16)
    (br' : Zip.Native.BitReader)
    (hwf : br.bitOff < 8)
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (h : Zip.Native.HuffTree.decode.go tree br n = .ok (sym, br')) :
    br'.bitOff = 0 ∨ br'.pos < br'.data.size := by
  induction tree generalizing br n with
  | leaf s =>
    simp only [Zip.Native.HuffTree.decode.go] at h
    obtain ⟨_, rfl⟩ := Except.ok.inj h; exact hpos
  | empty => simp only [Zip.Native.HuffTree.decode.go] at h; simp at h
  | node z o ihz iho =>
    simp only [Zip.Native.HuffTree.decode.go] at h
    split at h
    · simp at h
    · simp only [bind, Except.bind] at h
      cases hrd : br.readBit with
      | error e => simp [hrd] at h
      | ok p =>
        obtain ⟨bit, br₁⟩ := p
        simp only [hrd] at h
        have hwf₁ := readBit_wf br bit br₁ hwf hrd
        have hpos₁ := readBit_pos_inv br bit br₁ hrd
        split at h
        · exact ihz br₁ _ hwf₁ hpos₁ h
        · exact iho br₁ _ hwf₁ hpos₁ h

/-- `HuffTree.decode` preserves the position invariant. -/
theorem decode_pos_inv (tree : Zip.Native.HuffTree)
    (br : Zip.Native.BitReader) (sym : UInt16) (br' : Zip.Native.BitReader)
    (hwf : br.bitOff < 8)
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (h : tree.decode br = .ok (sym, br')) :
    br'.bitOff = 0 ∨ br'.pos < br'.data.size := by
  have hgo : Zip.Native.HuffTree.decode.go tree br 0 = .ok (sym, br') := by
    simp only [Zip.Native.HuffTree.decode] at h; exact h
  exact decode_go_pos_inv tree br 0 sym br' hwf hpos hgo

/-- `readBits.go` preserves the well-formedness invariant `bitOff < 8`. -/
private theorem readBits_go_wf (br : Zip.Native.BitReader)
    (acc : UInt32) (shift k : Nat) (val : UInt32) (br' : Zip.Native.BitReader)
    (hwf : br.bitOff < 8)
    (h : Zip.Native.BitReader.readBits.go br acc shift k = .ok (val, br')) :
    br'.bitOff < 8 := by
  induction k generalizing br acc shift with
  | zero =>
    simp only [Zip.Native.BitReader.readBits.go] at h
    obtain ⟨_, rfl⟩ := Except.ok.inj h; exact hwf
  | succ k ih =>
    simp only [Zip.Native.BitReader.readBits.go, bind, Except.bind] at h
    cases hrd : br.readBit with
    | error e => simp [hrd] at h
    | ok p =>
      obtain ⟨bit, br₁⟩ := p
      simp only [hrd] at h
      exact ih br₁ _ _ (readBit_wf br bit br₁ hwf hrd) h

/-- `readBits` preserves the well-formedness invariant `bitOff < 8`. -/
theorem readBits_wf (br : Zip.Native.BitReader)
    (n : Nat) (val : UInt32) (br' : Zip.Native.BitReader)
    (hwf : br.bitOff < 8)
    (h : br.readBits n = .ok (val, br')) : br'.bitOff < 8 := by
  simp only [Zip.Native.BitReader.readBits] at h
  exact readBits_go_wf br 0 0 n val br' hwf h

/-! ## Table correspondence lemmas -/

set_option maxRecDepth 1024 in
protected theorem lengthBase_eq : ∀ i : Fin 29,
    (Zip.Native.Inflate.lengthBase[i.val]!).toNat =
    (Deflate.Spec.lengthBase[i.val]!) := by decide

set_option maxRecDepth 1024 in
protected theorem lengthExtra_eq : ∀ i : Fin 29,
    (Zip.Native.Inflate.lengthExtra[i.val]!).toNat =
    (Deflate.Spec.lengthExtra[i.val]!) := by decide

set_option maxRecDepth 1024 in
protected theorem distBase_eq : ∀ i : Fin 30,
    (Zip.Native.Inflate.distBase[i.val]!).toNat =
    (Deflate.Spec.distBase[i.val]!) := by decide

set_option maxRecDepth 1024 in
protected theorem distExtra_eq : ∀ i : Fin 30,
    (Zip.Native.Inflate.distExtra[i.val]!).toNat =
    (Deflate.Spec.distExtra[i.val]!) := by decide

set_option maxRecDepth 1024 in
protected theorem lengthExtra_le_32 : ∀ i : Fin 29,
    (Zip.Native.Inflate.lengthExtra[i.val]!).toNat ≤ 32 := by decide

set_option maxRecDepth 1024 in
protected theorem distExtra_le_32 : ∀ i : Fin 30,
    (Zip.Native.Inflate.distExtra[i.val]!).toNat ≤ 32 := by decide

set_option maxRecDepth 1024 in
protected theorem spec_distBase_pos : ∀ i : Fin 30,
    (Deflate.Spec.distBase[i.val]!) ≥ 1 := by decide

/-- `arr[i]? = some arr[i]!` when `i` is in bounds.
    Combines `getElem!_pos` and `getElem?_pos` into a single step. -/
protected theorem getElem?_eq_some_getElem! [Inhabited α] (arr : Array α) (i : Nat)
    (h : i < arr.size) : arr[i]? = some arr[i]! := by
  rw [getElem!_pos arr i h]; exact getElem?_pos arr i h

/-! ## Copy loop helpers -/

/-- `ba[j]!` equals `ba.data.toList[j]!` when `j` is in bounds. -/
private theorem ba_getElem!_eq_toList (ba : ByteArray) (j : Nat) (hj : j < ba.size) :
    ba[j]! = ba.data.toList[j]! := by
  rw [getElem!_pos ba j hj,
      getElem!_pos ba.data.toList j (by simp [Array.length_toList, ByteArray.size_data]; exact hj)]
  show ba.data[j] = ba.data.toList[j]
  rw [Array.getElem_toList]

/-- `ByteArray.push` preserves earlier elements: for `j < buf.size`,
    `(buf.push b)[j]! = buf[j]!`. -/
private theorem push_getElem_lt (buf : ByteArray) (b : UInt8) (j : Nat)
    (hj : j < buf.size) :
    (buf.push b)[j]! = buf[j]! := by
  have hj' : j < (buf.push b).size := by simp [ByteArray.size_push]; omega
  rw [getElem!_pos (buf.push b) j hj', getElem!_pos buf j hj]
  exact Array.getElem_push_lt hj

/-- `ByteArray.push` appends one element to `data.toList`. -/
private theorem push_data_toList (buf : ByteArray) (b : UInt8) :
    (buf.push b).data.toList = buf.data.toList ++ [b] := by
  simp [ByteArray.push, Array.toList_push]

/-- Generalized loop invariant for `copyLoop`. After running from index
    `k`, the result has the original buffer contents plus `List.ofFn` of
    the remaining elements. -/
private theorem copyLoop_spec (output : ByteArray) (start distance : Nat)
    (k length : Nat) (buf : ByteArray)
    (hd_pos : distance > 0)
    (hstart : start + distance ≤ output.size)
    (hk_le : k ≤ length)
    (hbuf_size : buf.size = output.size + k)
    (hbuf_prefix : ∀ j, j < output.size → buf[j]! = output[j]!)
    (hbuf_data : buf.data.toList = output.data.toList ++
      List.ofFn (fun (i : Fin k) =>
        output.data.toList[start + (i.val % distance)]!)) :
    (Zip.Native.Inflate.copyLoop buf start distance k length).data.toList =
      output.data.toList ++
      List.ofFn (fun (i : Fin length) =>
        output.data.toList[start + (i.val % distance)]!) := by
  unfold Zip.Native.Inflate.copyLoop
  split
  · rename_i hk_lt
    have hmod_lt : k % distance < distance := Nat.mod_lt k hd_pos
    have hidx_lt : start + (k % distance) < output.size := by omega
    have hnew_eq : buf[start + (k % distance)]! = output[start + (k % distance)]! :=
      hbuf_prefix _ hidx_lt
    apply copyLoop_spec output start distance (k + 1) length
    · exact hd_pos
    · exact hstart
    · omega
    · simp [ByteArray.size_push]; omega
    · intro j hj
      rw [push_getElem_lt _ _ _ (by rw [hbuf_size]; omega)]
      exact hbuf_prefix j hj
    · rw [push_data_toList, hbuf_data, List.append_assoc]
      congr 1
      rw [hnew_eq, ba_getElem!_eq_toList _ _ hidx_lt]
      symm
      exact List.ofFn_succ_last
  · rename_i hk_nlt
    have hk_eq : k = length := by omega
    subst hk_eq
    exact hbuf_data
termination_by length - k

/-- The native copy loop produces the same result as the spec's `List.ofFn`
    for LZ77 back-references. -/
protected theorem copyLoop_eq_ofFn
    (output : ByteArray) (length distance : Nat)
    (hd_pos : distance > 0) (hd_le : distance ≤ output.size) :
    (Zip.Native.Inflate.copyLoop output (output.size - distance) distance
      0 length).data.toList =
    output.data.toList ++
      List.ofFn (fun (i : Fin length) =>
        output.data.toList[(output.size - distance) +
          (i.val % distance)]!) := by
  exact copyLoop_spec output (output.size - distance) distance 0 length output
    hd_pos (by omega) (Nat.zero_le _) rfl (fun _ _ => rfl) (by simp [List.ofFn])

end Deflate.Correctness
