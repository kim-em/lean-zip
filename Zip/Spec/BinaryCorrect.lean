import Zip.Binary
import Std.Tactic.BVDecide

/-!
# Binary LE read/write roundtrip proofs

Roundtrip correctness theorems for the `Binary` module's little-endian
integer read/write operations. Building blocks for gzip/zlib framing
roundtrip proofs.
-/

namespace Binary

-- Helper lemmas for reducing getElem! on literal ByteArrays

private theorem ba2_getElem!_0 (a b : UInt8) :
    (ByteArray.mk #[a, b])[0]! = a := rfl

private theorem ba2_getElem!_1 (a b : UInt8) :
    (ByteArray.mk #[a, b])[0 + 1]! = b := rfl

private theorem ba4_getElem!_0 (a b c d : UInt8) :
    (ByteArray.mk #[a, b, c, d])[0]! = a := rfl

private theorem ba4_getElem!_1 (a b c d : UInt8) :
    (ByteArray.mk #[a, b, c, d])[0 + 1]! = b := rfl

private theorem ba4_getElem!_2 (a b c d : UInt8) :
    (ByteArray.mk #[a, b, c, d])[0 + 2]! = c := rfl

private theorem ba4_getElem!_3 (a b c d : UInt8) :
    (ByteArray.mk #[a, b, c, d])[0 + 3]! = d := rfl

/-! ## UInt16 roundtrip -/

theorem readUInt16LE_writeUInt16LE (val : UInt16) :
    readUInt16LE (writeUInt16LE val) 0 = val := by
  simp only [readUInt16LE, writeUInt16LE, ba2_getElem!_0, ba2_getElem!_1]
  bv_decide

/-! ## UInt32 roundtrip -/

theorem readUInt32LE_writeUInt32LE (val : UInt32) :
    readUInt32LE (writeUInt32LE val) 0 = val := by
  simp only [readUInt32LE, writeUInt32LE,
    ba4_getElem!_0, ba4_getElem!_1, ba4_getElem!_2, ba4_getElem!_3]
  bv_decide

/-- Inline-byte variant matching the gzip/zlib encoder pattern. -/
theorem readUInt32LE_bytes (v : UInt32) :
    readUInt32LE (ByteArray.mk #[
      (v &&& 0xFF).toUInt8, ((v >>> 8) &&& 0xFF).toUInt8,
      ((v >>> 16) &&& 0xFF).toUInt8, ((v >>> 24) &&& 0xFF).toUInt8]) 0 = v := by
  simp only [readUInt32LE,
    ba4_getElem!_0, ba4_getElem!_1, ba4_getElem!_2, ba4_getElem!_3]
  bv_decide

/-! ## Concatenation-aware variants -/

/-- `getElem!` on a concatenated ByteArray reads from the left part when in bounds. -/
private theorem getElem!_append_left (a b : ByteArray) (i : Nat) (h : i < a.size) :
    (a ++ b)[i]! = a[i]! := by
  rw [getElem!_pos (a ++ b) i (by simp [ByteArray.size_append]; omega),
      getElem!_pos a i h]
  exact ByteArray.getElem_append_left h

/-- `getElem!` on a concatenated ByteArray reads from the right part at offset `a.size`. -/
private theorem getElem!_append_right (a b : ByteArray) (i : Nat) (h : i < b.size) :
    (a ++ b)[a.size + i]! = b[i]! := by
  rw [getElem!_pos (a ++ b) (a.size + i) (by simp [ByteArray.size_append]; omega),
      getElem!_pos b i h]
  have hle : a.size ≤ a.size + i := Nat.le_add_right _ _
  rw [ByteArray.getElem_append_right hle]
  congr 1
  omega

theorem readUInt32LE_append_left (a b : ByteArray) (offset : Nat)
    (h : offset + 4 ≤ a.size) :
    readUInt32LE (a ++ b) offset = readUInt32LE a offset := by
  unfold readUInt32LE
  rw [getElem!_append_left a b offset (by omega),
      getElem!_append_left a b (offset + 1) (by omega),
      getElem!_append_left a b (offset + 2) (by omega),
      getElem!_append_left a b (offset + 3) (by omega)]

theorem readUInt32LE_append_right (a b : ByteArray) (offset : Nat)
    (h : offset + 4 ≤ b.size) :
    readUInt32LE (a ++ b) (a.size + offset) = readUInt32LE b offset := by
  unfold readUInt32LE
  rw [show a.size + offset + 1 = a.size + (offset + 1) from by omega,
      show a.size + offset + 2 = a.size + (offset + 2) from by omega,
      show a.size + offset + 3 = a.size + (offset + 3) from by omega,
      getElem!_append_right a b offset (by omega),
      getElem!_append_right a b (offset + 1) (by omega),
      getElem!_append_right a b (offset + 2) (by omega),
      getElem!_append_right a b (offset + 3) (by omega)]

theorem readUInt16LE_append_left (a b : ByteArray) (offset : Nat)
    (h : offset + 2 ≤ a.size) :
    readUInt16LE (a ++ b) offset = readUInt16LE a offset := by
  unfold readUInt16LE
  rw [getElem!_append_left a b offset (by omega),
      getElem!_append_left a b (offset + 1) (by omega)]

theorem readUInt16LE_append_right (a b : ByteArray) (offset : Nat)
    (h : offset + 2 ≤ b.size) :
    readUInt16LE (a ++ b) (a.size + offset) = readUInt16LE b offset := by
  unfold readUInt16LE
  rw [show a.size + offset + 1 = a.size + (offset + 1) from by omega,
      getElem!_append_right a b offset (by omega),
      getElem!_append_right a b (offset + 1) (by omega)]

end Binary
