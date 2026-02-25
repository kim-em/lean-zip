import Zip.Binary
import ZipForStd.ByteArray
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

theorem ba4_getElem!_0 (a b c d : UInt8) :
    (ByteArray.mk #[a, b, c, d])[0]! = a := rfl

theorem ba4_getElem!_1 (a b c d : UInt8) :
    (ByteArray.mk #[a, b, c, d])[0 + 1]! = b := rfl

theorem ba4_getElem!_2 (a b c d : UInt8) :
    (ByteArray.mk #[a, b, c, d])[0 + 2]! = c := rfl

theorem ba4_getElem!_3 (a b c d : UInt8) :
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
theorem getElem!_append_left (a b : ByteArray) (i : Nat) (h : i < a.size) :
    (a ++ b)[i]! = a[i]! := by
  rw [getElem!_pos (a ++ b) i (by simp [ByteArray.size_append]; omega),
      getElem!_pos a i h]
  exact ByteArray.getElem_append_left h

/-- `getElem!` on a concatenated ByteArray reads from the right part at offset `a.size`. -/
theorem getElem!_append_right (a b : ByteArray) (i : Nat) (h : i < b.size) :
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

/-! ## Size lemmas -/

@[simp] theorem writeUInt32LE_size (v : UInt32) : (writeUInt32LE v).size = 4 := rfl

@[simp] theorem writeUInt16LE_size (v : UInt16) : (writeUInt16LE v).size = 2 := rfl

/-! ## UInt64 roundtrip -/

theorem readUInt64LE_writeUInt64LE (val : UInt64) :
    readUInt64LE (writeUInt64LE val) 0 = val := by
  simp only [readUInt64LE, writeUInt64LE]
  rw [readUInt32LE_append_left _ _ 0 (by simp),
      readUInt32LE_writeUInt32LE,
      show 0 + 4 = (writeUInt32LE val.toUInt32).size + 0 from by simp,
      readUInt32LE_append_right _ _ 0 (by simp),
      readUInt32LE_writeUInt32LE]
  bv_decide

/-! ## Triple-append indexing -/

/-- Index into the left part of a triple concatenation. -/
theorem getElem!_append3_left (a b c : ByteArray) (i : Nat) (h : i < a.size) :
    (a ++ b ++ c)[i]! = a[i]! := by
  rw [getElem!_append_left (a ++ b) c i (by simp [ByteArray.size_append]; omega),
      getElem!_append_left a b i h]

/-- Index into the middle part of a triple concatenation. -/
theorem getElem!_append3_mid (a b c : ByteArray) (i : Nat) (h : i < b.size) :
    (a ++ b ++ c)[a.size + i]! = b[i]! := by
  rw [getElem!_append_left (a ++ b) c (a.size + i) (by simp [ByteArray.size_append]; omega),
      getElem!_append_right a b i h]

/-- Index into the right part of a triple concatenation. -/
theorem getElem!_append3_right (a b c : ByteArray) (i : Nat) (h : i < c.size) :
    (a ++ b ++ c)[a.size + b.size + i]! = c[i]! := by
  rw [show a.size + b.size + i = (a ++ b).size + i from by simp [ByteArray.size_append],
      getElem!_append_right (a ++ b) c i h]

/-! ## Triple-append read lemmas -/

/-- Read UInt32LE from the middle part of a triple concatenation. -/
theorem readUInt32LE_append3_mid (a b c : ByteArray) (offset : Nat)
    (h : offset + 4 ≤ b.size) :
    readUInt32LE (a ++ b ++ c) (a.size + offset) = readUInt32LE b offset := by
  unfold readUInt32LE
  rw [show a.size + offset + 1 = a.size + (offset + 1) from by omega,
      show a.size + offset + 2 = a.size + (offset + 2) from by omega,
      show a.size + offset + 3 = a.size + (offset + 3) from by omega,
      getElem!_append3_mid a b c offset (by omega),
      getElem!_append3_mid a b c (offset + 1) (by omega),
      getElem!_append3_mid a b c (offset + 2) (by omega),
      getElem!_append3_mid a b c (offset + 3) (by omega)]

/-- Read UInt32LE from the right part of a triple concatenation. -/
theorem readUInt32LE_append3_right (a b c : ByteArray) (offset : Nat)
    (h : offset + 4 ≤ c.size) :
    readUInt32LE (a ++ b ++ c) (a.size + b.size + offset) = readUInt32LE c offset := by
  unfold readUInt32LE
  rw [show a.size + b.size + offset + 1 = a.size + b.size + (offset + 1) from by omega,
      show a.size + b.size + offset + 2 = a.size + b.size + (offset + 2) from by omega,
      show a.size + b.size + offset + 3 = a.size + b.size + (offset + 3) from by omega,
      getElem!_append3_right a b c offset (by omega),
      getElem!_append3_right a b c (offset + 1) (by omega),
      getElem!_append3_right a b c (offset + 2) (by omega),
      getElem!_append3_right a b c (offset + 3) (by omega)]

/-! ## Big-endian UInt32 roundtrip (for zlib Adler32 trailer) -/

/-- Inline big-endian byte roundtrip matching the zlib encoder Adler32 pattern. -/
theorem readUInt32BE_bytes (v : UInt32) :
    let b := ByteArray.mk #[
      ((v >>> 24) &&& 0xFF).toUInt8, ((v >>> 16) &&& 0xFF).toUInt8,
      ((v >>> 8) &&& 0xFF).toUInt8, (v &&& 0xFF).toUInt8]
    (b[0]!.toUInt32 <<< 24) ||| (b[1]!.toUInt32 <<< 16) |||
    (b[2]!.toUInt32 <<< 8) ||| b[3]!.toUInt32 = v := by
  simp only [ba4_getElem!_0, ba4_getElem!_1, ba4_getElem!_2, ba4_getElem!_3]
  bv_decide

/-- Big-endian read from a concatenated ByteArray at an offset into the right part. -/
theorem readUInt32BE_append_right (a b : ByteArray) (offset : Nat)
    (h : offset + 4 ≤ b.size) :
    let c := a ++ b
    (c[a.size + offset]!.toUInt32 <<< 24) |||
    (c[a.size + offset + 1]!.toUInt32 <<< 16) |||
    (c[a.size + offset + 2]!.toUInt32 <<< 8) |||
    c[a.size + offset + 3]!.toUInt32 =
    (b[offset]!.toUInt32 <<< 24) |||
    (b[offset + 1]!.toUInt32 <<< 16) |||
    (b[offset + 2]!.toUInt32 <<< 8) |||
    b[offset + 3]!.toUInt32 := by
  simp only
  rw [show a.size + offset + 1 = a.size + (offset + 1) from by omega,
      show a.size + offset + 2 = a.size + (offset + 2) from by omega,
      show a.size + offset + 3 = a.size + (offset + 3) from by omega,
      getElem!_append_right a b offset (by omega),
      getElem!_append_right a b (offset + 1) (by omega),
      getElem!_append_right a b (offset + 2) (by omega),
      getElem!_append_right a b (offset + 3) (by omega)]

/-! ## In-place write size preservation -/

theorem writeUInt16LEAt_size (buf : ByteArray) (offset : Nat) (val : UInt16) :
    (writeUInt16LEAt buf offset val).size = buf.size := by
  unfold writeUInt16LEAt
  rw [ByteArray.size_set!, ByteArray.size_set!]

theorem writeUInt32LEAt_size (buf : ByteArray) (offset : Nat) (val : UInt32) :
    (writeUInt32LEAt buf offset val).size = buf.size := by
  unfold writeUInt32LEAt
  rw [ByteArray.size_set!, ByteArray.size_set!, ByteArray.size_set!, ByteArray.size_set!]

theorem writeUInt64LEAt_size (buf : ByteArray) (offset : Nat) (val : UInt64) :
    (writeUInt64LEAt buf offset val).size = buf.size := by
  unfold writeUInt64LEAt
  rw [writeUInt32LEAt_size, writeUInt32LEAt_size]

/-! ## In-place write roundtrips -/

/-- Writing UInt16LE in-place and reading it back gives the original value. -/
theorem readUInt16LE_writeUInt16LEAt (buf : ByteArray) (offset : Nat) (val : UInt16)
    (h : offset + 2 ≤ buf.size) :
    readUInt16LE (writeUInt16LEAt buf offset val) offset = val := by
  simp only [readUInt16LE, writeUInt16LEAt]
  have hs : (buf.set! offset val.toUInt8).size = buf.size := ByteArray.size_set! ..
  -- b1 (offset + 1): self on outermost set!
  rw [ByteArray.getElem!_set!_self _ _ _ (by omega)]
  -- b0 (offset): ne on outer, self on inner
  rw [ByteArray.getElem!_set!_ne _ _ _ _ (by omega),
      ByteArray.getElem!_set!_self _ _ _ (by omega)]
  bv_decide

/-- Writing UInt32LE in-place and reading it back gives the original value. -/
theorem readUInt32LE_writeUInt32LEAt (buf : ByteArray) (offset : Nat) (val : UInt32)
    (h : offset + 4 ≤ buf.size) :
    readUInt32LE (writeUInt32LEAt buf offset val) offset = val := by
  simp only [readUInt32LE, writeUInt32LEAt]
  have hs0 : (buf.set! offset val.toUInt8).size = buf.size := ByteArray.size_set! ..
  have hs1 : ((buf.set! offset val.toUInt8).set! (offset + 1)
    (val >>> 8).toUInt8).size = buf.size := by rw [ByteArray.size_set!, hs0]
  have hs2 : (((buf.set! offset val.toUInt8).set! (offset + 1)
    (val >>> 8).toUInt8).set! (offset + 2) (val >>> 16).toUInt8).size = buf.size := by
    rw [ByteArray.size_set!, hs1]
  -- Resolve each getElem! through the set! chain
  -- Each byte at offset+k must peel off the outer set! layers (ne) then hit self
  have hb3 : ((((buf.set! offset val.toUInt8).set! (offset + 1) (val >>> 8).toUInt8).set!
    (offset + 2) (val >>> 16).toUInt8).set! (offset + 3) (val >>> 24).toUInt8)[offset + 3]! =
    (val >>> 24).toUInt8 :=
    ByteArray.getElem!_set!_self _ _ _ (by omega)
  have hb2 : ((((buf.set! offset val.toUInt8).set! (offset + 1) (val >>> 8).toUInt8).set!
    (offset + 2) (val >>> 16).toUInt8).set! (offset + 3) (val >>> 24).toUInt8)[offset + 2]! =
    (val >>> 16).toUInt8 := by
    rw [ByteArray.getElem!_set!_ne _ _ _ _ (by omega)]
    exact ByteArray.getElem!_set!_self _ _ _ (by omega)
  have hb1 : ((((buf.set! offset val.toUInt8).set! (offset + 1) (val >>> 8).toUInt8).set!
    (offset + 2) (val >>> 16).toUInt8).set! (offset + 3) (val >>> 24).toUInt8)[offset + 1]! =
    (val >>> 8).toUInt8 := by
    rw [ByteArray.getElem!_set!_ne _ _ _ _ (by omega),
        ByteArray.getElem!_set!_ne _ _ _ _ (by omega)]
    exact ByteArray.getElem!_set!_self _ _ _ (by omega)
  have hb0 : ((((buf.set! offset val.toUInt8).set! (offset + 1) (val >>> 8).toUInt8).set!
    (offset + 2) (val >>> 16).toUInt8).set! (offset + 3) (val >>> 24).toUInt8)[offset]! =
    val.toUInt8 := by
    rw [ByteArray.getElem!_set!_ne _ _ _ _ (by omega),
        ByteArray.getElem!_set!_ne _ _ _ _ (by omega),
        ByteArray.getElem!_set!_ne _ _ _ _ (by omega)]
    exact ByteArray.getElem!_set!_self _ _ _ (by omega)
  rw [hb0, hb1, hb2, hb3]
  bv_decide

/-- Writing UInt32LE at one offset doesn't affect reads at a non-overlapping offset. -/
theorem readUInt32LE_writeUInt32LEAt_ne (buf : ByteArray) (i j : Nat) (val : UInt32)
    (_hj : j + 4 ≤ buf.size) (hne : i + 4 ≤ j ∨ j + 4 ≤ i) :
    readUInt32LE (writeUInt32LEAt buf i val) j = readUInt32LE buf j := by
  simp only [readUInt32LE, writeUInt32LEAt]
  have hs0 : (buf.set! i val.toUInt8).size = buf.size := ByteArray.size_set! ..
  have hs1 : ((buf.set! i val.toUInt8).set! (i + 1)
    (val >>> 8).toUInt8).size = buf.size := by rw [ByteArray.size_set!, hs0]
  have hs2 : (((buf.set! i val.toUInt8).set! (i + 1)
    (val >>> 8).toUInt8).set! (i + 2) (val >>> 16).toUInt8).size = buf.size := by
    rw [ByteArray.size_set!, hs1]
  rw [ByteArray.getElem!_set!_ne _ _ _ _ (by omega),
      ByteArray.getElem!_set!_ne _ _ _ _ (by omega),
      ByteArray.getElem!_set!_ne _ _ _ _ (by omega),
      ByteArray.getElem!_set!_ne _ _ _ _ (by omega),
      ByteArray.getElem!_set!_ne _ _ _ _ (by omega),
      ByteArray.getElem!_set!_ne _ _ _ _ (by omega),
      ByteArray.getElem!_set!_ne _ _ _ _ (by omega),
      ByteArray.getElem!_set!_ne _ _ _ _ (by omega),
      ByteArray.getElem!_set!_ne _ _ _ _ (by omega),
      ByteArray.getElem!_set!_ne _ _ _ _ (by omega),
      ByteArray.getElem!_set!_ne _ _ _ _ (by omega),
      ByteArray.getElem!_set!_ne _ _ _ _ (by omega),
      ByteArray.getElem!_set!_ne _ _ _ _ (by omega),
      ByteArray.getElem!_set!_ne _ _ _ _ (by omega),
      ByteArray.getElem!_set!_ne _ _ _ _ (by omega),
      ByteArray.getElem!_set!_ne _ _ _ _ (by omega)]

/-- Writing UInt64LE in-place and reading it back gives the original value. -/
theorem readUInt64LE_writeUInt64LEAt (buf : ByteArray) (offset : Nat) (val : UInt64)
    (h : offset + 8 ≤ buf.size) :
    readUInt64LE (writeUInt64LEAt buf offset val) offset = val := by
  simp only [readUInt64LE, writeUInt64LEAt]
  rw [readUInt32LE_writeUInt32LEAt_ne _ _ _ _ (by rw [writeUInt32LEAt_size]; omega) (by omega),
      readUInt32LE_writeUInt32LEAt _ _ _ (by omega),
      readUInt32LE_writeUInt32LEAt _ _ _ (by rw [writeUInt32LEAt_size]; omega)]
  bv_decide

end Binary
