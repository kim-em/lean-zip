import Zip.Spec.BitstreamCorrect

/-!
# `readBitsFast` equals `BitReader.readBits`

`Zip.Native.readBitsFast` reads an `n`-bit field with O(1) heap allocations
(threading the cursor as unboxed `Nat`s, building the `BitReader` once) instead
of the O(n) allocations of the `readBit`-looping `BitReader.readBits`. This file
proves they are extensionally equal, so every consumer proof transfers by `rw`.
-/

namespace Zip.Native

open ZipCommon (BitReader)

/-- The fast cursor-threading loop agrees step-for-step with `readBits.go`:
    at fuel `k` from cursor `(pos, bitOff)`, both read the same bits and reach
    the same `(value, BitReader)`. -/
theorem readBitsFast_go_eq (br : BitReader) (pos bitOff : Nat) (acc : UInt32) (shift k : Nat) :
    readBitsFast.go br pos bitOff acc shift k =
      BitReader.readBits.go { br with pos := pos, bitOff := bitOff } acc shift k := by
  induction k generalizing pos bitOff acc shift with
  | zero => rfl
  | succ k ih =>
    rw [readBitsFast.go, BitReader.readBits.go, BitReader.readBit]
    by_cases hp : pos ≥ br.data.size
    · simp only [hp, ↓reduceIte, bind, Except.bind]
    · simp only [hp, ↓reduceIte]
      by_cases hb : bitOff + 1 ≥ 8
      · simp only [hb, ↓reduceIte, bind, Except.bind]
        exact ih (pos + 1) 0 _ _
      · simp only [hb, ↓reduceIte, bind, Except.bind]
        exact ih pos (bitOff + 1) _ _

/-- `readBitsFast` decodes exactly the same `(value, BitReader)` (and the same
    error) as `BitReader.readBits`. -/
theorem readBitsFast_eq (br : BitReader) (n : Nat) :
    readBitsFast br n = br.readBits n := by
  rw [readBitsFast, BitReader.readBits, readBitsFast_go_eq]

end Zip.Native
