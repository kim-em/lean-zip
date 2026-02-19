/-!
# Adler-32 Specification

Adler-32 is a checksum defined in RFC 1950. It maintains two 16-bit sums
modulo 65521 (the largest prime less than 2^16):

  A = 1 + sum of all bytes
  B = sum of all A values after each byte

The result is `(B <<< 16) ||| A`, packed into a `UInt32`.
-/

namespace Adler32.Spec

/-- The Adler-32 modulus: largest prime less than 2^16. -/
def MOD_ADLER : Nat := 65521

/-- The two components of an Adler-32 state: (A, B). -/
abbrev State := Nat × Nat

/-- Initial Adler-32 state: A = 1, B = 0. -/
def init : State := (1, 0)

/-- Process a single byte, updating the Adler-32 state. -/
def updateByte (s : State) (byte : UInt8) : State :=
  let a := (s.1 + byte.toNat) % MOD_ADLER
  let b := (s.2 + a) % MOD_ADLER
  (a, b)

/-- Process a list of bytes via left fold. -/
def updateList (s : State) (data : List UInt8) : State :=
  data.foldl updateByte s

/-- Pack the state into a `UInt32`: `(B <<< 16) ||| A`. -/
def pack (s : State) : UInt32 :=
  (UInt32.ofNat s.2 <<< 16) ||| UInt32.ofNat s.1

/-- Compute the Adler-32 checksum of a byte list. -/
def checksum (data : List UInt8) : UInt32 :=
  pack (updateList init data)

/-- Unpack a `UInt32` into Adler-32 state: `(A, B)`. -/
def unpack (v : UInt32) : State :=
  (v.toNat % 65536, v.toNat / 65536)

/-! ## Specification theorems -/

/-- `updateList` over a concatenation equals sequential application. -/
theorem updateList_append (s : State) (xs ys : List UInt8) :
    updateList s (xs ++ ys) = updateList (updateList s xs) ys := by
  simp [updateList, List.foldl_append]

/-- Empty input leaves the state unchanged. -/
theorem updateList_nil (s : State) : updateList s [] = s := rfl

/-- Cons unfolds to updateByte then updateList. -/
theorem updateList_cons (s : State) (b : UInt8) (bs : List UInt8) :
    updateList s (b :: bs) = updateList (updateByte s b) bs := rfl

/-! ## Bounds theorems -/

/-- A state is valid when both components are less than MOD_ADLER. -/
def Valid (s : State) : Prop := s.1 < MOD_ADLER ∧ s.2 < MOD_ADLER

/-- The first component of `updateByte` is less than MOD_ADLER. -/
theorem updateByte_fst_lt (s : State) (b : UInt8) :
    (updateByte s b).1 < MOD_ADLER := by
  simp [updateByte, MOD_ADLER]
  omega

/-- The second component of `updateByte` is less than MOD_ADLER. -/
theorem updateByte_snd_lt (s : State) (b : UInt8) :
    (updateByte s b).2 < MOD_ADLER := by
  simp [updateByte, MOD_ADLER]
  omega

/-- `updateByte` preserves validity. -/
theorem updateByte_valid (s : State) (b : UInt8) :
    Valid (updateByte s b) :=
  ⟨updateByte_fst_lt s b, updateByte_snd_lt s b⟩

/-- The initial state is valid. -/
theorem init_valid : Valid init := by
  simp [Valid, init, MOD_ADLER]

/-- `updateList` preserves validity. -/
theorem updateList_valid (s : State) (hs : Valid s) (data : List UInt8) :
    Valid (updateList s data) := by
  induction data generalizing s with
  | nil => exact hs
  | cons b bs ih => exact ih (updateByte s b) (updateByte_valid s b)

end Adler32.Spec
