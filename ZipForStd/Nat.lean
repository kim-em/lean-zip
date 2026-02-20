/-!
# Missing Nat lemmas for standard library

Lemmas about bitwise operations on natural numbers that are useful for
reasoning about bit-level algorithms (CRC, DEFLATE, etc.) but missing
from Lean 4's standard library. Candidates for upstreaming.
-/

namespace Nat

/-- When `a < 2^n`, bitwise OR with `2^n` equals addition.
    This holds because bit `n` of `a` is 0, so there's no overlap. -/
theorem or_two_pow_eq_add {a n : Nat} (h : a < 2 ^ n) : a ||| 2 ^ n = a + 2 ^ n := by
  have := Nat.two_pow_add_eq_or_of_lt h 1
  simp [Nat.mul_one] at this
  rw [Nat.or_comm, ← this, Nat.add_comm]

end Nat
