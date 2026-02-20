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
  induction n generalizing a with
  | zero =>
    have : a = 0 := by omega
    subst this; rfl
  | succ n ih =>
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_or]
    cases i with
    | zero =>
      simp only [Nat.testBit_zero]
      have h1 : 2 ^ (n + 1) % 2 = 0 := by
        rw [Nat.pow_succ, Nat.mul_comm]; exact Nat.mul_mod_right 2 (2 ^ n)
      have h2 : (a + 2 ^ (n + 1)) % 2 = a % 2 := by
        rw [Nat.add_mod, h1, Nat.add_zero]
        exact Nat.mod_eq_of_lt (Nat.mod_lt a (by omega))
      rw [h1, h2]; simp
    | succ i =>
      simp only [Nat.testBit_succ]
      have hdiv : 2 ^ (n + 1) / 2 = 2 ^ n := by
        rw [Nat.pow_succ, Nat.mul_div_cancel _ (by omega : 0 < 2)]
      have hsum : (a + 2 ^ (n + 1)) / 2 = a / 2 + 2 ^ n := by
        rw [Nat.pow_succ]
        exact Nat.add_mul_div_right a (2 ^ n) (by omega)
      rw [hdiv, hsum, ← Nat.testBit_or, ih (by omega)]

end Nat
