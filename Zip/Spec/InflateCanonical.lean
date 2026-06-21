import Zip.Spec.InflateTable
import Zip.Spec.HuffmanCorrectLoop

/-!
# Canonical O(n) decode-table build: equivalence to the tree-built table

`HuffTree.buildTableCanonical lengths` fills the fast decode table directly from
the code lengths (libdeflate `build_decode_table`): no Huffman tree, no per-slot
tree walk. The goal is to prove it equal to `buildTable (fromLengthsTree lengths)`,
so the canonical build becomes a drop-in for the tree-built table with every
decode proof transferring unchanged and no `@[implemented_by]` trust gap.

This file develops the format-independent **foundation** of that proof. The
planned route (per #2671) characterizes each table slot by the canonical code
table `allCodes`: slot `idx` holds `packEntry sym len` iff some `(sym, cw)` with
`len = cw.length ≤ fastBits` and `cwOf idx len = cw` is in `allCodes`, else the
sentinel `packEntry 0 0`. `buildTable`'s side follows from the existing
`hasLeaf_of_tableEntry_go` / `fromLengths_leaf_spec` / `fromLengths_hasLeaf`
bridge; the canonical loop's side from a table-local `nextCode` invariant. The
final equality theorem (`buildTableCanonical_eq`) and the decode rewiring land in
a follow-up; a differential conformance test already witnesses the equality at
runtime.

The foundation lemmas here, bottom-up:
1. `bitReverse` arithmetic — the bit-reversed codeword indexes the fast table.
2. `cwOf`/`bitReverse` bridge (`cwOf_eq_iff_mod`) — slot `idx` lies on a
   codeword's path iff `idx % 2^len` is the bit-reversed code.
3. `fillSlots` — what the slot-fill writes (`fillSlots_getElem_eq`) and
   preserves (`fillSlots_getElem_ne`, `fillSlots_size`).
-/

namespace Zip.Native.HuffTree

open Huffman.Spec (natToBits)

/-! ## `bitReverse` arithmetic -/

/-- The accumulator of `bitReverse` separates as a high-order summand: reversing
    `n` bits of `x` onto `acc` is `acc` shifted up by `n` plus the bare reversal. -/
theorem bitReverse_acc (x n acc : Nat) :
    bitReverse x n acc = acc * 2 ^ n + bitReverse x n 0 := by
  induction n generalizing x acc with
  | zero => simp [bitReverse]
  | succ n ih =>
    simp only [bitReverse]
    rw [ih (x / 2) (acc * 2 + x % 2), ih (x / 2) (0 * 2 + x % 2), Nat.zero_mul,
        Nat.zero_add, Nat.pow_succ, Nat.mul_comm (2 ^ n) 2, Nat.add_mul,
        Nat.mul_assoc acc 2 (2 ^ n)]
    omega

/-- The bare reversal of `n` bits fits in `n` bits. -/
theorem bitReverse_lt (x n : Nat) : bitReverse x n 0 < 2 ^ n := by
  induction n generalizing x with
  | zero => simp [bitReverse]
  | succ n ih =>
    simp only [bitReverse]
    rw [bitReverse_acc, Nat.pow_succ]
    have hr := ih (x / 2)
    rcases Nat.mod_two_eq_zero_or_one x with h | h <;> rw [h] <;> omega

/-- Bit `i` (`i < n`) of the `n`-bit reversal of `x` is bit `n-1-i` of `x`:
    `bitReverse` reverses the low `n` bits. -/
theorem bitReverse_testBit (x n i : Nat) (hi : i < n) :
    (bitReverse x n 0).testBit i = x.testBit (n - 1 - i) := by
  induction n generalizing x i with
  | zero => omega
  | succ n ih =>
    have hR : bitReverse x (n + 1) 0 = 2 ^ n * (x % 2) + bitReverse (x / 2) n 0 := by
      simp only [bitReverse]
      rw [bitReverse_acc, Nat.zero_mul, Nat.zero_add, Nat.mul_comm (x % 2) (2 ^ n)]
    rw [hR, Nat.testBit_two_pow_mul_add _ (bitReverse_lt (x / 2) n)]
    rcases Nat.lt_or_ge i n with hlt | hge
    · rw [if_pos hlt, ih (x / 2) i hlt, ← Nat.testBit_succ]
      congr 1; omega
    · have hin : i = n := by omega
      subst hin
      rw [if_neg (by omega), Nat.sub_self, show i + 1 - 1 - i = 0 from by omega,
          Nat.testBit_zero, Nat.testBit_zero, show x % 2 % 2 = x % 2 from by omega]

/-! ## `cwOf` / `bitReverse` bridge

`tableEntry` walks the table index LSB-first, so slot `idx` lies on the path of a
length-`len` codeword `c` exactly when `cwOf idx len = natToBits c len`. The
canonical fill writes the slots `idx` with `idx % 2^len = bitReverse c len 0`;
these two descriptions coincide. -/

/-- `(natToBits c len)[j]` (MSB-first) is bit `len-1-j` of `c`. -/
theorem natToBits_getElem (c len j : Nat) (hj : j < len) :
    (natToBits c len)[j]'(by rw [Huffman.Spec.natToBits_length]; exact hj)
      = c.testBit (len - 1 - j) := by
  induction len generalizing j with
  | zero => omega
  | succ n ih =>
    match j with
    | 0 => simp only [natToBits, List.getElem_cons_zero, Nat.add_sub_cancel, Nat.sub_zero]
    | j + 1 =>
      have hstep : (natToBits c (n + 1))[j + 1]'(by rw [Huffman.Spec.natToBits_length]; omega)
          = (natToBits c n)[j]'(by rw [Huffman.Spec.natToBits_length]; omega) := by
        simp only [natToBits, List.getElem_cons_succ]
      rw [hstep, ih j (by omega)]; congr 1; omega

/-- `cwOf` depends only on the low `k` bits of `bits` (it reads them LSB-first). -/
theorem cwOf_mod (bits k : Nat) : cwOf (bits % 2 ^ k) k = cwOf bits k := by
  apply List.ext_getElem (by simp only [cwOf_length])
  intro j h₁ _
  rw [cwOf_length] at h₁
  rw [cwOf_getElem (bits % 2 ^ k) k j h₁, cwOf_getElem bits k j h₁,
      Nat.testBit_mod_two_pow]
  simp [h₁]

/-- The bit-reversed code is the unique low-`len`-bits value whose `cwOf` path is
    the codeword `natToBits c len`. -/
theorem cwOf_bitReverse (c len : Nat) :
    cwOf (bitReverse c len 0) len = natToBits c len := by
  apply List.ext_getElem (by rw [cwOf_length, Huffman.Spec.natToBits_length])
  intro j h₁ _
  rw [cwOf_length] at h₁
  rw [cwOf_getElem (bitReverse c len 0) len j h₁, bitReverse_testBit _ _ _ h₁,
      natToBits_getElem c len j h₁]

/-- Two `cwOf` paths of the same length agree iff the low bits agree. -/
theorem cwOf_mod_eq_of_cwOf_eq (a b len : Nat) (h : cwOf a len = cwOf b len) :
    a % 2 ^ len = b % 2 ^ len := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  by_cases hi : i < len
  · simp only [hi, decide_true, Bool.true_and]
    have ha : (cwOf a len)[i]? = some (a.testBit i) := by
      rw [List.getElem?_eq_getElem (by rw [cwOf_length]; exact hi), cwOf_getElem a len i hi]
    have hb : (cwOf b len)[i]? = some (b.testBit i) := by
      rw [List.getElem?_eq_getElem (by rw [cwOf_length]; exact hi), cwOf_getElem b len i hi]
    rw [h, hb] at ha
    exact (Option.some.inj ha).symm
  · simp [hi]

/-- The slot-fill membership condition: slot `idx` lies on the path of a
    length-`len` codeword `c` (`cwOf idx len = natToBits c len`) iff its low
    `len` bits are the bit-reversed code. -/
theorem cwOf_eq_iff_mod (idx c len : Nat) :
    cwOf idx len = natToBits c len ↔ idx % 2 ^ len = bitReverse c len 0 := by
  constructor
  · intro h
    have h2 : cwOf (idx % 2 ^ len) len = cwOf (bitReverse c len 0) len := by
      rw [cwOf_mod, h, ← cwOf_bitReverse]
    have h3 := cwOf_mod_eq_of_cwOf_eq _ _ _ h2
    rwa [Nat.mod_eq_of_lt (Nat.mod_lt idx (Nat.two_pow_pos len)),
        Nat.mod_eq_of_lt (bitReverse_lt c len)] at h3
  · intro h
    have hbr := cwOf_bitReverse c len
    rw [← h] at hbr
    exact (cwOf_mod idx len).symm.trans hbr

/-! ## `fillSlots` -/

/-- `fillSlots` preserves the array size. -/
@[simp] theorem fillSlots_size (packed : Array UInt32) (base stride count : Nat)
    (entry : UInt32) :
    (fillSlots packed base stride count entry).size = packed.size := by
  induction count generalizing packed base with
  | zero => simp [fillSlots]
  | succ n ih =>
    rw [fillSlots]
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    rw [ih (packed.set! base entry) (base + stride)]
    simp

/-- A slot not on the fill's arithmetic progression `{base + j·stride : j < count}`
    keeps its old value. -/
theorem fillSlots_getElem_ne (packed : Array UInt32) (base stride count idx : Nat)
    (entry : UInt32) (h : ∀ j < count, idx ≠ base + j * stride) :
    (fillSlots packed base stride count entry)[idx]! = packed[idx]! := by
  induction count generalizing packed base with
  | zero => simp [fillSlots]
  | succ n ih =>
    rw [fillSlots]
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    rw [ih (packed.set! base entry) (base + stride) (by
      intro j hj
      have hne := h (j + 1) (by omega)
      have e : base + (j + 1) * stride = base + stride + j * stride := by
        rw [Nat.succ_mul]; omega
      rw [e] at hne; exact hne)]
    have hb : idx ≠ base := by have := h 0 (Nat.zero_lt_succ n); simpa using this
    rw [Array.set!_eq_setIfInBounds]
    by_cases hlt : idx < packed.size
    · rw [getElem!_pos _ idx (by rw [Array.size_setIfInBounds]; exact hlt),
          getElem!_pos _ idx hlt, Array.getElem_setIfInBounds hlt, if_neg (Ne.symm hb)]
    · rw [getElem!_neg _ idx (by rw [Array.size_setIfInBounds]; exact hlt),
          getElem!_neg _ idx hlt]

/-- A slot on the fill's arithmetic progression `base + j·stride` (`j < count`,
    in bounds) holds the fill value. -/
theorem fillSlots_getElem_eq (packed : Array UInt32) (base stride count j : Nat)
    (entry : UInt32) (hstride : 0 < stride) (hj : j < count)
    (hbound : base + j * stride < packed.size) :
    (fillSlots packed base stride count entry)[base + j * stride]! = entry := by
  induction count generalizing packed base j with
  | zero => omega
  | succ n ih =>
    rw [fillSlots]
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    match j with
    | 0 =>
      rw [show base + 0 * stride = base from by omega]
      rw [fillSlots_getElem_ne (packed.set! base entry) (base + stride) stride n base entry
        (fun k _ => by omega)]
      have hbase : base < packed.size := by have := hbound; omega
      rw [Array.set!_eq_setIfInBounds,
          getElem!_pos _ base (by rw [Array.size_setIfInBounds]; exact hbase),
          Array.getElem_setIfInBounds_self]
    | j' + 1 =>
      have e : base + (j' + 1) * stride = base + stride + j' * stride := by
        rw [Nat.succ_mul]; omega
      rw [e]
      exact ih (packed.set! base entry) (base + stride) j' (by omega)
        (by rw [Array.size_set!, ← e]; exact hbound)

end Zip.Native.HuffTree
