---
name: lean-uint-bitvec
description: Use when Lean 4 proofs involve UInt8/UInt16/UInt32/BitVec conversions, bv_decide, or bridging between numeric types and Nat.
allowed-tools: Read, Bash, Grep
---

# Lean 4 UInt/BitVec Proof Patterns

## `bv_decide` for UInt32/BitVec

Effective for bitvector reasoning. Proved CRC linearity (`crcBit_xor_high`) and the
8-fold split (`crcBits8_split`) each in one line.

**Caveat**: fails when expressions contain `UInt32.ofNat x.toNat` (abstracted as opaque).
Use `generalize` to unify shared subexpressions first (see below).

## UInt8→UInt32 Conversion for `bv_decide`

When `bv_decide` fails on `UInt32.ofNat byte.toNat`, rewrite to `⟨byte.toBitVec.setWidth 32⟩`
using `BitVec.ofNat_toNat`. Then use `show` + `congr 1` to expose the inner `BitVec`:
```lean
rw [UInt32_ofNat_UInt8_toNat]  -- rewrites via BitVec.ofNat_toNat
show UInt32.ofBitVec (... bitvec expr ...) = UInt32.ofBitVec (...)
congr 1; bv_decide
```

## `generalize` Before `bv_decide` for Shared Subexpressions

When `bv_decide` fails with "spurious counterexample" because it abstracts the same
expression (e.g., `data[pos]`) as multiple opaque variables, use
`generalize data[pos].toUInt32 = x` first to unify them into a single variable.

## UInt32 Bit Operations → `Nat.testBit`

To prove `(byte.toUInt32 >>> off.toUInt32) &&& 1 = if byte.toNat.testBit off then 1 else 0`:
1. `UInt32.toNat_inj.mp` to reduce to Nat
2. `UInt32.toNat_and`/`UInt32.toNat_shiftRight`/`UInt8.toNat_toUInt32`
3. `Nat.testBit` unfolds to `1 &&& m >>> n != 0` — use `Nat.and_comm` + `Nat.one_and_eq_mod_two` + `split <;> omega`

## `Nat.and_one_is_mod` and `Nat.one_and_eq_mod_two`

For bridging `Nat.testBit` (which uses `1 &&& (m >>> n)`) to `% 2`:
- `Nat.one_and_eq_mod_two : 1 &&& n = n % 2` (matches testBit order)
- `Nat.and_one_is_mod : x &&& 1 = x % 2` (matches code order)

## UInt32 Shift Mod 32

`UInt32.shiftLeft` reduces the shift amount mod 32 — for `bit <<< shift.toUInt32`
with `shift ≥ 32`, the bit is placed at position `shift % 32`, not `shift`.
Any theorem about `readBits` (which accumulates via `bit <<< shift`) needs `n ≤ 32`.

## Avoid `▸` with UInt32/BitVec Goals

The `▸` (subst rewrite) tactic triggers full `whnf` reduction, which can
deterministic-timeout on goals involving UInt32 or BitVec operations. Use
`obtain ⟨rfl, _⟩ := h` + `rw [...]` + `exact ...` instead.

## UInt16 Comparison and Conversion

In v4.29.0-rc1+, UInt16 is BitVec-based:
- `sym < 256` (UInt16 lt) directly proves `sym.toNat < 256` via `exact hsym`
- `¬(sym < 256)` gives `sym.toNat ≥ 256` via `Nat.le_of_not_lt hge`
- `sym.toNat = 256` proves `sym = 256` via `UInt16.toNat_inj.mp (by simp; exact heq)`
- `sym.toUInt8` equals `sym.toNat.toUInt8` by `rfl`
- `omega` CANNOT directly bridge UInt16 comparisons to Nat — extract hypotheses first

## Nat↔UInt16 beq Bridging

When `hsym_ne : ¬(sym == N) = true` (Nat beq) but you have `h : sym.toUInt16 = N`
(UInt16 equality from `rw [beq_iff_eq] at h`), bridge via:
```lean
have := congrArg UInt16.toNat h  -- sym.toUInt16.toNat = N.toNat
rw [hsym_toNat] at this          -- sym = N.toNat (= N by simp)
exact absurd (beq_iff_eq.mpr (by simpa using this)) hsym_ne
```
Don't try `exact absurd h hsym_ne` — types differ (UInt16 vs Nat beq).

## UInt8 Comparison ↔ Nat Comparison

When native code uses UInt8 comparisons (e.g. `bw.bitCount + 1 >= 8`) but proofs
work in Nat (e.g. `bw.bitCount.toNat + 1 >= 8`), bridge with
`UInt8.le_iff_toNat_le`, `UInt8.toNat_add`, `UInt8.toNat_ofNat` + `omega`.

Prefer plain induction + `by_cases` on the Nat condition, then convert to UInt8
for the goal's `if` using an iff bridging lemma.

## UInt8 Positivity from Nat Membership

When you have `hne0 : (lengths.toList.map UInt8.toNat)[s] ≠ 0` and need
`lengths[s] > 0` (UInt8 comparison):
1. `have hs_i : (...)[s] = lengths[s].toNat := by simp only [...]; rfl`
2. `have hne0_nat : lengths[s].toNat ≠ 0 := hs_i ▸ hne0`
3. `simp only [GT.gt, UInt8.lt_iff_toNat_lt, UInt8.toNat_ofNat]; omega`

Plain `omega` can't bridge UInt8 `>` to Nat directly.

## `toUInt32.toNat` for Small Nat

`rep.toUInt32.toNat = rep` when `rep < 2^n` for small `n` (e.g., from
`readBitsLSB_bound`). Use `Nat.mod_eq_of_lt (by omega)` directly. Don't use
`show rep % UInt32.size = rep; omega` — omega can't reason about `%`.

## Nat `beq` False

To prove `(n == m) = false` for Nat with `n ≠ m`:
```lean
cases heq : n == m <;> simp_all [beq_iff_eq]
```
Direct `omega` and `rw [beq_iff_eq]` don't work — `omega` doesn't understand
`BEq` and `beq_iff_eq` is about `= true`, not `= false`.

## `Bool.false_eq_true` for Stuck `if false = true`

After substituting `(x == y) = false` via simp, `↓reduceIte` can't reduce
`if false = true then ... else ...` because `false = true` is a `Prop`. Add
`Bool.false_eq_true` to rewrite it to `False`, then `↓reduceIte` can reduce the `if`.
