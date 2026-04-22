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

### When to Reach for `bv_decide`

Use `bv_decide` as the **final step** when the goal is purely about bit-level operations
on UInt8/UInt16/UInt32/UInt64/BitVec:

1. **Byte read/write roundtrips**: `readUInt32LE (writeUInt32LE val) 0 = val` —
   first `simp only` to normalize getElem!/set! calls, then `bv_decide` to close
   the bit reconstruction.

2. **Bit extraction/reconstruction**: goals like
   `((v &&& 0xFF).toUInt8).toUInt16 ||| (((v >>> 8) &&& 0xFF).toUInt8).toUInt16 <<< 8 = v`

3. **After `generalize`**: when data comes from `ByteArray` indexing, use
   `generalize data[pos].toUInt32 = x` to abstract concrete array access into
   a BitVec variable, then `bv_decide` reasons about the variable.

### `bv_decide` vs `bv_omega` vs `decide_cbv`

- `bv_decide` handles BitVec/UInt goals via SAT solving — fast for symbolic reasoning,
  **handles bitwise AND/OR/XOR/shift**
- `bv_omega` extends `omega` with some BitVec support but **cannot reason about
  bitwise AND/OR/XOR** — it only handles linear arithmetic. Use `bv_decide` instead
  when the goal involves `&&&`, `|||`, `^^^`, or similar bitwise operations.
- `decide_cbv` uses kernel evaluation — works for concrete decidable propositions but
  **fails on large arrays** (e.g., 288-element Huffman tables)
- For large concrete instances, use `decide` with `set_option maxHeartbeats 1600000`
  instead of `decide_cbv`

**Common pattern — UInt32 match catch-all elimination:**
When `split` on a UInt32 match creates a catch-all case with hypotheses like
`¬(expr &&& 3 = 0)`, `¬(expr &&& 3 = 1)`, `¬(expr &&& 3 = 2)`, `¬(expr &&& 3 = 3)`,
use `exfalso; bv_decide` to close the goal. The SAT solver recognizes that
`x &&& 3` can only produce values 0-3.

**Common pattern — `if x == 0 then a else b = c` on `UInt32`:**
prefer `bv_decide`. It handles the case-split inline without manual
`by_cases`. Precedent: the `raw_eq` helper inside `crc32_append` at
[`Zip/Native/Crc32.lean:103`](../../../Zip/Native/Crc32.lean) folds
the post-init zero-check into a single XOR via one `bv_decide`.

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

### Distinct Proof Terms Break Abstraction

A stronger variant of the same pitfall: when the same `GetElem` expression `arr[i]`
appears twice with **different proof-of-bounds terms** — one side has the
theorem-signature's named bounds proof, the other gets a term of shape `hidx ▸ hlt`
produced by `getElem_congr_idx` — `bv_decide`'s abstraction pass treats them as two
opaque variables and returns a spurious counterexample with conflicting assignments.
Proof irrelevance is not applied during abstraction; the two proof terms have to be
collapsed manually. First align the indices with `getElem_congr_idx`, then
`generalize` the unified expression to a fresh variable, then `bv_decide`:

```lean
rw [getElem_congr_idx (c := arr) hidx]
generalize arr[i]'(hidx ▸ hlt) = t
bv_decide
```

Precedents in [`Zip/Spec/Crc32.lean`](../../../Zip/Spec/Crc32.lean): the closed-form
proof `Crc32.Spec.checksum_singleton` uses the full three-step dance to collapse
`mkTable[0xFF ^^^ b.toNat]'(hidx ▸ hlt)` for the single-byte CRC; `checksum_pair`
reuses the index-alignment half (`rw [getElem_congr_idx ...]`) for the inner byte of
the two-byte CRC.

## Packing small nibbles via bitwise OR

When a `Nat` (or `UInt*`) is built by `x ||| (y <<< n)` with
`x < 2 ^ n` (and the high half stays in range), its `toNat` (or
value) equals `x + y * 2 ^ n`. The library lemma is
`Nat.two_pow_add_eq_or_of_lt`; for `BitVec` / `UInt*` use the
bitwidth-aware equivalent.

A reusable `Nat`-level helper for two-nibble packs:

```lean
lemma pack_toNat_of_bounds {x y : Nat} {n : Nat}
    (hx : x < 2 ^ n) :
    (y <<< n ||| x) = y * 2 ^ n + x := by
  rw [Nat.two_pow_add_eq_or_of_lt hx]
  ring
```

Use this whenever a checksum, packed header, or bitfield adds
lower bits into a higher-bit container. Adler-32 (PR #1641) is
the project's first user; CRC32 could adopt it on its next
refactor.

The concrete `UInt32`-specific instance lives as a `private`
helper at [`Zip/Spec/Adler32.lean:108`](../../../Zip/Spec/Adler32.lean) —
`pack_toNat_of_bounds {a b : Nat} (ha : a < 65536) (hb : b < 65536) :`
`(pack (a, b)).toNat = a + b * 65536`. Promote it to a public
`Nat`-level lemma the next time a third caller needs it.

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

## UInt8/UInt16 Hypotheses from `split`/`if` Need Nat Annotation for `omega`

When `split` or `if h : cond then ...` introduces a UInt comparison hypothesis
(e.g., `hlen_pos : lengths[start] > (0 : UInt8)`), `omega` CANNOT use it directly
because UInt comparison is opaque to `omega`. Add an explicit Nat annotation:
```lean
have hlen_pos_nat : 0 < lengths[start].toNat := hlen_pos
```
This forces Lean to elaborate the UInt comparison into a Nat constraint that `omega`
can see. The `have` looks like a redundant alias but is NOT — removing it breaks
downstream `omega` calls. This applies to UInt8, UInt16, UInt32, and UInt64.

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

## Exhaustive Proof over All UInt8 Values (Fin 256 Pattern)

When proving `∀ d : UInt8, P d` and automated tactics fail (`decide_cbv`, `bv_decide`,
`grind` all struggle with mixed Nat/UInt64 arithmetic from `.toNat` conversions):

**Use `decide` on `Fin 256` instead:**
```lean
set_option maxRecDepth 1024 in
theorem foo (d : UInt8) : P d := by
  have h : ∀ i : Fin 256, P ⟨⟨i⟩⟩ := by decide
  exact h d.toBitVec.toFin
```

**Why this works:**
- `UInt8 = BitVec 8 = { toFin : Fin 256 }` (two nested structures)
- `⟨⟨i⟩⟩` constructs `UInt8` from `Fin 256` (outer `UInt8.mk`, inner `BitVec.ofFin`)
- `Fin n` has `Decidable (∀ i : Fin n, P i)` — so `decide` enumerates all 256 values
- Structure eta fires: `⟨⟨d.toBitVec.toFin⟩⟩ = d` definitionally
- `set_option maxRecDepth 1024` is needed for 256-case recursion

**When to use:** Properties of functions that take `UInt8` and produce `UInt16`/`UInt32`/`UInt64`,
especially when the function mixes `.toNat` conversions between different UInt widths.
`bv_decide` abstracts `.toNat` as opaque; `decide_cbv` can't reduce the mixed arithmetic;
`decide +revert` fails because `BitVec` lacks a `Decidable (∀ x : BitVec n, ...)` instance.

**Tactics that DON'T work for this pattern:**
- `decide_cbv` — gets stuck on UInt64 operations
- `bv_decide` — spurious counterexample from opaque `.toNat` abstractions
- `decide +revert` — no `Decidable (∀ d : UInt8, ...)` instance
- `decide` alone — "free variables" error
- `grind` — can't handle UInt64 modular arithmetic
