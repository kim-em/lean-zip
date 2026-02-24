---
name: lean-no-mathlib
description: Use when a Lean 4 tactic fails or is unavailable — such as ring, set, push_neg, by_contra, field_simp, rcases, norm_num, or obtain — because this project does not use Mathlib.
allowed-tools: Read, Bash, Grep
---

# Lean 4 Without Mathlib — Tactic Alternatives

This project uses only **Lean 4 core + Std**. Mathlib is NOT available.

## Unavailable Tactics and Their Replacements

| Mathlib tactic | Replacement |
|---------------|-------------|
| `ring` | **`grind`** — fully subsumes `ring` for algebraic goals (commutativity, associativity, distributivity over any ring/semiring) |
| `field_simp` | `simp` with relevant field lemmas manually specified |
| `positivity` | `omega` or `simp` with bounds |
| `polyrith` | `grind` or manual calculation |
| `norm_num` (Mathlib version) | `decide` for small concrete computations; `omega` for linear arithmetic |
| `push_neg` | Manual `simp only [not_forall, not_exists, not_le, not_lt, ...]` |
| `by_contra h` | `by_cases h : P` then `exfalso` in the `¬P` branch |
| `rcases h with ⟨a, b, c⟩` | `obtain ⟨a, b, c⟩ := h` (available in Std) |
| `obtain` | Available — use it freely |
| `set x := expr with hx` | `let x := expr` or `have hx : expr = expr := rfl` |
| `interval_cases` | `omega` or `fin_cases` for `Fin n` |

## Unavailable Names and Their Replacements

| Mathlib name | Replacement |
|-------------|-------------|
| `le_refl` | `Nat.le.refl` or `by omega` |
| `Nat.gt_of_not_le` | `by omega` |
| `congr_arg` | `congrArg` (note capitalization) |

## General Strategy

When in doubt, prefer: **`omega`**, **`simp`**, **`grind`**, **`by_cases`**, **`exact`**, **`decide`**

- `grind` is the go-to for algebraic/arithmetic goals
- `omega` handles linear integer/natural number arithmetic
- `decide` for decidable propositions over small finite types
- `simp` with explicit lemma lists for equational reasoning

## `set` is Not Available

Use `have` or `let` instead:
```lean
-- Instead of: set x := expensive_expr with hx
let x := expensive_expr
have hx : x = expensive_expr := rfl
```

## Contradiction Proofs

Instead of `by_contra h`:
```lean
by_cases h : P
· -- P case
· exfalso
  -- ¬P case, derive False
```

## Missing Standard Library Lemmas

If a proof is blocked by a missing lemma for standard types (ByteArray, Array,
List, UInt32, etc.), add it to `ZipForStd/` in the appropriate namespace.
For example, `ByteArray.foldl_toList` → add to `ZipForStd/ByteArray.lean`.
Write these lemmas as if they belonged in the standard library — they're
candidates for upstreaming.
