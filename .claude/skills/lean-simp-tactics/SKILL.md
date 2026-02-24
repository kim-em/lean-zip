---
name: lean-simp-tactics
description: Use when simp only fails unexpectedly in Lean 4, or when dealing with Bool vs Prop conditions, filter+lambda, let bindings in omega, linter false positives, or hypothesis normalization mismatches.
allowed-tools: Read, Bash, Grep
---

# Lean 4 `simp` Tactic Patterns

## `simp only` Fails with `List.filter` + Anonymous Lambdas

When `List.filter_cons` unfolds `(a :: l).filter p` to `if p a = true then ...`, and
`p` is an anonymous lambda like `(· != 0)`, the `p a` application remains unreduced.
`simp only` cannot beta-reduce this or evaluate the boolean.

Use full `simp` (without `only`) which includes beta-reduction and boolean evaluation.

Similarly, `List.set_cons_zero` and `List.set_cons_succ` are not `@[simp]` — unfold
them with `simp only` first, then use `simp` for the filter/boolean parts.

## `Bool` vs `Prop` in `if` Conditions

When proving an `if` takes a specific branch, check whether the condition is `Bool`
or `Prop`:
- **`Bool`**: prove `show (cond) = false from by decide` then use
  `Bool.false_eq_true, ↓reduceIte`
- **`Prop`**: prove `show ¬P from by omega` then use `↓reduceIte`

Don't use `show P = false from by omega` for `Prop` conditions — `>` on `Nat`
creates a `Prop`, not a `Bool`.

## Extracting Conditions from `&&` Boolean Hypotheses

When a proof has `hcond : (a && decide P && decide Q) = true` from an `if` guard:
```lean
simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
```
This decomposes into `hcond : (a = true ∧ P) ∧ Q`.

Note: `&&` is left-associative, so the result is left-nested `(... ∧ ...) ∧ ...`,
NOT right-nested. Use `obtain ⟨⟨ha, hp⟩, hq⟩ := hcond` or `hcond.1.2` / `hcond.2`
to access components.

## `let` Bindings Are Opaque to `omega`

When a hypothesis `hj` contains an expanded expression (e.g. `(List.map f xs).length`)
and you define `let pl := List.map f xs`, omega treats `pl.length` and
`(List.map f xs).length` as distinct variables.

Fix with `change j ≥ max 4 (pl.length - tw.length) at hj` — `change` does definitional
unfolding, making the terms syntactically identical for omega.

Don't try `simp` or `rfl` equations — they add complexity without helping omega.

## `simp` Hypothesis Must Match Post-Rewrite Form

When using `simp only [rewrite_eq, neg_hyp, ↓reduceIte]`, if `rewrite_eq` transforms
the goal's condition (e.g. `sym.toUInt16.toNat` → `sym`), then `neg_hyp` must be
stated in the post-rewrite form (e.g. `¬(sym - 257 ≥ ...)`, not
`¬(sym.toUInt16.toNat - 257 ≥ ...)`).

`simp` applies all rules together, so the hypothesis must match the normalized goal,
not the pre-rewrite form.

## `letFun` Linter False Positive

When `unfold f at h` leaves `have x := e; body` bindings, `simp only [letFun] at h`
is needed to reduce them before `split at h` can see inner `if` expressions.

The linter may report `letFun` as unused — this is a false positive. Do NOT remove it.
Same applies to `guard`, `pure`, `Pure.pure` in `simp only [guard, ...]` — the linter
reports them as unused but removing them leaves `match guard (...)` unreduced.

Use `set_option linter.unusedSimpArgs false in` to suppress.

## `Nat.mod_eq_sub_mod` for Inductive Mod Proofs

When proving `(n - k) % k = 0` from `n % k = 0` and `n ≥ k`:
```lean
← Nat.mod_eq_sub_mod hge  -- rewrites (n - k) % k to n % k
```
`omega` cannot reason about `%` directly.
