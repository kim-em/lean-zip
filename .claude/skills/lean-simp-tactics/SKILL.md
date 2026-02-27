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

## Fixing `bind`/`Option.bind`/`Except.bind` Linter Warnings

The linter flags `bind`, `Option.bind`, and `Except.bind` as unused in
`simp only [hX, bind, Option.bind]` because they contribute only via dsimp.
Do NOT suppress with `set_option linter.unusedSimpArgs false` — use the
`rw + dsimp` pattern from the `lean-monad-proofs` skill instead:

```lean
rw [hX] at h; dsimp only [bind, Option.bind] at h ⊢
```

## `have` Bindings That Look Unused but Feed `omega`/`simp`

`omega` and `simp` scan the **entire local context** for usable hypotheses.
A `have` binding that is never referenced by name may still be critical:

```lean
have hlen_pos_nat : 0 < lengths[i].toNat := hlen  -- "unused" but omega needs it
have hlen_le : lengths[i].toNat ≤ maxBits := ...   -- "unused" but omega needs it
...
exact foo (by rw [hls_i]; omega)  -- omega closes via hlen_pos_nat + hlen_le
```

**Before removing a `have`**: Check whether any downstream `omega`, `simp`,
or `simp_all` could be relying on it. The binding won't appear in grep results
but `omega` uses it implicitly. Build after each removal to catch breakage.

**Common pattern**: UInt8/UInt16/UInt32 → Nat bridge hypotheses
(`hlen_pos_nat : 0 < x.toNat := hlen`) exist specifically because `omega`
works on `Nat`, not on `UIntN`. These are NOT dead code.

## `simp` Destroys Type Info Needed for Recursive Call Inference

When proving length bounds for recursive functions, `simp only [List.length_cons]`
reduces `(x :: recursive_call).length` to `recursive_call.length + 1`. After this,
`have := recursive_func _ _ _` fails because Lean can no longer infer the implicit
arguments from the goal — the List structure connecting them is gone.

**Fix**: Use a type-bridge helper lemma that takes the recursive call as an argument
(not via `have`). This works because Lean unifies the argument's type against the
goal before `simp` runs:

```lean
-- Helper bridges the recursive call through simp
private theorem length_cons_le {n k s pos : Nat}
    (ih : n ≤ s - (pos + k)) (hk : k ≥ 1) (hle : pos + k ≤ s) :
    n + 1 ≤ s - pos := by omega

-- Usage: recursive call is an argument, not a have
simp only [List.length_cons]
exact length_cons_le (mainLoop_length _ _ _ _ _ _) (by omega) hle
```

**Why `have` before `simp` also fails**: Even with `have ih := recursive_func _ _ _`
before `simp`, Lean still can't infer implicit arguments if the goal doesn't
directly mention the recursive call's result type.

**Also**: `all_goals (have := f _ _; tac)` with semicolons inside parenthesized
tactic blocks can cause parse errors. Use separate focused proofs (`·`) instead.

## `Nat.mod_eq_sub_mod` for Inductive Mod Proofs

When proving `(n - k) % k = 0` from `n % k = 0` and `n ≥ k`:
```lean
← Nat.mod_eq_sub_mod hge  -- rewrites (n - k) % k to n % k
```
`omega` cannot reason about `%` directly.
