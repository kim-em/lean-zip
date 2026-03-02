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

When `unfold f at h` leaves `have x := e; body` bindings, the `letFun` wrapper
must be reduced before `split at h` can see inner `if` expressions.

The linter flags `letFun` as unused in `simp only [letFun] at h` because simp
handles it via built-in reduction, not the named lemma. Replace with:
```lean
dsimp only at h  -- definitional reduction handles letFun
```
This eliminates the linter warning while performing the same reduction.

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

## Replacing Bare `simp at h` in Error Branches

When `split at h` or `cases` produces a contradictory hypothesis
(e.g., `h : Except.error e = Except.ok x`), bare `simp at h` closes
the goal via built-in discriminator analysis (`reduceCtorEq` simproc).

**`simp only` cannot do this** — it lacks the discriminator simproc.
Neither `simp only [] at h` nor `contradiction` (max recursion in
deeply nested contexts) are reliable replacements.

**Canonical replacement**: `exact nomatch h`

```lean
-- Before (bare simp)
split at h
· simp at h  -- closes Except.error _ = Except.ok _

-- After (targeted)
split at h
· exact nomatch h  -- constructor discrimination
```

For `simp [hrb] at h` that substitutes then closes:
```lean
-- Before
| error e => simp [hrb] at h

-- After (two steps: substitute + discriminate)
| error e => simp only [hrb] at h; exact nomatch h
```

**Why `nomatch` works**: `Eq` has one constructor (`rfl`) requiring
definitional equality. `Except.error _` and `Except.ok _` are different
constructors, so no pattern matches — `nomatch h` produces the empty
match, proving `False`.

**Evaluating `if false = true then X else Y`**: Use `if_neg Bool.false_ne_true`
since `simp only [ite_false]` requires the condition to already be `False`,
not `false = true` (a decidable-but-not-reduced Prop).

## `simp only []` for Match Reduction

`simp only []` (empty argument list) can reduce `match` expressions
where the scrutinee is already a constructor:

```lean
-- After cases/split has resolved the scrutinee:
simp only []  -- reduces match (LZ77Token.literal b) with ...
```

This replaces patterns like `simp only [htok]` where the named hypothesis
was unused by simp — the match reduction happens without it.

**Limitation**: `simp only []` does NOT reduce `Option.bind none f` to `none`
or other monadic chain reductions. These require the full `@[simp]` database.
For deeply nested `do`-notation / `Option.bind` chains, bare `simp [hyps]`
is often the only practical approach — converting to `simp only` would require
explicitly listing every `@[simp]` lemma used in the bind reduction chain.

## `simp at h` vs `dsimp at h` for `if P then a else none = some b`

When `h : (if P then a else none) = some b`, `simp at h` deduces that `P`
must be true (since the `else` branch is `none ≠ some b`) and simplifies to
`h : a = some b`. **`dsimp at h` cannot do this** — it only performs
definitional reduction (iota, beta), not propositional reasoning about `if`.

This commonly arises in WF-recursive functions where the guard condition
(e.g., `if bits₁.length < br.toBits.length then ...`) is embedded in the
hypothesis. Replacing `simp at h` with `dsimp at h` will leave the guard
unresolved, causing downstream proofs to fail because they lose the length
bound that `simp` implicitly derived.

**Rule**: Use `dsimp at h` only for pure constructor/match reduction (e.g.,
reducing `match LZ77Symbol.literal b with | .literal b => ...`). Use
`simp at h` when the hypothesis contains `if P then ... else none` patterns
that need propositional resolution.

## `simp [hf]` vs `rw [if_pos/neg hf]` in Monadic Proofs

In suffix/roundtrip proofs where the goal's condition differs syntactically
from the hypothesis (e.g., goal has `(bits ++ suffix).length` but hypothesis
proves about `bits.length`), `simp [hf]` can bridge the gap via
`List.length_append` + arithmetic, while `rw [if_pos/neg hf]` and
`rw [dif_pos/neg hf]` require exact syntactic match. Don't try to replace
`simp [hf] at hgo ⊢` with `rw` in these cases — it will fail.

## `↓reduceIte` Decision Guide

| Condition Form | `↓reduceIte` Works? | Fix |
|----------------|---------------------|-----|
| `if True/False then ...` | Yes | — |
| `if (n > 0) then ...` (Prop) | After `rw [if_pos/if_neg h]` | Prove `h`, then `rw` |
| `if (false = true) then ...` | **No** | `if_neg (show ¬(false = true) from nofun)` |
| `if (x == y) then ...` (Bool) | After `show (x == y) = false` | `Bool.false_eq_true, ↓reduceIte` |

**After WF unfolding** (`rw [f.eq_1]`), function bodies often contain
`if` branches. The standard pattern: `rw [f.eq_1]; simp only [h, ↓reduceIte]`
where `h` resolves the guard. See the `lean-wf-recursion` skill for details.

## `decide` vs Structural Proofs for Large Finite Types

`decide` on large finite types (e.g., `∀ i : Fin 288, ...`) requires high
`maxRecDepth`. Replace with structural proofs that case-split on array
segments:

```lean
-- BAD: needs maxRecDepth 4096
theorem fixedLitLengths_le_15 : ∀ i : Fin 288, fixedLitLengths[i] ≤ 15 := by decide

-- GOOD: structural proof on array segments
theorem fixedLitLengths_le_15 : ∀ i : Fin 288, fixedLitLengths[i] ≤ 15 := by
  intro ⟨i, hi⟩
  simp only [fixedLitLengths, Array.getElem_ofFn]
  omega  -- or split on ranges
```

## Dagger Lemmas (`✝`) in `simp?` Suggestions

`simp?` sometimes suggests auto-generated lemmas with `✝` suffixes
(e.g., `UInt32.reduceBEq✝`). These are internal reduction lemmas that
**cannot be referenced by name** in `simp only` — the `✝` character is
not valid in Lean identifiers.

**Common case**: UInt32/UInt16/UInt8 `BEq` reduction. `simp?` suggests
`UInt32.reduceBEq✝` to evaluate expressions like `(1 : UInt32) == 0`.

**Workaround**: Replace with `decide` or explicit case analysis:

```lean
-- BAD: simp? suggested this but it won't compile
simp only [UInt32.reduceBEq✝, ↓reduceIte]

-- GOOD: use decide for concrete BEq evaluation
simp only [Nat.toUInt32_eq, this, ↓reduceIte]; decide

-- GOOD: for Bool case splits that previously used simp_all
cases b with
| false => rfl
| true => rw [hbit_val] at hbit; exact absurd hbit (by decide)
```

**When this arises**: Converting `cases b <;> simp_all` (which handles
UInt BEq reduction via the full simp database) to `simp only`. The
`simp_all` freely uses dagger lemmas internally, but `simp only` cannot.

## `Nat.mod_eq_sub_mod` for Inductive Mod Proofs

When proving `(n - k) % k = 0` from `n % k = 0` and `n ≥ k`:
```lean
← Nat.mod_eq_sub_mod hge  -- rewrites (n - k) % k to n % k
```
`omega` cannot reason about `%` directly.
