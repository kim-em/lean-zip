---
name: lean-monad-proofs
description: Use when working on Lean 4 proofs involving Option or Except monad, do-notation unfolding, guard patterns, bind handling, join points, or forIn loops in specifications.
allowed-tools: Read, Bash, Grep
---

# Lean 4 Monad Proof Patterns

## Avoid `for`/`while` in Spec Functions

In `Option`/`Except` monads, `return` inside a `for` loop exits the loop (producing
`some`), not the function. Use explicit recursive helper functions instead — they're
also easier to reason about in proofs. Reserve `for`/`while` for `IO` code.

## Unfolding do-notation with `Except.bind`

When a hypothesis `h` contains a `do` block (`let x ← f; g x`), use `cases hrd : f`
to split on the result BEFORE simplifying `h`. Then
`simp only [..., hrd, bind, Except.bind] at h` substitutes the known result.
This is cleaner than `simp [...] at h; split at h; rename_i ...` which produces
fragile unnamed hypotheses.

## do-notation Guards (`if ... then throw`)

Guards like `if cond then throw err` in `Except` do-notation expand to
`match (if cond then Except.error err else pure PUnit.unit) with | Except.error e => ... | Except.ok _ => ...`.
After splitting the outer condition with `split at h`, the `pure` branch leaves a
stuck `match`. Use `simp only [pure, Except.pure] at h` to reduce it, then continue
with the next `cases`/`split`.

## Closing `Except.error = Except.ok` Contradictions

`simp only` does NOT know that `Except.error ≠ Except.ok` — it lacks the
discriminator simproc. The canonical replacement is `exact nomatch h`:

```lean
-- Before (bare simp):
| error e => simp at h

-- After (targeted):
| error e => exact nomatch h
```

For cases where a hypothesis must be rewritten first:
```lean
-- Before:
| error e => simp [hrb] at h

-- After (two steps):
| error e => simp only [hrb] at h; exact nomatch h
```

**Why `nomatch` works**: `Eq` has one constructor (`rfl`) requiring
definitional equality. `Except.error _` and `Except.ok _` are different
constructors, so no pattern can match — `nomatch h` proves `False`.

**Why NOT `contradiction`**: In deeply nested contexts (6+ bind levels),
`contradiction` hits max recursion depth. `exact nomatch h` always works.

**Why NOT `exact absurd h (by simp)`**: Roundabout — invokes simp just
to produce the `≠` proof. `nomatch` is direct and needs no lemma database.

## Nested `cases` Parsing

Nested `cases ... with | ... | ...` blocks cause Lean to misparse the inner
`| some =>` as belonging to the outer `cases`. Use `match` for the inner case split:
```lean
cases hdb : f x with
| none =>
  match hdec : g y with   -- NOT `cases hdec : g y with`
  | none => ...
  | some p => ...
| some p => ...
```

## Block-Level Correspondence Proof Pattern

For theorems connecting native imperative decoders (`Except` monad with `do`) to
spec decoders (`Option` monad with `bind`):
1. `simp only [NativeFunc, bind, Except.bind] at h` to unfold the native
2. `cases hx : operation` + `simp [hx] at h` for each `Except` operation
3. Build spec-level hypotheses by chaining correspondence lemmas
4. Close with `simp only [SpecFunc, bind, Option.bind, hyp₁, hyp₂, ...]` + `rfl`

Key: prepare all intermediate spec hypotheses in unified form (substituting
`← hrest` to align bit positions) before the final `simp`.

## Option `pure` vs `some`

After `simp only` with `↓reduceIte` on spec functions, goals may have
`pure (...) = some (...)`. Add `pure` to the simp arguments to unfold it.

Note: `Option.pure` doesn't exist as a constant. Use `pure, Pure.pure` in simp
arguments to unfold monadic `return` in Option specs.

## `cases` + `bind` in Option do-notation Goals

After `cases h : f x with | some p =>`, the `cases` substitutes the constructor
in the goal, making `h` unnecessary for `simp`. But the bind wrapper
`Option.bind (some p) (fun ... => ...)` still needs reducing.
Use `simp only [bind, Option.bind]` (NOT `simp only [h]`).
When cleaning up unused simp argument warnings in this pattern, remove the
hypothesis name, keep `bind, Option.bind`.

## `simp` (not `simp only`) for Option do-notation Match Chains

When `unfold` expands a do-block in `Option`, the result is nested
`match opt?, fun val => ... with | none, _ => none | some a, f => f a`.
`simp only` CANNOT enter these match expressions to rewrite inner terms.
Use full `simp` (without `only`) with the relevant hypotheses to resolve all
match steps at once. This differs from `Except` monad do-blocks where
`simp only [bind, Option.bind]` suffices.

## `letFun` Linter False Positive

When `unfold f at h` leaves `have x := e; body` bindings, the `letFun`
wrapper must be reduced before `split at h` can see inner `if` expressions.

The linter flags `letFun` as unused in `simp only [letFun] at h` because
simp handles it via built-in reduction, not the named lemma. Replace with:
```lean
dsimp only at h  -- definitional reduction handles letFun
```
This eliminates the linter warning while performing the same reduction.

## Fixing `bind`/`Option.bind` Linter Warnings

**This is the most commonly rediscovered pattern in this codebase.**
If you're about to write `simp only [hX, bind, Option.bind]`, stop —
use the two-step pattern below instead.

The linter flags `bind` and `Option.bind` as unused in
`simp only [hX, bind, Option.bind]` because they contribute only via dsimp
(definitional simplification), not as rewrite rules. Do NOT suppress with
`set_option linter.unusedSimpArgs false` — use the two-step pattern instead:

```lean
-- Before (triggers linter warning):
simp only [hX, bind, Option.bind] at h ⊢

-- After (no warning):
rw [hX] at h; dsimp only [bind, Option.bind] at h ⊢
```

**Why**: `rw [hX]` substitutes the known value (e.g. `some (v, bits')`),
then `dsimp only [bind, Option.bind]` reduces `Option.bind (some ...) f`
to `f ...`. Neither step alone suffices — `simp only [hX]` without `bind`
cannot reduce the bind wrapper, and `dsimp only [bind, Option.bind]`
without `rw [hX]` cannot reduce when the scrutinee is opaque.

For standalone bind reduction (no hypothesis rewrite needed), replace
`simp only [bind, Option.bind]` with `dsimp only [bind, Option.bind]`.

The same pattern applies to `Except.bind`:
```lean
rw [hX] at h; dsimp only [bind, Except.bind] at h ⊢
```

## Guard Contradiction in `by_cases` Negative Branch

When `by_cases` splits on `(x == y) = true`, the negative branch gives
`¬(x == y) = true`, NOT `(x == y) = false`. To reduce a `guard` (or
`if ... then pure () else failure`) stuck in a hypothesis, first derive
the `= false` form:
```lean
have hfalse : (x == y) = false := by cases h : (x == y) <;> simp_all
rw [hfalse] at hspec
simp [guard, Bool.false_eq_true] at hspec  -- reduces to none = some, contradiction
```
Don't try `simp [hguard]` alone — it reduces the `if` but leaves
`guard False` or `match guard False, ...` unreduced.

## Avoid `do { if ... then return ...; rest }`

Creates `have __do_jp` join points in desugared form, making `h` and `⊢`
syntactically different after `unfold`. Use `if ... then some (...) else do { rest }`
instead. This applies to spec functions where proofs need to unfold both sides
simultaneously.

## Multi-Guard Except Unfolding (Framing Proofs)

Functions like `Gzip.decompressSingle` chain ~6 sequential `unless`/`if` guards
in the `Except` monad before calling core operations. Proving properties through
these requires systematic unfolding.

**How `unless` desugars:**
`unless cond do throw err` becomes `if ¬cond then Except.error err else pure ()`.
After `simp only [bind, Except.bind]`, this produces a stuck match on the guard
result.

**Tactic sequence for each guard:**

```lean
-- After: simp only [FuncName, bind, Except.bind] at h
-- h now contains: match (if ¬cond then .error msg else pure ()) with ...
by_cases hcond : cond
· simp [hcond] at h    -- guard passes → reduces stuck match, continue
· simp [hcond] at h    -- guard fails → h becomes .error = .ok, contradiction
```

**For long guard chains**, use nested `match` instead of `by_cases` to avoid
managing too many hypotheses:

```lean
simp only [Gzip.decompressSingle, bind, Except.bind] at h
-- Split on each monadic operation in sequence
match h1 : operation₁ with
| .error e => simp [h1] at h
| .ok (val₁, state₁) =>
  rw [h1] at h; simp only [] at h
  -- h now has the tail of the do-block
  match h2 : operation₂ with
  | .error e => simp [h2] at h
  | .ok (val₂, state₂) =>
    rw [h2] at h; simp only [] at h
    -- For unless/if guards between operations:
    by_cases hguard : guardCondition
    · simp [hguard] at h     -- contradiction
    · simp only [hguard] at h
      -- Continue with next operation...
```

**Key insight**: After each `match`/`cases` on a monadic result, use
`rw [h_result] at h; simp only [] at h` (NOT `simp [h_result] at h`) to
substitute the known result without over-simplifying. This is safer on
recursive functions where `simp` may loop.

**Extracting witnesses through guards**: When you need a specific result from
the chain, use `have` to establish existence first, then obtain:

```lean
have h_result : ∃ bytes, operation = .ok (bytes, finalState) := by
  revert h; intro h
  simp only [pure, Except.pure] at h
  by_cases hg1 : guard₁ <;> [simp [hg1] at h; simp only [hg1] at h]
  by_cases hg2 : guard₂ <;> [simp [hg2] at h; simp only [hg2] at h]
  match h3 : operation with
  | .error e => simp [h3] at h
  | .ok (val, st) => exact ⟨val, by simp [h3] at h; rw [h.2]⟩
obtain ⟨bytes, h_result⟩ := h_result
```

## Option Monad Lemma Kit for `readBitsLSB` Unfolding

When unfolding `readBitsLSB` do-notation in Option proofs, the standard
lemma set is:

```lean
simp only [Spec.readBitsLSB, Option.pure_def, Option.bind_eq_bind, Option.bind_some]
```

This set handles:
- `pure x` → `some x` (via `Option.pure_def`)
- `Option.bind (some x) f` → `f x` (via `Option.bind_eq_bind` + `Option.bind_some`)
- do-notation desugaring of `let x ← f; g x`

**When this kit is insufficient**: For deeply nested readBitsLSB calls
(e.g., reading 5+ bits with individual bit operations), you may also need
`List.cons.injEq` and `reduceCtorEq` for the list pattern matching. At
that point, bare `simp [Spec.readBitsLSB]` is acceptable (see the
"readBitsLSB as Computation Engine" section in `lean-simp-tactics`).

## `simp only` for Option Case Splits with `nomatch`

When case-splitting on monadic `Option` operations and a hypothesis `hgo`
tracks the overall computation result (e.g., `decode.go bits acc = some result`):

```lean
-- None branch (contradiction): substitute then close
| none => simp only [hX] at hgo; exact nomatch hgo

-- Some branch (continue): just substitute, don't inject yet
| some p =>
  obtain ⟨val, rest⟩ := p
  simp only [hX] at hgo

-- True branch of by_cases (extract equality): inject manually
· simp only [hf] at hgo; obtain rfl := Option.some.inj hgo
  exact some_prefix_lemma

-- False branch of by_cases (continue or contradiction):
· simp only [hf] at hgo
  -- If no more alternatives: exact nomatch hgo
  -- If more case splits needed: continue
```

**Pitfalls** (each of these cost a build cycle to debug):
- `↓reduceIte` is **unnecessary** with `simp only [hf]` — iota reduction
  handles `if true/false then A else B` automatically after hypothesis
  substitution. The linter flags it as unused.
- `hgo ▸ X` **fails** after `simp only` because `hgo` is
  `some X = some result`, not `X = result`. Use
  `obtain rfl := Option.some.inj hgo` instead.
- `Option.some.injEq` as a **simp arg** is flagged unused by the linter.
  Use `Option.some.inj` explicitly (not via simp).

## `dsimp` vs `simp` After `unfold` on Recursive Functions

**CRITICAL**: After `unfold F at h` on a recursive function, do NOT use
`simp only [F, bind, Except.bind] at h` — this may re-unfold `F` and loop.

Instead use:
```lean
unfold F at h
dsimp only [Bind.bind, Except.bind] at h
```

`dsimp` (definitional simp) reduces `bind`/`Except.bind` without unfolding
named definitions, so it won't re-enter `F`. This pattern is essential for
fuel-based recursive functions in the `Except` monad.

## `Except.ok.injEq` + `Prod.mk.injEq` Extraction Chains

Functions returning `Except ε (α × β)` (e.g., `readBit`, `readBits`,
`inflateBlock`) produce hypotheses like `Except.ok (val, rest) = Except.ok (x, y)`.
The canonical two-step extraction:

```lean
simp only [Except.ok.injEq, Prod.mk.injEq] at h
obtain ⟨hval, hrest⟩ := h
```

**Full pattern** after `split at h` on an Except-returning function:
```lean
split at h
· -- error branch: constructor discrimination
  exact nomatch h
· -- ok branch: extract pair components
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨hval, hrest⟩ := h
  -- hval : val = x, hrest : rest = y
```

This pattern appears 35+ times in BitReaderInvariant.lean and
InflateRawSuffix.lean. It is always `simp only` — never bare simp.

**Common extensions**:
- With `rfl` destructuring: `obtain ⟨rfl, rfl⟩ := h` when you want
  substitution rather than named equalities
- Chained with `simp_all`: `... at h <;> obtain ⟨_, rfl⟩ := h <;> simp_all`
  for one-liner proofs of BitReader invariants

**Anti-pattern**: Don't use bare `simp at h` for pair extraction — it
may rewrite terms you want to keep (e.g., simplifying `br.data.size`).

## Option.bind Chain Handling: `cases` + `dsimp` vs Bare `simp`

When a hypothesis or goal has nested `Option.bind` from do-notation,
choose the approach based on nesting depth:

### Shallow chains (≤3 levels): Sequential `cases` + `dsimp`

```lean
-- h : (do let x ← f a; let y ← g x; pure (x, y)) = some result
cases hf : f a with
| none => rw [hf] at h; dsimp only [bind, Option.bind] at h; exact nomatch h
| some x =>
  rw [hf] at h; dsimp only [bind, Option.bind] at h
  cases hg : g x with
  | none => rw [hg] at h; dsimp only [bind, Option.bind] at h; exact nomatch h
  | some y =>
    rw [hg] at h; dsimp only [bind, Option.bind] at h
    -- h is now fully reduced
```

### Deep chains (>3 levels): Bare `simp` with comment

```lean
-- 6-level bind chain in decodeDynamicTables
simp [hcl, hlit, hdist, hacc, hfinal, hresult] at hgo
-- bare simp: 6-level Option.bind chain
```

### Guard + bind interleaving

After `split at h` on an `if` inside a bind chain, the remaining
`match` on `Option.bind` may not reduce. Interleave a bind reduction:

```lean
split at h  -- splits the if
· -- true branch
  dsimp only [bind, Option.bind] at h  -- reduce the surrounding bind
  -- continue with next case split
```

This was independently rediscovered in 3+ sessions before being codified.
