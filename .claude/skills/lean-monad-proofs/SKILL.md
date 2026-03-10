---
name: lean-monad-proofs
description: Use when working on Lean 4 proofs involving Option or Except monad, do-notation unfolding, guard patterns, bind handling, join points, forIn loops in specifications, or Id monad loop invariants (Id.run do with for loops).
allowed-tools: Read, Bash, Grep
---

# Lean 4 Monad Proof Patterns

**`Except.mapError` in simp sets**: Use `Except.mapError.eq_2` (not
`Except.mapError`) to simplify `(.ok v).mapError f = .ok v`. The bare
`Except.mapError` unfolds to a match that simp may not fully reduce.
Also add `beq_self_eq_true` when the proof needs `(0 : Nat) == 0 = true`.

**Common pitfall**: `nomatch` fails inside `try` and `<;>` combinators —
use `next => exact nomatch h` instead. See "`nomatch` fails inside `try`"
section below.

## Avoid `for`/`while` in Spec Functions

In `Option`/`Except` monads, `return` inside a `for` loop exits the loop (producing
`some`), not the function. Use explicit recursive helper functions instead — they're
also easier to reason about in proofs. Reserve `for`/`while` for `IO` code.

**Critical reason: `while` loops are unprovable.** `while` in do-notation desugars
to `Lean.Loop.forIn`, which internally calls `Lean.Loop.forIn.loop` — a `partial`
definition. The kernel treats `partial` defs as axioms: they cannot be unfolded,
have no equation lemmas, and no properties can be proven about them.

**Workaround for existing `while`-based functions** (e.g., `weightsToMaxBits`):
1. Define a pure WF-recursive function that mirrors the loop logic
2. Prove properties about the pure version (sorry-free)
3. Bridge with a sorry: `imperativeVersion = pureVersion := by sorry`
4. Derive properties of the imperative version via the bridge

```lean
-- Pure spec version of a while loop that doubles `power` until `power ≥ ws`
def findMaxBitsLoop (ws bits power : Nat) (hpow : power ≥ 1) : Nat × Nat :=
  if h : power < ws then findMaxBitsLoop ws (bits + 1) (power * 2) (by omega)
  else (bits, power)
termination_by ws - power

-- Bridge (inherently sorry — partial defs are axioms)
theorem imperativeVersion_eq_spec : imperativeVersion x = pureSpec x := by sorry

-- Derive properties via the bridge
theorem imperativeVersion_valid : P (imperativeVersion x) := by
  rw [imperativeVersion_eq_spec]; exact pureSpec_valid x
```

This sorry is **irreducible** — it can only be eliminated by refactoring the
implementation to use explicit recursion instead of `while`.

## Unfolding do-notation with `Except.bind`

When a hypothesis `h` contains a `do` block (`let x ← f; g x`), use `cases hrd : f`
to split on the result BEFORE simplifying `h`. Then
`simp only [..., hrd, bind, Except.bind] at h` substitutes the known result.
This is cleaner than `simp [...] at h; split at h; rename_i ...` which produces
fragile unnamed hypotheses.

## `cases hrd : expr` Rewrites the Goal Too

When you write `cases hrd : f` where `f` appears in the goal (not just
in hypotheses), Lean rewrites `f` in the goal to the constructor value.
So if the goal contains `f = .ok rdval`, after `cases hrd : f` with
`| ok val =>`, the goal becomes `.ok val = .ok rdval` — and `hrd` has
type `f = .ok val`, NOT `.ok val = .ok val`.

**Consequence**: Use `rfl` (not `hrd`) to close the equality in the goal,
since the goal already has the constructor form on both sides. Using `hrd`
causes a type mismatch: `f = .ok val` vs `.ok val = .ok val`.

```lean
-- WRONG: type mismatch on hrd
cases hrd : br.readBits 4 with
| ok val => exact ⟨val, hrd⟩  -- hrd : br.readBits 4 = .ok val, but goal wants .ok val = .ok val

-- RIGHT: goal already has .ok val, use rfl
cases hrd : br.readBits 4 with
| ok val => exact ⟨val, rfl⟩
```

## do-notation Guards (`if ... then throw`)

Guards like `if cond then throw err` in `Except` do-notation expand to
`match (if cond then Except.error err else pure PUnit.unit) with | Except.error e => ... | Except.ok _ => ...`.
After splitting the outer condition with `split at h`, the `pure` branch leaves a
stuck `match`. Use `simp only [pure, Except.pure] at h` to reduce it, then continue
with the next `cases`/`split`.

## `pure PUnit.unit` Artifacts from Destructuring Bind

`let (a, b) ← expr` in Except do-notation desugars to TWO nested matches:
1. `match expr with | .error e => .error e | .ok v => ...` (the bind)
2. `match pure PUnit.unit with | .error e => .error e | .ok _ => ...` (artifact)

The second match is a no-op but `dsimp only []` cannot reduce it because
`pure` is not unfolded. After handling the first match with `cases`/`split`,
use:

```lean
simp only [pure, Pure.pure, Except.pure] at h
```

This unfolds `pure PUnit.unit` to `Except.ok PUnit.unit` and performs iota
reduction, collapsing the trivial match. Without this step, subsequent
`split at h` targets the wrong match expression.

## Non-Recursive Functions with Multiple Guards

For non-recursive `do` functions with multiple `if ... then throw` guards
(e.g., `parseSequencesHeader`), the cleanest approach is a **single-pass
simp** that reduces all monadic constructs at once, then `split at h`:

```lean
-- Reduce ALL bind/pure in one pass (safe for non-recursive functions)
simp only [parseSequencesHeader, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
-- Now h is plain nested if-then-else — split works cleanly
split at h
· exact nomatch h  -- error branch
· split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, -, rfl⟩ := h; omega
  ...
```

**Why not interleaved `dsimp`/`split`**: Each guard produces a `bind`
wrapper. With N guards, you'd need N rounds of `split` + `dsimp`. The
single-pass `simp only [F, Bind.bind, ...]` eliminates all wrappers at
once. This is safe because `F` is not recursive, so `simp` won't loop.

**For the goal** (forward proofs like `parseSequencesHeader_byte0_zero`),
the same single-pass works, followed by condition resolution:
```lean
simp only [parseSequencesHeader, Bind.bind, Except.bind, Pure.pure, Except.pure]
simp only [show ¬(data.size < pos + 1) from by omega, ↓reduceIte, hbyte,
  beq_self_eq_true]
```

Note: `beq_self_eq_true` is needed when hypothesis substitution produces
`(0 == 0) = true` as an if-condition — `↓reduceIte` alone won't reduce it.

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

### `nomatch` fails inside `try` and `<;>` combinators

**Problem**: `split at h <;> try exact nomatch h` does NOT work. `nomatch`
produces elaboration-level "Missing cases" errors, not tactic failures.
`try` only catches tactic failures, so the elaboration error leaks through.

**Solution**: Use `next =>` focusing to target the error branch specifically:

```lean
-- WRONG: elaboration error leaks through try
split at h <;> try exact nomatch h

-- RIGHT: next => focuses on first goal, closes it, leaves second goal
split at h
next => exact nomatch h
-- ... now work on the success branch

-- ALSO RIGHT: use contradiction in combinators (it fails gracefully)
split at h <;> first | contradiction | skip
```

**Rule**: Use `exact nomatch h` standalone or after `next =>`. Use
`contradiction` inside `first`, `try`, or `<;>` combinators.

### Batching error elimination in multi-branch functions

For functions with N branches where most are error paths, the efficient
pattern is `iterate` + `all_goals`:

```lean
iterate 5 (all_goals (try (first | contradiction | (split at h))))
all_goals first
  | contradiction
  | (simp only [Except.ok.injEq, Prod.mk.injEq] at h
     obtain ⟨-, rfl⟩ := h; omega)
```

This closes all error branches automatically, leaving only the success
branches for manual work.

## Completeness Proofs (Function Succeeds Under Preconditions)

When proving `∃ result, f x = .ok result` (the function succeeds),
the cleanest approach is **backward**: case-split on the result, derive
`False` on the error branch.

**Key pattern for `cases hres : f x`**: After `cases hres`, the GOAL
has `.ok val` or `.error e` (not `f x`). So the `ok` branch uses `rfl`,
not `hres`:

```lean
cases hres : f x with
| ok val => obtain ⟨a, b⟩ := val; exact ⟨a, b, rfl⟩  -- NOT hres
| error e => exfalso; ...
```

**Synchronizing case analysis across hypotheses**: When the function
and a size hypothesis both depend on the same expressions (e.g.,
descriptor byte fields), use `generalize` to abstract shared
sub-expressions into variables present in BOTH `hres` and `hsize`.
Then `by_cases`/`split at hres` substitutes consistently:

```lean
-- Generalize shared expressions into both hres and hsize
generalize hss : (desc >>> 5 &&& 1 == 1) = ss at hres hsize
generalize hdf : (desc &&& 3).toNat = df at hres hsize
-- by_cases on Bool substitutes in ALL hypotheses
by_cases hss_val : ss = true
· simp only [hss_val, ...] at hres hsize
  -- Now split walks through remaining guards
  repeat (first | contradiction | (simp [...] at hsize; omega) | (split at hres))
```

**Why `generalize` is needed**: Without it, `split at hres` creates
branches where the discriminant value is known in `hres` but NOT in
`hsize`, so `omega` can't derive contradictions from size bounds.

**Reducing `if false = true then ...` for omega**: After substituting
`ss = false`, expressions like `if false = true then 0 else 1` remain
opaque to `omega`. Use `simp only [Bool.false_eq_true, ite_false]` to
reduce them to concrete values before `omega`.

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

### Constructor Inequality After Struct Substitution

When proving `¬ Constructor1 = Constructor2` after monadic unfolding, `decide`
fails if the goal or context contains free variables (e.g., `data[pos]!` in
struct fields). The pattern:

```lean
-- After: simp only [bind, Except.bind, pure, Except.pure] at h
-- h : Except.ok ({field1 := expr_with_free_vars, field2 := .raw, ...}, pos + 3)
--     = Except.ok (hdr, pos')
-- Goal: ¬ hdr.field2 = .reserved
-- WRONG: decide  -- fails: "Expected type must not contain free variables"
-- WRONG: intro h; exact nomatch h  -- fails: "Missing cases: Eq.refl"
-- RIGHT: substitute the struct first, THEN discriminate
obtain ⟨rfl, rfl⟩ := h  -- substitutes hdr := {field2 := .raw, ...}
exact fun h => nomatch h  -- now .raw = .reserved has no free vars
```

The key insight: `obtain ⟨rfl, rfl⟩` substitutes the struct into the goal,
replacing `hdr.field2` with the concrete constructor (e.g., `.raw`). Only
then can `nomatch` (or `decide`) discriminate the constructors.

### `subst` leaves struct projections unreduced

When `h : { field1 := e1, field2 := e2 } = result` and you `subst h`, Lean
replaces `result` with the struct literal but does NOT reduce projections like
`result.field1` → they remain as `{ field1 := e1, ... }.field1`. This causes
`exact hwm` to fail when `hwm` expects the reduced form.

**Workaround**: Use `constructor` to split the goal, then `rw [← h]` (which
rewrites with the equation directly) instead of `subst h`:

```lean
-- BAD: subst h leaves { maxBits := m, ... }.maxBits unreduced
simp only [Except.ok.injEq] at h; subst h
exact ⟨hwm, ...⟩  -- fails: hwm is about `m`, goal has `{ maxBits := m, ... }.maxBits`

-- GOOD: use rw to avoid the projection issue
simp only [Except.ok.injEq] at h
constructor
· rw [← h]  -- rewrites result.maxBits to m directly
· subst h; ...  -- subst is fine when projections aren't in the goal
```

## `eq_of_beq` for BEq-to-Eq Conversion

When a monadic function uses `bne` or `==` for guards (e.g.,
`if magic != expected then throw ...`), the negative branch gives
`¬(a != b) = true` or `¬(a == b) = true`. To extract `a = b`:

```lean
-- After: by_cases hmagic : (magic != expected) = true
-- Negative branch gives: hmagic : ¬(magic != expected) = true
-- First derive the BEq equality:
have heq : (magic == expected) = true := by
  cases h : (magic == expected) <;> simp_all
-- Then convert to propositional equality:
exact eq_of_beq heq
```

**`eq_of_beq`** works for any type with a `LawfulBEq` instance (including
`UInt32`, `UInt8`, `String`, etc.). It converts `(a == b) = true` to `a = b`.

**Common context**: After `by_cases` on a `bne` guard, you need to derive
the positive `==` form before `eq_of_beq` can be applied. The
`cases h : (a == b) <;> simp_all` idiom handles the Boolean case split.

**Anti-pattern**: Don't use `simp [bne, BEq.beq]` to try to normalize
`bne` — it creates large intermediate terms on big hypotheses. Use the
targeted `cases` + `eq_of_beq` pattern instead.

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

## `forIn` Loop Invariants in the `Id` Monad

Functions using `Id.run do` with `for` loops (e.g., `buildFseTableCells`) desugar to
chains of `forIn (m := Id) [:n] init body`. To prove properties preserved across
loops, use a loop invariant lemma like `range_forIn_inv`.

**Metavariable trap**: When using `have := range_forIn_inv n _ _ P hinit hf`,
the body function `f` is a metavariable `?m` during `hf` elaboration. Tactics
like `split` fail because they can't find `if`/`match` in `?m x b`.

**Fix**: Pass the `heq` equation (from `split; rename_i ... heq`) as an early
argument so Lean resolves `f` before elaborating `hf`:

```lean
-- Helper that resolves f from heq before elaborating hf:
private theorem forIn_fst_size_of_heq {α β : Type} {n k : Nat}
    {init : MProd (Array α) β}
    {f : Nat → MProd (Array α) β → Id (ForInStep (MProd (Array α) β))}
    {result : Array α} {rest : β}
    (heq : forIn (m := Id) [:n] init f = ⟨result, rest⟩)
    (hinit : init.fst.size = k)
    (hf : ∀ a b, b.fst.size = k → ∃ b', f a b = ForInStep.yield b' ∧ b'.fst.size = k) :
    result.size = k := ...

-- Usage: f is resolved from heq₁ before hf is elaborated
have h₁ : cells₁.size = 1 <<< al :=
  forIn_fst_size_of_heq heq₁ (by simp) (fun _ b hb => by
    split  -- NOW works because f is concrete
    · exact ⟨_, rfl, by simp [Array.size_setIfInBounds, hb]⟩
    · exact ⟨_, rfl, hb⟩)
```

**Key pattern for `Id.run do` proofs**:
1. `unfold f; simp only [Id.run, pure, Pure.pure, Bind.bind]` to reduce do-block
2. `split; rename_i ... heq` to destructure each `match` on loop results
3. Use `forIn_fst_size_of_heq heq ...` (not `range_forIn_inv _ _ _ P ...`)

**For nested loops** (e.g., inner `for` inside outer `for`), `split` inside
the outer `hf` proof to reach the inner `match`, then use
`forIn_fst_size_of_heq heq_inner ...` for the inner loop.

## `forIn` with Yield-Only Body → `Array.foldl`

When a `for w in arr do` loop in `Except` always yields (no `break`/`return`),
the `forIn` result equals the corresponding `Array.foldl`. Three steps are needed:

### Step 1: Simplify do-notation desugaring artifacts

Mutable variable assignment in `for` loops desugars to
`match pure PUnit.unit with | .error => ... | .ok v => ...` wrappers.
Simplify with:
```lean
simp only [pure, Pure.pure, Except.pure] at heq_forIn
```

### Step 2: Factor `Except.ok (ForInStep.yield ...)` out of `if` branches

The body may have `if c then ok (yield a) else ok (yield b)` which must become
`ok (yield (if c then a else b))`:
```lean
simp only [show ∀ (w : UInt8) (r : Nat),
    (if w.toNat > 0 then Except.ok (ForInStep.yield (r + f w))
     else (Except.ok (ForInStep.yield r) : Except ε (ForInStep Nat))) =
    Except.ok (ForInStep.yield (if w.toNat > 0 then r + f w else r))
  from fun w r => by split <;> rfl] at heq_forIn
```

### Step 3: Apply `forIn_pure_yield_eq_foldl`

```lean
rw [forIn_pure_yield_eq_foldl] at heq_forIn
exact (Except.ok.inj heq_forIn).symm
```

### Critical: Match expression matching in `simp`/`rw`

**Lean 4's `simp`/`rw` CANNOT match syntactically identical `match`
expressions from different elaboration contexts.** Two `match` blocks that
print identically may have different internal `casesOn` representations.

This means a separately proved lemma about `List.foldlM` with a `match`
body CANNOT be applied via `simp`/`rw` to a `foldlM` expression whose
`match` came from `Array.forIn_eq_foldlM`.

**Workaround**: Prove by `generalize` + induction directly on the goal,
so the `match` expression is the one from the goal itself:

```lean
rw [Array.forIn_eq_foldlM, ← Array.foldlM_toList, ← Array.foldl_toList]
generalize as.toList = l
revert init
induction l with
| nil => intro init; rfl
| cons x l ih =>
  intro init
  simp only [List.foldlM, bind, Except.bind, List.foldl_cons]
  exact ih (f x init)
```

## When to Use `split at h` vs `by_cases`

**Choose based on the function size** after unfolding:

| Function size | Recommended | Why |
|---------------|-------------|-----|
| < 15 branches | `split at h` | Fast, automatic, handles `if`/`match` uniformly |
| 15-25 branches | Try `split`, fall back to `by_cases` | May or may not hit step limit |
| > 25 branches or `let mut` | `by_cases` + `rw [if_pos/if_neg]` | `split` will definitely hit step limit |

**Key indicators favoring `by_cases`**:
- Function uses `let mut` (mutable state in `do`) — desugars into a large
  nested match that multiplies the term size.
- Guards use `BEq` comparisons (e.g., `x == 0`) — `split at h` creates
  stuck `Decidable.rec` expressions or inaccessible hypotheses from `BEq`
  conditions. `by_cases` with `beq_iff_eq` normalization avoids this.
- Guard wraps `Except.bind` around a conditional — `split at h` may split
  at the wrong level (the `Except.bind` rather than the guard condition).

**Worked examples**:
- `decodeFseDistribution_accuracyLog_ge` in `Zip/Spec/Fse.lean` — uses
  `split at h` (medium-size function, ~15 branches)
- `parseFrameHeader_magic` in `Zip/Spec/Zstd.lean` — uses `by_cases` +
  `rw` (large function with `let mut`, `split` fails)
- `parseSequencesHeader_numSeq_small` — uses `by_cases` because `BEq`
  guards create inaccessible hypotheses with `split at h`
- `parseHuffmanTreeDescriptor_pos_gt` — uses `by_cases` because `split
  at h` creates stuck `Decidable.rec` in the FSE path

### Destructured tuple arguments avoid projection issues

When a function returns a tuple like `(Nat × Nat × Nat × Bool)`, using
destructured arguments in helper lemma signatures avoids tuple projection
reduction issues:

```lean
-- WRONG: omega can't reduce v.1, v.2.1, v.2.2.1
theorem myLemma (v : Nat × Nat × Nat × Bool) (h : ...) : v.1 ≤ 1000 := by
  omega  -- fails: can't see through projections

-- RIGHT: destructuring gives omega direct access to the components
theorem myLemma (regen comp hdr : Nat) (fs : Bool) (h : ...) : regen ≤ 1000 := by
  omega  -- works: regen is a plain Nat
```

This pattern was essential in `parseLiteralsSection` proofs where the
header is a 4-tuple.

## `grind` for Struct Field Extraction from Bind Chains

When a function always returns `.ok { field := input, ... }` through deeply
nested bind chains (e.g., `buildFseTable` returns `{ accuracyLog := al, ... }`),
proving `result.field = input` after success:

```lean
-- Pattern: prove table.accuracyLog = al given buildFseTable probs al = .ok table
simp only [buildFseTable, bind, Except.bind, pure, Except.pure] at h
grind
```

**Why this works**: `simp only` reduces all bind/pure wrappers, leaving a
deeply nested `match` chain that always ends in `Except.ok { field := al, ... }`.
`grind` can extract the struct field equality from this reduced term.

**When this fails**: If the field depends on loop iterations (e.g., array size
after `forIn` modifications), `grind` cannot reason through the loop body.
See the `forIn` limitation below.

### `grind` as finishing tactic for monadic case-splitting

`grind` is also useful as a finishing tactic when the goal involves nested
monadic matches on structure fields that `split` cannot decompose:

```lean
-- After unfolding and peeling error branches, the goal has
-- nested matches on struct fields (checksum guard, etc.)
grind  -- handles the remaining case analysis automatically
```

**When to use `grind` over `split`/`simp`**:
- Nested `match` on structure fields (`hdr.isLastBlock`, `desc.checksum`)
  that `split` cannot target because the scrutinee is a field accessor
- Multi-branch functions where all branches lead to the same conclusion
  (e.g., proving `pos' ≤ data.size` regardless of which branch was taken)
- After `simp only [...]` has reduced bind/pure but leaves complex
  conditional structure

**When NOT to use `grind`**:
- When you need specific hypotheses from cases (use `split at h` instead)
- For loop invariants — `grind` cannot reason through `forIn` or
  WF-recursive calls
- When `omega` alone suffices (prefer `omega` for pure arithmetic)

## Multi-Bind Chains with State Threading (decompressFrame Pattern)

Functions like `decompressFrame` chain 5-10 monadic operations where each
returns `(result, updatedState)` and the state threads through:

```lean
do
  let (magic, br₁) ← readU32 br
  unless magic == 0xFD2FB528 do throw .badMagic
  let (hdr, br₂) ← parseFrameHeader br₁
  let (blocks, br₃) ← decompressBlocks br₂ hdr
  let (checksum, br₄) ← readChecksum br₃
  ...
```

### Proof strategy for properties through long chains

When proving a property about the final output (e.g., output size matches
content size, or checksum is valid):

1. **Unfold and reduce the first bind**:
   ```lean
   simp only [decompressFrame, bind, Except.bind] at h
   cases hread : readU32 br with
   | error e => simp only [hread] at h; exact nomatch h
   | ok val =>
     obtain ⟨magic, br₁⟩ := val
     simp only [hread] at h; dsimp only [bind, Except.bind] at h
   ```

2. **Handle each guard between operations**:
   ```lean
   by_cases hmagic : magic == expected
   · simp only [hmagic] at h; dsimp only [bind, Except.bind] at h
   · simp only [hmagic] at h; exact nomatch h
   ```

3. **Thread through remaining operations** repeating steps 1-2.

4. **At the final `pure`/`return`**: extract the result with
   `simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h`
   then `obtain ⟨rfl, rfl⟩ := h`.

### When the chain is too deep (>6 operations)

Rather than mechanically peeling all layers, prove **per-operation lemmas**
for each step's contribution to the property, then compose:

```lean
-- Lemma: parseFrameHeader preserves br.data
theorem parseFrameHeader_data (h : parseFrameHeader br = .ok (hdr, br')) :
    br'.data = br.data := by ...

-- Main theorem: compose per-operation results
theorem decompressFrame_output_size ... := by
  have hd₁ := readU32_data h₁
  have hd₂ := parseFrameHeader_data h₂
  have hd₃ := decompressBlocks_data h₃
  ...
```

This scales better than monolithic unfolding and produces reusable lemmas.

## `forIn` Loop Invariants Are Not Automatable

**Current gap**: There is no standard library theorem for proving properties
preserved through `forIn` iterations in the `Except` monad. Tactics like
`grind`, `simp`, and `omega` cannot see through the opaque `forIn` wrapper.

Example: proving `cells.size = tableSize` after a loop that only uses
`Array.set!` (which preserves size) requires a loop invariant theorem:
"if `P` holds initially and each iteration preserves `P`, then `P` holds
on the result." This doesn't exist for `Std.Legacy.Range.forIn'` in `Except`.

**Workaround**: Leave as `sorry` with documentation. This is a known
standard library gap, not a proof technique issue.

## Nested `match` Within `do` Blocks

When a `do` block contains `match expr with | ctor₁ => ... | ctor₂ => ...`,
the do-notation desugaring wraps each branch in bind continuations, producing
deeply nested terms. Two patterns arise:

### Pattern 1: Match on a pure value mid-chain

```lean
-- Implementation:
do
  let hdr ← parseHeader br
  match hdr.blockType with
  | .raw => handleRaw hdr br
  | .rle => handleRle hdr br
  | .compressed => handleCompressed hdr br
  | .reserved => throw .invalidBlockType
```

After `cases hparse : parseHeader br` and extracting the ok branch,
the remaining hypothesis contains the `match`. Use `cases` on the
discriminant directly:

```lean
cases hbt : hdr.blockType with
| raw => simp only [hbt] at h; ...
| rle => simp only [hbt] at h; ...
| compressed => simp only [hbt] at h; ...
| reserved => simp only [hbt] at h; exact nomatch h
```

**Key**: `simp only [hbt]` reduces the `match` to the selected branch.
Don't use `split at h` here — it generates too many subgoals when the
hypothesis also contains subsequent binds.

### Pattern 2: Match on a monadic result that feeds subsequent binds

```lean
do
  let result ← operation₁
  let next ← match result with
    | .modeA => operationA
    | .modeB => operationB
  finalOperation next
```

This produces nested `Except.bind (match result with ...) (fun next => ...)`.
Unfold the match first, THEN handle the bind:

```lean
cases hmode : result with
| modeA =>
  simp only [hmode] at h
  dsimp only [bind, Except.bind] at h
  -- h now has operationA >>= finalOperation
| modeB => ...
```

### Anti-pattern: `split at h` on match-within-bind

`split at h` when the match is wrapped in `Except.bind` creates subgoals
where `h` retains the outer bind wrapper around a partially-reduced match.
Use `cases` on the discriminant + `simp only` to reduce cleanly.

## `split at h` Chains with `letFun` Interleaving

When unfolding a function that chains multiple guards (e.g.,
`executeSequences.loop`), successive `split at h` calls may stall
because Lean inserts `letFun` wrappers between branches. Interleave
`dsimp only [letFun]` between splits:

```lean
rw [executeSequences.loop.eq_2] at h
split at h
· simp at h  -- error branch
· rename_i hlit
  split at h
  dsimp only [letFun] at h  -- ← required between splits
  split at h
  · simp at h  -- error branch
  · split at h
    · simp at h
    · -- success path: apply IH
      have ⟨ih_size, ih_le, ih_bound⟩ := ih _ _ _ hlp' h
```

**Key insight**: `letFun` appears when the desugared `do` block
creates `have x := expr; body` bindings between monadic operations.
Without `dsimp only [letFun]`, the next `split at h` cannot see the
inner `if`/`match` expressions.

## Inline `show` Proofs for Condition Resolution

When `simp only` needs a proof that a condition is true or false,
use inline `show ... from by omega` instead of a separate `have`:

```lean
-- Compact: condition proofs inline
simp only [resolveOffset, show ¬(2 > 3) from by omega,
  show litLen > 0 from hlit, ↓reduceIte]

-- Verbose equivalent (avoid):
have h1 : ¬(2 > 3) := by omega
have h2 : litLen > 0 := hlit
simp only [resolveOffset, h1, h2, ↓reduceIte]
```

This pattern is especially useful for resolving multiple `if` conditions
in a single `simp only` call. Each `show P from proof` provides `P`
as a simp argument without polluting the local context.

## `split at h` Step Limit on Large Unfolded Functions

**Problem**: `split at h` uses `simp` internally. On large unfolded functions
(e.g., `parseFrameHeader` with mutable state and many guards), it hits the
simp step limit: `` `simp` failed: maximum number of steps exceeded ``.

**Solution**: Use `by_cases` + `rw [if_pos/if_neg]` instead of `split at h`:

```lean
-- Instead of: split at h (hits step limit)
-- Do:
by_cases hcond : condition
· rw [if_pos hcond] at h; exact nomatch h   -- throws → contradiction
· rw [if_neg hcond] at h                     -- continues
  -- For match on pure PUnit.unit after rw:
  simp only [pure, Pure.pure] at h           -- reduces to .ok branch
```

**Why this works**: `rw [if_pos/if_neg]` does a targeted rewrite without
traversing the whole term. `split at h` tries to analyze the entire
hypothesis to find the match/ite, which is expensive on large terms.

**Also avoid `simp [bne, hb]` on large hypotheses**. Instead, use targeted
`show` + `rw` for Bool goals like `(!false) = true`:
```lean
exfalso; apply hmagic
show (!(a == b)) = true
rw [hb]  -- hb : (a == b) = false, goal becomes (!false) = true
-- rfl closes it
```

## `repeat split at h` Is Depth-First — Use `iterate` for Breadth

**Problem**: `repeat split at h` follows ONE depth-first branch to
completion, leaving all other goals with partially-split hypotheses.
After it finishes, remaining goals still have `if`/`match` in `h`.

**Solution**: Use `iterate N (all_goals (try (first | contradiction | (split at h))))`:

```lean
-- After by_cases eliminates error guards and initial split at h:
repeat split at h          -- depth-first: only processes one branch
iterate 5 (all_goals (try (first | contradiction | (split at h))))
-- Now ALL goals either closed by contradiction or fully split
all_goals first
  | contradiction
  | (simp only [Except.ok.injEq, Prod.mk.injEq] at h
     obtain ⟨-, rfl⟩ := h; omega)
```

**Why `contradiction` not `nomatch` in `first`**: `nomatch` produces
elaboration errors that `first` cannot catch (not a tactic failure).
`contradiction` is a proper tactic that fails gracefully. Use
`contradiction` inside `first` combinators, `exact nomatch h` standalone.

**Worked example**: `parseFrameHeader_pos_gt` in `Zip/Spec/Zstd.lean` —
uses `by_cases` for 3 error guards, `split at h` for the singleSegment
branch, then `iterate 5 (all_goals ...)` to process remaining branches.

## Private Functions Are Opaque Cross-Module

**Problem**: `private def` functions in module A cannot be unfolded by `simp only`
in module B. After `simp only [callingFunction, ...]`, the private function appears
as `Module.privateFunc✝` (with hygiene suffix) in hypotheses. You cannot reference
it by name, unfold it, or apply lemmas about it.

**Symptoms**:
- `simp only [privateFunc, ...]` fails with "Unknown identifier"
- `split at h` on the private call only gives error/ok (bind result), not internal branches
- You need properties of the private function's output but can't prove them

**Solution**: Either remove `private` or add a public helper lemma in the same module:

```lean
-- Option 1: Remove private (simplest, when encapsulation isn't critical)
-- Change: private def parseHeader → def parseHeader

-- Option 2: Add a public lemma in the SAME file as the private def
-- (private defs CAN be referenced by non-private theorems in the same file)
theorem parseHeader_headerBytes_ge (h : parseHeader data pos fmt = .ok (a, b, hdr, fs)) :
    hdr ≥ 3 := by
  simp only [parseHeader, ...] at h  -- works: same module
  ...
```

**Key insight**: Check `private` visibility BEFORE writing the proof. If a proof
needs to reason about a function's internals (not just its success/failure), and
that function is `private` in another module, address visibility first.

**Tuple projection gotcha**: After `subst h` where `h : tuple = v`, projections
like `v.2.2.fst` remain unreduced. Use destructured arguments in helper lemmas:
```lean
-- BAD: v.2.2.fst doesn't reduce for omega
theorem helper (h : f x = .ok v) : v.2.2.fst ≥ 3 := by ...

-- GOOD: hdr is a plain Nat, omega works directly
theorem helper (h : f x = .ok (a, b, hdr, fs)) : hdr ≥ 3 := by ...
```

## BackwardBitReader Proof Patterns

The `BackwardBitReader` in `Zip/Native/Fse.lean` reads bits MSB-first from a
backward bitstream. Its `readBits` function uses an inner `readBits.go` loop
with a `Nat` count parameter (fuel-like but well-founded). Three proof patterns
have emerged for reasoning about it.

### Induction on the count parameter

`readBits.go br k acc` recurses on `k`. Proofs about it use:

```lean
induction k generalizing br acc with
| zero =>
  -- Base: readBits.go _ 0 acc = .ok (acc, br)
  simp only [BackwardBitReader.readBits.go] at h
  obtain ⟨rfl, _⟩ := Prod.mk.inj (Except.ok.inj h)
  ...
| succ k ih =>
  -- Step: unfold one iteration, split on bitsRemaining == 0
  simp only [BackwardBitReader.readBits.go, bind, Except.bind] at h
  split at h
  · exact nomatch h  -- error: no bits remaining
  · simp only [pure, Except.pure] at h
    -- Apply IH with updated br and acc
    refine ih _ _ ... h
```

**Key**: `generalizing br acc` is essential because both change at each step.

### Accumulator value bound invariant

To prove `readBits n` produces `val.toNat < 2^n`, track the invariant
`acc.toNat < 2^(n-k)` through the loop. The inductive step shows that
`(acc <<< 1) ||| bit` preserves the bound with one more bit:

```lean
-- The invariant: acc < 2^(n-k) → result < 2^n
private theorem readBits_go_value_bound {n : Nat}
    (br : BackwardBitReader) (k : Nat) (acc val : UInt32)
    (hkn : k ≤ n) (hacc : acc.toNat < 2 ^ (n - k))
    (h : readBits.go br k acc = .ok (val, br')) :
    val.toNat < 2 ^ n := by
  induction k generalizing br acc ...
```

The wrapper theorem instantiates with `k = n`, `acc = 0`:
```lean
theorem readBits_value_lt_pow2 ... :=
  readBits_go_value_bound br n 0 val br' (Nat.le_refl n) (by simp) h
```

This pattern (inner loop invariant → wrapper instantiation) applies to any
accumulator-based loop in `Except`.

### `totalBitsRemaining` as decreasing measure

`totalBitsRemaining br` counts `bitsRemaining + 8 * (bytePos - startPos)`.
For termination/progress proofs about callers that loop over `readBits`:

1. Prove `readBits` decreases `totalBitsRemaining` when it succeeds
2. Use `totalBitsRemaining` as the termination measure for outer loops

The key helper `readBits_go_totalBitsRemaining_decreasing` shows that
each successful bit read strictly decreases the total. The outer function
then composes: `readBits n` decreases by at least `n` bits (when
`n > 0` and enough bits are available).

## `MProd` vs `Prod` in `do`-Notation State

**Problem**: Desugared `do`-notation with mutable variables uses `MProd`
(mutable pair) for tuple state, NOT `Prod` (`×`). This causes type
mismatches when pattern-matching or destructuring loop state.

```lean
-- After desugaring, a do block with `let mut a := ...; let mut b := ...`
-- creates state of type `MProd (Array α) β`, NOT `Array α × β`.
-- Pattern matching must use ⟨fst, snd⟩ (anonymous) or MProd.mk, not (a, b).
```

**Symptoms**:
- `split; rename_i ... heq` gives `heq : forIn ... init f = ⟨result, rest⟩`
  where the pair is `MProd`, not `Prod`
- `obtain ⟨a, b⟩ := val` fails with type mismatch on `Prod` vs `MProd`
- Hypothesis shows `MProd.fst` and `MProd.snd` instead of `Prod.fst`/`Prod.snd`

**Solution**: Use `MProd` explicitly in invariant types and helper lemmas:

```lean
-- Helper theorem must use MProd, not Prod:
private theorem forIn_fst_size_of_heq {α β : Type} {n k : Nat}
    {init : MProd (Array α) β}  -- NOT: Array α × β
    {f : Nat → MProd (Array α) β → Id (ForInStep (MProd (Array α) β))}
    ...

-- In proofs, access fields via .fst/.snd:
have h₁ : cells₁.size = 1 <<< al :=
  forIn_fst_size_of_heq heq₁ (by simp) (fun _ b hb => ...)
```

**Detection**: If `split; rename_i` on a `forIn` result gives a type
involving `MProd`, all downstream lemmas and patterns must use `MProd`.

## Counter vs Element in `forIn_range_preserves_indexed`

**Problem**: `forIn_range_preserves_indexed` callbacks receive both a
counter `k : Nat` and an element `a : Nat`. For `[:n]` ranges, these
are numerically equal (`k = a`), but Lean treats them as distinct
variables. Using the wrong one causes `omega` failures.

```lean
-- The callback signature:
-- fun (k : Nat) (a : Nat) (b : β) (b' : β) => ...
-- k = counter (0, 1, 2, ...), a = element from the range
-- For [:n], k = a, but they are distinct free variables

-- WRONG: using k when the goal needs a (the element)
intro k _ b b' hk hinv heq
have hcount : v[k]! ≤ bound := ...  -- k might not match goal terms

-- RIGHT: name the element and use it
intro k kv b b' hk hinv heq
have hcount : v[kv]! ≤ bound := ...  -- kv matches goal terms
```

**Symptoms**:
- `omega` fails on a goal that "looks" provable
- Hypotheses mention `k` but the goal uses `a✝¹` (auto-named element)
- `exact hinv _` type-checks but `omega` can't close the arithmetic

**Solution**: Always name the element variable (don't use `_`) and use
it consistently in `have` statements. For `[:n]`, the element is what
appears in array indexing expressions in the goal.

## `omega` Limitations with `Except.ok.injEq` Conjunctions

After `simp only [Except.ok.injEq, Prod.mk.injEq] at h`, the hypothesis is a
conjunction like `A ∧ B ∧ C ∧ D`. **omega cannot decompose this conjunction if
any conjunct contains non-linear terms** (bitwise `&&&`, `>>>`, `|||`).

```lean
-- BAD: omega can't extract `3 = headerSize` from the conjunction
simp only [Except.ok.injEq, Prod.mk.injEq] at h
-- h : (raw >>> 4) &&& 0x3FF = regen ∧ ... ∧ 3 = headerSize ∧ ...
omega  -- FAILS: can't decompose h

-- GOOD: extract the needed component first
simp only [Except.ok.injEq, Prod.mk.injEq] at h
obtain ⟨-, -, hhdr, -⟩ := h
-- hhdr : 3 = headerSize
omega  -- succeeds
```

**Related**: `split at h` on `if (x == y) then ...` (Bool condition) produces
`h✝ : (x == y) = true` or `h✝ : ¬(x == y) = true`. Omega cannot use these.
Convert with `simp only [beq_iff_eq] at *` before omega:

```lean
-- After split on `if sizeFormat == 2 then ...`
-- h✝ : (sizeFormat == 2) = true   ← omega can't use this
simp only [beq_iff_eq] at *
-- h✝ : sizeFormat = 2             ← omega handles this
omega  -- now succeeds for contradiction cases
```

Note: `split at h` on `if x ≤ y then ...` (Prop condition) produces
`h✝ : x ≤ y` directly — no conversion needed. The issue is specific to
Bool-valued `==`/`!=` conditions.

## Cross-References

- **Dependent `if` preserving hypotheses through `do` blocks**:
  `lean-wf-recursion` skill, "Dependent `if` Hypotheses and `do` Early-Throw".
  Critical when monadic functions need termination proofs later in the block.
  Use `if hoff : cond then .error ... else do ...` not `do; if cond then throw ...`.
- **`simp only` vs bare `simp` decisions**: `lean-simp-tactics` skill,
  "Bare `simp` Resistant Patterns" section.
- **WF function unfolding** (`rw [f.eq_1]` not `simp only [f]`):
  `lean-wf-recursion` skill. Never use `simp only [f]` on recursive functions.
- **Loop invariant proofs for Zstd spec**: `lean-zstd-spec-pattern` skill,
  "Loop Invariant Theorems via Equation Lemma Matching".
