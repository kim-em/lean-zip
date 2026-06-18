---
name: lean-monad-proofs
description: Use when working on Lean 4 proofs involving Option or Except monad, do-notation unfolding, guard patterns, bind handling, join points, forIn loops in specifications, or Id monad loop invariants (Id.run do with for loops).
allowed-tools: Read, Bash, Grep
---

# Lean 4 Monad Proof Patterns

# Spec function shape

## Avoid `for`/`while` in spec functions
In `Option`/`Except` monads, `return` inside a `for` loop exits the loop (producing
`some`), not the function. `while` desugars to `Lean.Loop.forIn` → `Lean.Loop.forIn.loop`,
a `partial` def the kernel treats as an axiom: no unfolding, no equation lemmas, no
provable properties. Use explicit recursive helpers. Reserve `for`/`while` for `IO`.

Workaround for an existing `while`-based function (e.g. `weightsToMaxBits`):
define a pure WF-recursive mirror, prove its properties sorry-free, bridge with an
irreducible `imperativeVersion x = pureSpec x := by sorry`, derive via `rw`.

```lean
def findMaxBitsLoop (ws bits power : Nat) (hpow : power ≥ 1) : Nat × Nat :=
  if h : power < ws then findMaxBitsLoop ws (bits + 1) (power * 2) (by omega)
  else (bits, power)
termination_by ws - power
```

## Avoid `do { if cond then return x; rest }`
Creates `__do_jp` join points: hypothesis uses `__do_jp` while the goal has the inline
form, so they look identical after `unfold` but don't match. Write
`if cond then some x else do { rest }` instead. Same for early `return` mid-`do`.

# Unfolding bind chains

## `Except.bind`: `cases hrd : f` before simplifying
Split on the result first, THEN substitute:
`cases hrd : f` then `simp only [..., hrd, bind, Except.bind] at h`. Cleaner than
`simp [...] at h; split at h; rename_i ...` (fragile unnamed hypotheses).

## `cases hrd : expr` rewrites the goal too
When `f` appears in the goal, `cases hrd : f with | ok val =>` rewrites it to `.ok val`,
and `hrd : f = .ok val`. So the goal is already `.ok val = .ok val` — close with `rfl`,
NOT `hrd` (which would be `f = .ok val`, a type mismatch). Same for completeness proofs
`∃ result, f x = .ok result`: after `cases hres : f x`, the ok branch uses `rfl`.

## `bind`/`Option.bind` linter warnings: two-step `rw` + `dsimp`
Most commonly rediscovered pattern. The linter flags `bind`/`Option.bind` as unused in
`simp only [hX, bind, Option.bind]` (they contribute only via dsimp). Do NOT suppress.

```lean
-- Before (warning):  simp only [hX, bind, Option.bind] at h ⊢
-- After:
rw [hX] at h; dsimp only [bind, Option.bind] at h ⊢
```
Neither step alone suffices: `simp only [hX]` can't reduce the bind wrapper; `dsimp`
alone can't reduce an opaque scrutinee. Same for `Except.bind`. For standalone bind
reduction (no rewrite), use `dsimp only [bind, Option.bind]` not `simp only`.

## `dsimp` not `simp only` after `unfold` on recursive functions
`simp only [F, bind, Except.bind] at h` may re-unfold recursive `F` and loop. Use:
```lean
unfold F at h
dsimp only [Bind.bind, Except.bind] at h
```
`dsimp` reduces bind without unfolding named defs. Essential for fuel-based recursion.
(For WF-recursive `F`, use `rw [f.eq_1]`, never `simp only [f]` — see `lean-wf-recursion`.)

## `pure PUnit.unit` artifacts from destructuring bind
`let (a, b) ← expr` in Except desugars to TWO nested matches: the bind, then a no-op
`match pure PUnit.unit with ...`. `dsimp only []` can't reduce the second (`pure` not
unfolded). After the first match, use `simp only [pure, Pure.pure, Except.pure] at h`.
Without it, the next `split at h` targets the wrong match.

## Single-pass simp for non-recursive multi-guard functions
For non-recursive `do` functions with many `if ... then throw` guards
(e.g. `parseSequencesHeader`), reduce all monadic constructs at once then `split`:
```lean
simp only [parseSequencesHeader, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
split at h
· exact nomatch h
· split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, -, rfl⟩ := h; omega
  ...
```
Safe only because `F` is non-recursive (simp won't loop). For forward (goal) proofs,
add condition resolution: `simp only [show ¬(data.size < pos + 1) from by omega,
↓reduceIte, hbyte, beq_self_eq_true]`. `beq_self_eq_true` is needed when substitution
yields `(0 == 0) = true` as an if-condition — `↓reduceIte` alone won't reduce it.

## `unless` desugaring
`unless cond do throw err` becomes `if ¬cond then .error err else pure ()`. After
`simp only [bind, Except.bind]`, gives a stuck match on the guard. Per guard:
```lean
by_cases hcond : cond
· simp [hcond] at h    -- passes → continue
· simp [hcond] at h    -- fails → .error = .ok contradiction
```

# Closing error/ok contradictions

## `exact nomatch h` for `Except.error = Except.ok`
`simp only` lacks the discriminator simproc. Replace `simp at h` with `exact nomatch h`
(`Eq` has one ctor; different ctors can't match → `False`). If a hypothesis must be
rewritten first: `simp only [hrb] at h; exact nomatch h`.
- NOT `contradiction` standalone: at 6+ bind levels it hits max recursion depth.
- NOT `exact absurd h (by simp)`: roundabout.

## `nomatch` fails inside `try` and `<;>`
`nomatch` produces an elaboration-level "Missing cases" error, NOT a tactic failure,
so `try`/`<;>` can't catch it. `split at h <;> try exact nomatch h` does NOT work.
- Standalone or after `next =>`: use `exact nomatch h`.
- Inside `first`/`try`/`<;>`: use `contradiction` (fails gracefully).
```lean
split at h
next => exact nomatch h      -- focus the error branch
split at h <;> first | contradiction | skip
```

## Batching error elimination across many branches
```lean
iterate 5 (all_goals (try (first | contradiction | (split at h))))
all_goals first
  | contradiction
  | (simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; omega)
```

# Extracting results

## `Except.ok.injEq` + `Prod.mk.injEq` extraction
For `Except ε (α × β)` results (`readBit`, `readBits`, `inflateBlock`). Always
`simp only`, never bare simp (bare may rewrite terms like `br.data.size` you want kept):
```lean
split at h
· exact nomatch h                                    -- error branch
· simp only [Except.ok.injEq, Prod.mk.injEq] at h    -- ok branch
  obtain ⟨hval, hrest⟩ := h
```
Extensions: `obtain ⟨rfl, rfl⟩ := h` to substitute; chain `<;> obtain ⟨_, rfl⟩ := h
<;> simp_all` for one-liners.

## Constructor inequality after struct substitution
`decide` fails with free vars (e.g. `data[pos]!` in fields); `intro h; exact nomatch h`
fails on the struct form. Substitute the struct first, then discriminate:
```lean
obtain ⟨rfl, rfl⟩ := h        -- substitutes hdr := {field2 := .raw, ...}
exact fun h => nomatch h      -- now .raw = .reserved has no free vars
```

## `subst` leaves struct projections unreduced
After `subst h` with `h : { field := e, ... } = result`, `result.field` stays as
`{...}.field`, breaking `exact hwm`. Use `rw [← h]` instead of `subst h`:
```lean
simp only [Except.ok.injEq] at h
constructor
· rw [← h]            -- rewrites result.maxBits to m directly
· subst h; ...        -- subst fine when projections aren't in the goal
```

## `eq_of_beq` for BEq→Eq from `bne`/`==` guards
Negative branch of `by_cases hmagic : (magic != expected) = true` gives
`¬(magic != expected) = true`. To extract `magic = expected`:
```lean
have heq : (magic == expected) = true := by cases h : (magic == expected) <;> simp_all
exact eq_of_beq heq
```
Works for any `LawfulBEq` type. Don't `simp [bne, BEq.beq]` — large intermediate terms.

## Destructured tuple arguments avoid projection issues
For tuple-returning functions, destructure in helper lemma signatures so `omega`/`subst`
see plain Nats instead of `v.2.2.fst` projections (which don't reduce):
```lean
-- WRONG: omega can't see through v.1
theorem myLemma (v : Nat × Nat × Nat × Bool) (h : ...) : v.1 ≤ 1000 := by omega
-- RIGHT
theorem myLemma (regen comp hdr : Nat) (fs : Bool) (h : ...) : regen ≤ 1000 := by omega
```
Essential in `parseLiteralsSection` (4-tuple header).

# Option monad

## `pure` vs `some`
`Option.pure` doesn't exist as a constant. To unfold monadic `return`/`pure` in Option
specs, add `pure, Pure.pure` to simp args (goals may show `pure (...) = some (...)`).

## After `cases h : f x with | some p`: reduce the bind, not `h`
`cases` already substituted the ctor in the goal; `h` is unnecessary. The wrapper
`Option.bind (some p) f` still needs `simp only [bind, Option.bind]` (NOT `simp only [h]`).

## Full `simp` (not `simp only`) for Option match chains
When `unfold` expands an Option do-block into
`match opt?, fun val => ... with | none, _ => none | some a, f => f a`, `simp only`
cannot enter these matches. Use full `simp` with the hypotheses. (Differs from Except,
where `simp only [bind, Except.bind]` suffices.)

## `readBitsLSB` Option lemma kit
```lean
simp only [Spec.readBitsLSB, Option.pure_def, Option.bind_eq_bind, Option.bind_some]
```
Handles `pure x → some x` and `Option.bind (some x) f → f x`. For deeply nested calls
(5+ bits), also need `List.cons.injEq`, `reduceCtorEq`; at that point bare
`simp [Spec.readBitsLSB]` is acceptable (see `lean-simp-tactics`).

## Option case-split with `nomatch` (`hgo` tracks the result)
```lean
| none => simp only [hX] at hgo; exact nomatch hgo
| some p => obtain ⟨val, rest⟩ := p; simp only [hX] at hgo   -- continue, don't inject
· simp only [hf] at hgo; obtain rfl := Option.some.inj hgo    -- by_cases true: inject
· simp only [hf] at hgo                                       -- false: continue/nomatch
```
Pitfalls (each cost a build cycle):
- `↓reduceIte` is unnecessary with `simp only [hf]` (iota handles it); linter flags it.
- `hgo ▸ X` fails after `simp only` (hgo is `some X = some result`). Use
  `obtain rfl := Option.some.inj hgo`.
- `Option.some.injEq` as a simp arg is flagged unused; use `Option.some.inj` explicitly.

## Option.bind chains by depth
- ≤3 levels: sequential `cases hf : f a with | none => rw [hf] at h;
  dsimp only [bind, Option.bind] at h; exact nomatch h | some x => rw [hf] ...; dsimp ...`
- >3 levels: bare `simp` with a comment, e.g.
  `simp [hcl, hlit, hdist, hacc, hfinal, hresult] at hgo  -- 6-level Option.bind chain`
- Guard+bind: after `split at h` on an inner `if`, interleave
  `dsimp only [bind, Option.bind] at h` to reduce the surrounding bind before continuing.

# Guards and conditionals

## Guard contradiction in `by_cases` negative branch
`by_cases` on `(x == y) = true` gives `¬(x == y) = true`, NOT `(x == y) = false`. To
reduce a stuck `guard`/`if ... then pure () else failure`:
```lean
have hfalse : (x == y) = false := by cases h : (x == y) <;> simp_all
rw [hfalse] at hspec
simp [guard, Bool.false_eq_true] at hspec   -- none = some contradiction
```
`simp [hguard]` alone leaves `guard False` unreduced.

## do-notation guards (`if ... then throw`)
Expand to `match (if cond then .error err else pure PUnit.unit) with ...`. After
`split at h` on the outer condition, the pure branch leaves a stuck match — reduce with
`simp only [pure, Except.pure] at h`.

## `letFun` linter false positive
`unfold f at h` may leave `have x := e; body` (`letFun`) blocking `split at h` from
seeing inner `if`s. The linter flags `simp only [letFun] at h` as unused (simp reduces
it via built-in, not the lemma). Use `dsimp only at h` — same reduction, no warning.

## `split at h` chains with interleaved `letFun`
Successive `split at h` may stall on `letFun` wrappers between branches (e.g.
`executeSequences.loop`). Interleave `dsimp only [letFun] at h` between splits.

## Inline `show` proofs for condition resolution
Provide if-condition proofs inline rather than via separate `have`:
```lean
simp only [resolveOffset, show ¬(2 > 3) from by omega, show litLen > 0 from hlit, ↓reduceIte]
```

# `split at h` vs `by_cases`

| Function size | Use | Why |
|---|---|---|
| < 15 branches | `split at h` | fast, handles `if`/`match` uniformly |
| 15-25 | try `split`, fall back to `by_cases` | may hit step limit |
| > 25 or `let mut` | `by_cases` + `rw [if_pos/if_neg]` | `split` will hit step limit |

Favor `by_cases` when: `let mut` (large nested match); `BEq` guards (`split` creates
stuck `Decidable.rec` / inaccessible hypotheses — use `by_cases` + `beq_iff_eq`); guard
wraps `Except.bind` around a conditional (`split` splits at the wrong level).

Examples: `decodeFseDistribution_accuracyLog_ge` (Fse.lean, `split`);
`parseFrameHeader_magic`, `parseSequencesHeader_numSeq_small`,
`parseHuffmanTreeDescriptor_pos_gt` (Zstd.lean, `by_cases`).

## `split at h` step limit on large functions
`split` uses simp internally and can hit ``maximum number of steps exceeded`` on large
unfolded functions (`parseFrameHeader` with `let mut`). Use targeted rewrites:
```lean
by_cases hcond : condition
· rw [if_pos hcond] at h; exact nomatch h
· rw [if_neg hcond] at h
  simp only [pure, Pure.pure] at h          -- reduce match on pure PUnit.unit
```
Also avoid `simp [bne, hb]` on large hypotheses; use targeted `show` + `rw` for Bool
goals like `(!false) = true`:
```lean
exfalso; apply hmagic; show (!(a == b)) = true; rw [hb]   -- then rfl
```

## `repeat split at h` is depth-first — use `iterate` for breadth
`repeat split at h` follows ONE branch to completion, leaving other goals partially
split. Use breadth-first instead:
```lean
iterate 5 (all_goals (try (first | contradiction | (split at h))))
all_goals first
  | contradiction
  | (simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; omega)
```
Use `contradiction` (not `nomatch`) inside `first`. Example: `parseFrameHeader_pos_gt`.

# Nested matches and case-split parsing

## Nested `cases` misparses — use `match` for the inner split
Nested `cases ... with` makes Lean attach the inner `| some =>` to the outer `cases`:
```lean
cases hdb : f x with
| none =>
  match hdec : g y with    -- NOT `cases hdec : g y with`
  | none => ...
  | some p => ...
| some p => ...
```

## Match within `do` blocks: `cases` discriminant + `simp only`, NOT `split`
Pattern 1 (match on a pure value mid-chain): `cases hbt : hdr.blockType with | raw =>
simp only [hbt] at h; ... | reserved => simp only [hbt] at h; exact nomatch h`.
`simp only [hbt]` reduces the match to the selected branch. `split at h` generates too
many subgoals when subsequent binds are present.

Pattern 2 (match on a monadic result feeding later binds): unfold the match, THEN the
bind: `cases hmode : result with | modeA => simp only [hmode] at h;
dsimp only [bind, Except.bind] at h`.

Anti-pattern: `split at h` on a match wrapped in `Except.bind` keeps the outer wrapper
around a partially-reduced match.

# Long state-threading chains (decompressFrame pattern)

For 5-10 monadic ops each returning `(result, state)`:
1. Unfold + reduce first bind: `simp only [F, bind, Except.bind] at h;
   cases hread : readU32 br with | error e => simp only [hread] at h; exact nomatch h
   | ok val => obtain ⟨magic, br₁⟩ := val; simp only [hread] at h;
   dsimp only [bind, Except.bind] at h`.
2. Each guard between ops: `by_cases hmagic : magic == expected`, simp in both branches.
3. Repeat. After each op, use `rw [h_result] at h; simp only [] at h` (NOT
   `simp [h_result] at h`) to avoid over-simplifying / looping on recursive functions.
4. Final `pure`/`return`: `simp only [pure, Except.pure, Except.ok.injEq,
   Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h`.

For chains >6 ops, prove per-operation lemmas (e.g. `parseFrameHeader_data` showing
`br'.data = br.data`) and compose — scales better, produces reusable lemmas.

Extract a witness through guards:
```lean
have h_result : ∃ bytes, operation = .ok (bytes, finalState) := by
  revert h; intro h; simp only [pure, Except.pure] at h
  by_cases hg1 : guard₁ <;> [simp [hg1] at h; simp only [hg1] at h]
  match h3 : operation with
  | .error e => simp [h3] at h
  | .ok (val, st) => exact ⟨val, by simp [h3] at h; rw [h.2]⟩
obtain ⟨bytes, h_result⟩ := h_result
```

# `grind` for struct/match finishing

## Struct field extraction from bind chains
When a function always returns `.ok { field := input, ... }`:
```lean
simp only [buildFseTable, bind, Except.bind, pure, Except.pure] at h
grind
```
`simp only` reduces wrappers to a nested match ending in `.ok { field := al, ... }`;
`grind` extracts the field equality. Fails when the field depends on loop iterations.

## `grind` as monadic case-split finisher
Use over `split`/`simp` for: nested `match` on struct fields (`hdr.isLastBlock`,
`desc.checksum`) where the scrutinee is a field accessor `split` can't target;
multi-branch functions where all branches reach the same conclusion. NOT for: needing
specific case hypotheses (use `split at h`); loop invariants; when `omega` alone suffices.

# `forIn` loops

## `Id` monad `forIn` invariants — metavariable trap
`Id.run do` with `for` loops desugars to `forIn (m := Id) [:n] init body`. With
`have := range_forIn_inv n _ _ P hinit hf`, the body `f` is a metavariable `?m` during
`hf` elaboration, so `split` fails (no `if`/`match` in `?m x b`). Fix: pass the `heq`
equation as an early argument so Lean resolves `f` first:
```lean
private theorem forIn_fst_size_of_heq {α β : Type} {n k : Nat}
    {init : MProd (Array α) β}
    {f : Nat → MProd (Array α) β → Id (ForInStep (MProd (Array α) β))}
    {result : Array α} {rest : β}
    (heq : forIn (m := Id) [:n] init f = ⟨result, rest⟩)
    (hinit : init.fst.size = k)
    (hf : ∀ a b, b.fst.size = k → ∃ b', f a b = ForInStep.yield b' ∧ b'.fst.size = k) :
    result.size = k := ...

have h₁ : cells₁.size = 1 <<< al :=
  forIn_fst_size_of_heq heq₁ (by simp) (fun _ b hb => by
    split                                            -- works: f is concrete
    · exact ⟨_, rfl, by simp [Array.size_setIfInBounds, hb]⟩
    · exact ⟨_, rfl, hb⟩)
```
Overall: `unfold f; simp only [Id.run, pure, Pure.pure, Bind.bind]`, then
`split; rename_i ... heq`, then `forIn_fst_size_of_heq heq ...`. For nested loops,
`split` inside the outer `hf` to reach the inner match.

## `MProd` vs `Prod` in desugared `do` state
Desugared `do` with `let mut` uses `MProd` (mutable pair), NOT `Prod`/`×`. Symptoms:
`split; rename_i ... heq` gives `heq : forIn ... = ⟨result, rest⟩` as `MProd`;
`obtain ⟨a, b⟩ := val` fails with Prod/MProd mismatch; hypotheses show `MProd.fst/.snd`.
Fix: use `MProd` in invariant types and helper lemmas (`init : MProd (Array α) β`, not
`Array α × β`); access via `.fst`/`.snd`. Pattern-match with `⟨fst, snd⟩` or `MProd.mk`.

## `forIn` with yield-only body → `Array.foldl`
When a `for w in arr do` in Except always yields (no break/return):
1. `simp only [pure, Pure.pure, Except.pure] at heq_forIn` (mutable-assign artifacts).
2. Factor `ok (yield ...)` out of `if` branches:
```lean
simp only [show ∀ (w : UInt8) (r : Nat),
    (if w.toNat > 0 then Except.ok (ForInStep.yield (r + f w))
     else (Except.ok (ForInStep.yield r) : Except ε (ForInStep Nat))) =
    Except.ok (ForInStep.yield (if w.toNat > 0 then r + f w else r))
  from fun w r => by split <;> rfl] at heq_forIn
```
3. `rw [forIn_pure_yield_eq_foldl] at heq_forIn; exact (Except.ok.inj heq_forIn).symm`.

Critical: `simp`/`rw` CANNOT match syntactically identical `match` expressions from
different elaboration contexts (different internal `casesOn`). A separately proved
`List.foldlM`+match lemma can't be `rw`'d into a `foldlM` whose match came from
`Array.forIn_eq_foldlM`. Workaround — prove by `generalize` + induction on the goal:
```lean
rw [Array.forIn_eq_foldlM, ← Array.foldlM_toList, ← Array.foldl_toList]
generalize as.toList = l
revert init
induction l with
| nil => intro init; rfl
| cons x l ih => intro init
                 simp only [List.foldlM, bind, Except.bind, List.foldl_cons]
                 exact ih (f x init)
```

## `forIn` invariants in Except are not automatable
No standard-library theorem proves properties preserved through `forIn` in Except;
`grind`/`simp`/`omega` can't see through it (e.g. `cells.size = tableSize` after a
`Array.set!` loop needs an invariant theorem that doesn't exist for
`Std.Legacy.Range.forIn'` in Except). Leave a documented `sorry` — a known stdlib gap.

## Counter vs element in `forIn_range_preserves_indexed`
Callback gets a counter `k : Nat` and an element `a : Nat`. For `[:n]` they're equal
numerically but distinct free vars. Using `k` where the goal uses the element makes
`omega` fail (goal mentions `a✝¹`). Always NAME the element and use it in `have`s:
```lean
intro k kv b b' hk hinv heq
have hcount : v[kv]! ≤ bound := ...    -- kv (element), not k
```

# `BackwardBitReader` (Zip/Native/Fse.lean)

Reads MSB-first; `readBits` uses inner `readBits.go br k acc` recursing on `Nat` count `k`.

## Induction on the count parameter (`generalizing br acc` essential)
```lean
induction k generalizing br acc with
| zero =>
  simp only [BackwardBitReader.readBits.go] at h
  obtain ⟨rfl, _⟩ := Prod.mk.inj (Except.ok.inj h)
| succ k ih =>
  simp only [BackwardBitReader.readBits.go, bind, Except.bind] at h
  split at h
  · exact nomatch h
  · simp only [pure, Except.pure] at h; refine ih _ _ ... h
```

## Accumulator bound invariant (inner loop → wrapper)
To prove `readBits n` gives `val.toNat < 2^n`, track `acc.toNat < 2^(n-k)`; the step
shows `(acc <<< 1) ||| bit` preserves it. Helper takes `(hkn : k ≤ n)
(hacc : acc.toNat < 2 ^ (n - k))`; wrapper instantiates `k = n`, `acc = 0`:
`readBits_go_value_bound br n 0 val br' (Nat.le_refl n) (by simp) h`.

## `totalBitsRemaining` as decreasing measure
`totalBitsRemaining br = bitsRemaining + 8 * (bytePos - startPos)`. Prove `readBits`
strictly decreases it on success (`readBits_go_totalBitsRemaining_decreasing`), then use
it as the termination measure for outer loops over `readBits`.

# `omega` limitations

## `Except.ok.injEq` conjunctions
After `simp only [Except.ok.injEq, Prod.mk.injEq] at h`, `h` is `A ∧ B ∧ C ∧ D`. `omega`
cannot decompose it if any conjunct has nonlinear terms (`&&&`, `>>>`, `|||`). Extract
first: `obtain ⟨-, -, hhdr, -⟩ := h` then `omega`.

## Bool conditions from `split`
`split at h` on `if (x == y) then ...` gives `(x == y) = true` / `¬(x == y) = true`,
which `omega` can't use. Convert: `simp only [beq_iff_eq] at *` then `omega`.
(Prop conditions like `if x ≤ y` give `x ≤ y` directly — no conversion needed.)

# Cross-module visibility

## Private functions are opaque cross-module
A `private def` in module A can't be unfolded by `simp only` in module B; it appears as
`Module.privateFunc✝` (hygiene suffix) — unreferenceable. Symptoms: `simp only
[privateFunc]` → "Unknown identifier"; `split at h` on the call gives only error/ok.
Fix: remove `private`, OR add a public lemma in the SAME file (non-private theorems can
reference private defs in their own module). Check visibility BEFORE writing a proof that
needs the function's internals. (Tuple projection gotcha: after `subst h`, `v.2.2.fst`
stays unreduced — destructure in the helper signature: `(h : f x = .ok (a, b, hdr, fs))`.)

# `Except.mapError` and `List.replicate`

## `Except.mapError.eq_2` not bare `Except.mapError`
To simplify `(.ok v).mapError f = .ok v`, use `Except.mapError.eq_2` in simp sets; the
bare `Except.mapError` unfolds to a match simp may not fully reduce. Add
`beq_self_eq_true` when the proof needs `(0 : Nat) == 0 = true`.

## `List.replicate` expansion after `unfold`
`unfold f at h` can expand `List.replicate 19 0` to a 19-element literal, making `rw`
slow. Alias the literal and `show`/`change` between forms:
```lean
private def defaultCodeLengths : List UInt8 := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem replicate_eq : List.replicate 19 (0 : UInt8) = defaultCodeLengths := rfl
```

# Cross-references
- Parsing completeness (function succeeds on well-formed input): `lean-parsing-completeness`.
- Dependent `if` through `do` blocks for termination: `lean-wf-recursion`,
  "Dependent `if` Hypotheses and `do` Early-Throw". Use `if hoff : cond then .error ...
  else do ...` not `do; if cond then throw ...`.
- `simp only` vs bare `simp`: `lean-simp-tactics`, "Bare `simp` Resistant Patterns".
- WF unfolding (`rw [f.eq_1]`, never `simp only [f]` on recursive defs): `lean-wf-recursion`.
- Zstd loop invariants via equation-lemma matching: `lean-zstd-spec-pattern`.
