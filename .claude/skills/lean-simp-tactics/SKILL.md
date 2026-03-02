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

---

# Bare `simp` Resistant Patterns

Some proof patterns genuinely resist `simp only` conversion. This section
documents the 5 categories discovered across 10+ review sessions, explains
why each resists conversion, and provides workaround strategies.

## Category 1: Nested `Option.bind` / `Except.bind` Chains

**Why it resists**: `do`-notation in `Option`/`Except` desugars to nested
`bind` calls. After `unfold` or `cases` on one monadic operation, the
remaining goal has `Option.bind (Option.bind (Option.bind ... f) g) h`.
`simp only [bind, Option.bind]` reduces one layer, but deeply nested
chains (6+ levels, common in `decodeDynamicTables` and similar functions)
require the full `@[simp]` database to traverse all layers at once.

**Example** (DeflateSuffix.lean, `decodeDynamicTables_append`):
```lean
-- 21 instances where bare simp is needed:
simp [hcl, hlit, hdist] at hgo
-- simp only [hcl, hlit, hdist, bind, Option.bind] at hgo
-- ↑ Fails: only reduces outermost bind, inner ones stay stuck
```

**Workaround strategies**:
1. **Sequential `rw` + `dsimp`**: Break the chain into individual steps.
   After each `cases hx : operation`, use `rw [hx]; dsimp only [bind, Option.bind]`
   to reduce one layer at a time. This works but produces verbose proofs.
2. **Helper lemma**: Extract the nested bind chain into a named lemma that
   states the overall result, then apply it in one step.
3. **Accept bare simp with comment**: For chains deeper than 4 levels,
   bare `simp [h₁, h₂, ...]` is acceptable — add a comment:
   `-- bare simp: 6-level Option.bind chain`

**Decision**: If the chain is ≤3 levels deep, use sequential `rw + dsimp`.
If >3 levels, accept bare simp with a justifying comment.

## Category 2: `dite`/`if` Reduction with Mismatched Conditions

**Why it resists**: After `split at h` on an `if`/`dite` inside a monadic
chain, the remaining goal may have a *different* `if` whose condition uses
`(bits ++ suffix).length` while the available hypothesis proves about
`bits.length`. `rw [if_pos hf]` requires exact syntactic match and fails.
`simp [hf]` succeeds because it implicitly applies `List.length_append`
and arithmetic to bridge the gap.

**Example** (DeflateSuffix.lean, `decode_go_suffix`):
```lean
-- Goal condition: (bits ++ suffix).length < maxPos
-- Hypothesis: hblen : bits.length < maxPos - suffix.length
-- rw [if_pos ...] fails — syntactic mismatch
-- simp [hblen] works — applies List.length_append + omega internally
simp [hblen] at hgo ⊢
```

**Workaround strategies**:
1. **Bridge lemma**: Prove an intermediate `have` that matches the goal's
   condition exactly:
   ```lean
   have hcond : (bits ++ suffix).length < maxPos := by
     simp [List.length_append]; omega
   rw [if_pos hcond] at hgo ⊢
   ```
2. **`conv` targeting**: Use `conv` to rewrite just the condition:
   ```lean
   conv at hgo => rw [show (bits ++ suffix).length = bits.length + suffix.length
     from List.length_append ..]
   ```
3. **Accept bare simp with comment**: When the bridge lemma is trivial but
   the proof is in a hot path, bare `simp [hf]` is acceptable.

**Decision**: Use a bridge lemma when the condition appears in multiple
branches (extract it once, use everywhere). Accept bare simp when it's a
one-off in a single branch.

## Category 3: `Prod.mk.injEq` Extraction in goR Patterns

**Why it resists**: Many functions return `(result, remaining)` pairs.
After proving `f x = Except.ok (result, bits')`, extracting the two
components requires `Except.ok.injEq` + `Prod.mk.injEq`, then
`obtain ⟨hval, hrest⟩`. This pattern uses `simp only` successfully —
it is NOT bare-simp-resistant.

**The actual pattern** (BitReaderInvariant.lean, InflateRawSuffix.lean):
```lean
split at h
· -- error branch
  exact nomatch h
· -- ok branch
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨hval, hrest⟩ := h
```

This is the canonical `simp only` pattern for pair extraction and does
NOT need bare simp. It appears 35+ times across the codebase. The key
insight is that `Except.ok.injEq` and `Prod.mk.injEq` are specific
enough for `simp only` — they don't pull in the full database.

**Anti-pattern**: Don't use `simp at h` for pair extraction — it
over-simplifies and may rewrite terms you want to keep.

## Category 4: `readBitsLSB` as Computation Engine

**Why it resists**: `readBitsLSB n bits` for concrete `n` (typically
1, 2, 3, or 5) unfolds into nested `match` on the list, producing
concrete boolean values. `simp [readBitsLSB]` evaluates the entire
chain including boolean arithmetic (`Nat.bit`, list cons/nil matching).
Converting to `simp only` would require listing 20+ lemmas including
`reduceCtorEq` for boolean equality, `List.cons.injEq`, etc.

**Example** (Deflate.lean, header bit parsing):
```lean
-- Evaluating BFINAL/BTYPE from a concrete 3-bit header:
simp [readBitsLSB]
-- Reduces: readBitsLSB 3 [true, false, true, ...rest]
--       → some (5, rest)  (after evaluating all bit arithmetic)
```

**Example** (BitstreamCorrect.lean, readBits base case):
```lean
exact ⟨0, br'.toBits, by simp [Deflate.Spec.readBitsLSB], rfl, by simp, hwf⟩
```

**Workaround strategies**:
1. **`decide`/`decide_cbv`**: If the statement is decidable (concrete
   inputs), these may work but require high `maxRecDepth`.
2. **`native_decide`**: Forbidden in this codebase.
3. **Accept bare simp**: For concrete bit-level computation, bare
   `simp [readBitsLSB]` is the right tool. Add comment:
   `-- bare simp: concrete bit computation`

**Decision**: Always accept bare `simp [readBitsLSB]` for concrete
header evaluation. It IS the computation engine — that's its job.

## Category 5: BitVec / UInt16 Normalization Pipelines

**Why it resists**: Converting between `Nat`, `UInt16`, `UInt8`, and
`BitVec` requires multi-step normalization: unfold `Nat.toUInt16`, then
`simp` to reduce `BitVec.toNat (BitVec.ofNat ...)`, then `rw` with
domain-specific lemmas like `and_255_eq_mod_256`, then `omega` for
arithmetic. The `simp` step in the middle needs the full `@[simp]`
database for `BitVec` normalization.

**Example** (Deflate.lean, byte extraction):
```lean
have hlo : (n.toUInt16 &&& 255).toUInt8.toNat = n % 256 := by
  unfold Nat.toUInt16; simp; rw [and_255_eq_mod_256]; omega
```

**Partial `simp only` replacement** (DecodeComplete.lean):
```lean
simp only [Nat.toUInt16, UInt16.toNat, UInt16.ofNat,
  BitVec.toNat_ofNat]; omega
```

**Decision**: When the full `simp only` lemma set is known (as in the
DecodeComplete example), use it. When the BitVec normalization is
complex (involving `&&&`, shifts, or casts through multiple types),
bare `simp` in the pipeline is acceptable with comment:
`-- bare simp: BitVec normalization`

## When Bare `simp` Is Acceptable

Not every bare `simp` needs conversion. The following categories should
be left with a justifying comment rather than forced into `simp only`:

| Category | Comment Template | Rationale |
|----------|-----------------|-----------|
| Deep Option.bind chains (>3 levels) | `-- bare simp: N-level Option.bind chain` | `simp only` needs full bind database |
| Concrete bit computation | `-- bare simp: concrete bit computation` | `readBitsLSB` evaluation engine |
| BitVec normalization pipeline | `-- bare simp: BitVec normalization` | Multi-type cast chain |
| `if` with mismatched length forms | `-- bare simp: bridges List.length_append` | Condition uses `(a ++ b).length` vs `a.length` |

**Categories that should always be converted:**
- Constructor discrimination (`simp at h` on `error = ok`): use `exact nomatch h`
- Pair extraction: use `simp only [Except.ok.injEq, Prod.mk.injEq]`
- Single bind reduction: use `dsimp only [bind, Option.bind]`
- `letFun` reduction: use `dsimp only`
- Match iota reduction: use `simp only []`

**Review workflow**: When reviewing bare `simp`:
1. Try `simp only` with `simp?` output
2. If that fails, try `dsimp only`
3. If that fails, try a helper lemma or bridge `have`
4. If all three fail, accept bare simp with a category comment

## Struct Field Access Not Reduced by `omega` or `decide`

When proving `{ data := d, pos := p, bitOff := 0 }.bitOff < 8`, neither `omega` nor
`decide` works: `omega` doesn't reduce struct field access, and `decide` fails because
the struct contains free variables.

**Fix**: Use `show` to manually reduce the struct projection:
```lean
by show 0 < 8; omega
```

Similarly for `Or.inl rfl` when proving `{ ... bitOff := 0 }.bitOff = 0 ∨ ...` — the
struct projection reduces definitionally, so `Or.inl rfl` works directly.

## `BEq.beq` vs `Nat.beq` — Use `beq_iff_eq`

When a hypothesis `h : (x == 0) = true` comes from a `split` on an `if x == 0` condition,
the `==` creates `BEq.beq`, NOT `Nat.beq`. So `Nat.eq_of_beq_eq_true h` fails with a
type mismatch.

**Fix**: Use `simp only [beq_iff_eq] at h` to convert `(x == 0) = true` into `x = 0`.
Or use `exact absurd (by rw [h]; decide) hne` for contradiction branches.

## `⟨⟨result.data.toList⟩⟩ = result` for ByteArray

`ByteArray.mk (Array.mk result.data.toList) = result` is true by **eta reduction** in
Lean 4 (structures have eta). Just use `rfl` — no `simp`, `ext`, or library lemmas needed.
