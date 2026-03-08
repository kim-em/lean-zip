---
name: proof-review-checklist
description: Use when reviewing Lean proof quality, cleaning up proofs after getting them to work, or performing a review session on a proof file. Also use when the review command targets a Lean file.
allowed-tools: Read, Bash, Grep, Glob
---

# Proof Review Checklist

Mechanical cleanup steps for Lean proof quality reviews. Follow this
checklist in order for each file.

## Phase 0: Verify Issue Accuracy

**Before starting work**, verify the issue's bare simp counts against
the actual master state. Issue descriptions go stale when other PRs
clean the same or overlapping files.

```bash
# Accurate bare simp grep (excludes simp only, simp_all, simp?, simp_wf, etc.)
grep -n 'simp\b' File.lean | grep -v 'simp only\|simp_all\|simp?\|simp_wf\|dsimp\|simp_rfl\|simp (config'
```

If the actual count differs significantly from the issue (e.g., issue
says 61 but master has 0), the file was already cleaned by another PR.
Use `coordination skip` and move on — don't waste time investigating.

## Phase 1: Metrics (Before)

Record starting metrics before making any changes:

```bash
# Bare simp count (the primary quality metric — use the accurate grep from Phase 0)
grep -n 'simp\b' File.lean | grep -v 'simp only\|simp_all\|simp?\|simp_wf\|dsimp\|simp_rfl\|simp (config'
```

Expected reduction targets by file size:
- Small files (<200 lines): 80-95% bare simp elimination
- Medium files (200-500 lines): 70-90% bare simp elimination
- Large files (500+ lines): 60-80% bare simp elimination
- Files heavy in monadic chains: 50-70% (many are legitimately resistant)

## Phase 2: Mechanical Cleanup

These steps are safe and should always be applied:

### 2a. Merge consecutive `rw` calls

```lean
-- Before
rw [ha] at h
rw [hb] at h

-- After
rw [ha, hb] at h
```

### 2b. Merge consecutive `simp only` calls

```lean
-- Before
simp only [ha] at h
simp only [hb] at h

-- After
simp only [ha, hb] at h
```

**Caveats**:
- Only merge when both target the same location (`at h` or `at ⊢`).
  Don't merge `simp only [ha] at h` with `simp only [hb]` (different targets).
- Don't merge when the first call unfolds definitions that create new
  redexes for the second call's lemmas. `simp only` applies all lemmas
  simultaneously, not sequentially — so merging two calls that depend on
  ordering (e.g. first unfolds `UInt32` terms, second normalizes
  `List.append_assoc`) will change the simplification result and break
  downstream proofs. Always build after attempting a merge.

### 2c. Remove dead `have` bindings

Search for `have` bindings whose names never appear later in the proof.

**WARNING**: `omega` and `simp` use the entire local context implicitly.
A `have` that appears unused may be feeding `omega`. Always build after
each removal to verify. See the `lean-simp-tactics` skill section on
"`have` Bindings That Look Unused but Feed `omega`/`simp`".

### 2d. Check for extractable lemmas

If the same proof pattern (3+ lines) appears twice or more in the file,
extract it into a `private theorem` or `private lemma`.

### 2e. Simplify `obtain` patterns

```lean
-- Before
obtain ⟨a, b⟩ := h
rw [a]; rw [b]

-- After
obtain ⟨rfl, rfl⟩ := h
```

## Phase 3: Bare `simp` Decision Tree

For each bare `simp` (without `only`), follow this decision tree.

**Batch discovery, sequential application.** For files with many bare
simps (10+), the most efficient workflow is:

1. **Batch discovery**: Convert ALL bare `simp` calls to `simp?`
   simultaneously, then build ONCE. This produces all `Try this:`
   suggestions in a single build pass — vastly more efficient than
   converting one at a time.
2. **Collect suggestions**: Read all info messages and note the
   suggested `simp only [...]` replacements.
3. **Apply in small batches**: Replace 3-5 at a time, building after
   each batch to verify. Some suggestions may not work in combination
   (simp? suggestions are computed independently).

This batch-then-apply approach was discovered in the bare simp campaign
and typically reduces a 20-bare-simp file in 2-3 build cycles instead
of 20.

**Important**: `simp [X]` is NOT equivalent to `simp only [X]` — bare
`simp` uses the entire `@[simp]` lemma database plus `X`, while
`simp only [X]` uses ONLY `X`. Never do a mechanical search-and-replace.

### Step 1: Try `simp?`

Replace `simp` (or `simp [X]`) with `simp?` (or `simp? [X]`), build,
and read the `Try this:` info message to get the minimal lemma set.
If it produces a `simp only [...]` that works, use it.

### Step 2: Try `simp only []` or `dsimp only`

If `simp?` fails or produces an unwieldy list:

**`simp only []`** (empty argument list) handles:
- Match/iota reduction when scrutinee is a constructor
- After `split`/`match` chains where the goal has unreduced matches
- Replaces `simp only [htok]` when linter flags the argument as unused

**`dsimp only`** handles:
- `letFun` reduction
- Beta reduction
- `bind`/`Option.bind` reduction (when scrutinee is known)

Try `simp only []` first for match reduction; use `dsimp only` for
definitional reductions like `letFun` and monadic bind.

### Step 3: Try a targeted replacement

Based on what the `simp` is doing:

| Pattern | Replacement |
|---------|-------------|
| `simp at h` closing `error = ok` | `exact nomatch h` |
| `simp at h` closing `none = some` | `exact nomatch h` |
| `simp [hx]` then contradiction | `exact nomatch (hx ▸ h)` (one step) or `simp only [hx] at h; exact nomatch h` (two steps) |
| `\| none => simp [hvar] at hspec` (Option case) | `\| none => exact nomatch (hvar ▸ hspec)` |
| `\| error e => simp [hvar] at h` (Except case) | `\| error e => exact nomatch (hvar ▸ h)` |
| `simp at hmem` closing `x ∈ []` | `exact nomatch hmem` (NOT `absurd hmem (List.not_mem_nil _)` — `List.not_mem_nil` has type `False` not `¬(x ∈ [])`) |
| `simp at h` closing `[].length ≥ 2` | `simp only [List.length_nil] at h; omega` (`omega` alone can't reduce `[].length`; same for `[_].length`, use `List.length_cons`) |
| `simp [bind, Option.bind]` | `dsimp only [bind, Option.bind]` |
| `simp [hx, bind, Option.bind]` | `rw [hx]; dsimp only [bind, Option.bind]` |
| `simp only []` | Keep — match iota reduction |
| `simp [Prod.mk.injEq]` | `simp only [Except.ok.injEq, Prod.mk.injEq]` |
| `simp; omega` (array size preservation) | `rw [Array.size_set!]; omega` or `rw [Array.size_replicate]; omega` |
| `simp at h` (negated comparison) | `simp only [ge_iff_le, Nat.not_le] at h` or `simp only [gt_iff_lt, Nat.not_lt] at h` |
| `simp_all` (beq→eq + close) | `simp only [beq_iff_eq] at h; exact h` |
| `by simp` (struct field = literal) | `by show <literal_eq>; omega` or `Or.inl rfl` or `rfl` |
| `simp [Spec.readBitsLSB, ...]` (Option do-notation) | `simp only [Spec.readBitsLSB, ..., Option.pure_def, Option.bind_eq_bind, Option.bind_some]` |
| `simp [hpos0, hpos1]` (getElem!/getElem) | `simp only [getElem!_pos, hpos0, hpos1, ...]` |
| `simp` after `split` on Bool `if` | `split <;> rfl` |
| `simp [Nat.toUInt32]; omega` | `simp only [Nat.toUInt32, UInt32.toNat_ofNat', Nat.reducePow, Nat.reduceDvd, Nat.mod_mod_of_dvd, ...]; omega` |
| `simp (config := { decide := true }) only [...]` | Keep — needed for concrete evaluation + targeted lemma application (e.g. BFINAL flags) |
| `have : T.size = N := by decide` then `omega` | Keep — table size computation via kernel |
| `simp [Spec.readBitsLSB, ...]` (Option do-notation) | `simp only [Spec.readBitsLSB, ..., Option.pure_def, Option.bind_eq_bind, Option.bind_some]` |
| `simp [hpos]` with `getElem!` | `simp only [getElem!_pos, hpos, ...]` — bridges `data[i]!` to `data[i]` |
| `simp at h` (double negation) | `exact Decidable.of_not_not h` or `simp only [not_not] at h` |

### Step 4: Accept bare simp with comment

If steps 1-3 all fail, the `simp` falls into a resistant category.
Add a justifying comment from this table:

| Category | Comment |
|----------|---------|
| Deep Option.bind chain | `-- bare simp: N-level Option.bind chain` |
| Concrete bit computation | `-- bare simp: concrete bit computation` |
| BitVec normalization | `-- bare simp: BitVec normalization` |
| Length mismatch bridging | `-- bare simp: bridges List.length_append` |
| Complex `if`/`dite` with arithmetic | `-- bare simp: dite with arithmetic bridging` |

## Phase 3b: `simp_all` Conversion

`simp_all` is a separate concern from bare `simp`. It applies `simp` to
all hypotheses and the goal simultaneously, which is powerful but fragile
(sensitive to lemma database changes).

### `simp_all` → `simp_all only [...]`

Replace bare `simp_all` with targeted variants using `simp_all?`:

1. Replace `simp_all` with `simp_all?`, build, read the suggestion
2. Apply the suggested `simp_all only [...]`

### Common `simp_all` replacement patterns

| `simp_all` usage | Targeted replacement |
|------------------|---------------------|
| `simp_all` closing Option/Prod destructuring | `simp_all only [Option.some.injEq, Prod.mk.injEq]` |
| `simp_all` after `beq` hypothesis | `simp only [beq_iff_eq] at *; exact h` or `simp_all only [beq_iff_eq]` |
| `simp_all` in termination proof | `simp_all only [countRun_le_length]; omega` — make the specific lemma explicit |
| `simp_all` for Bool-to-Prop conversion | `simp_all only [beq_eq_false_iff_ne]` or use `beq_eq_false_iff_ne.mpr hx0` |

### Injection lemma kit for Option/Prod

When `simp_all` handles Option/Prod destructuring, the targeted replacements are:

- **`Option.some.injEq`**: reduces `Option.some a = Option.some b` to `a = b`
- **`Prod.mk.injEq`**: reduces `(a, b) = (c, d)` to `a = c ∧ b = d`
- **`Except.ok.injEq`**: reduces `Except.ok a = Except.ok b` to `a = b`

These three lemmas replace the majority of `simp_all` calls in monadic
proof contexts. Combined with `obtain ⟨rfl, rfl⟩ := h`, they eliminate
the need for `simp_all` in most injection scenarios.

### `beq_eq_false_iff_ne.mpr` for Bool-to-Prop

When `simp_all` is used to convert `(x == 0) = false` to `x ≠ 0`,
the targeted replacement is:

```lean
-- Before (bare simp_all):
simp_all [beq_iff_eq]

-- After (direct):
have hne := beq_eq_false_iff_ne.mpr hx0  -- hx0 : x ≠ 0
```

This is more explicit and doesn't depend on the simp lemma database.

### Campaign status

The bare `simp_all` campaign achieved zero bare `simp_all` across the
entire codebase as of PR #832. New code should maintain this invariant.

The bare `simp` campaign is nearly complete (only
`DeflateEncodeDynamicProps.lean` and `Huffman.lean` remain as of
2026-03-08). The batch-then-apply workflow from Phase 3 was the key
efficiency breakthrough, reducing per-file review time from ~20 build
cycles to 2-3.

## Phase 4: Linter Compliance

Check for linter warnings on the cleaned-up proofs:

### Unused simp arguments

The linter flags `bind`, `Option.bind`, `Except.bind`, `letFun` as
unused in `simp only` calls because they contribute only via dsimp.
Replace with the `rw + dsimp` pattern (see `lean-monad-proofs` skill).

### `↓reduceIte` flagged as unused

After `simp only [hf]`, iota reduction handles `if true/false`
automatically. Remove `↓reduceIte` if the linter flags it.

### `Option.some.injEq` flagged as unused

Replace `simp only [Option.some.injEq]` with explicit
`obtain rfl := Option.some.inj h`.

## Phase 5: Verification

After all changes:

1. Build the file: `lake build Module.Name`
2. Compare metrics:
   ```bash
   # Same grep commands as Phase 1
   ```
3. Verify no sorry introduced
4. Verify no `maxRecDepth` increased (indicates a regression)

## Phase 6: Commit

One commit per file reviewed. Use prefix `refactor:` with a summary:
```
refactor: replace bare simp with simp only in FileName.lean
```

Include metrics in the commit body:
```
Bare simp: 45 → 12 (73% reduction)
Remaining 12: 8 Option.bind chains, 2 readBitsLSB computations,
2 BitVec normalizations
```
