---
name: proof-review-checklist
description: Use when reviewing Lean proof quality, cleaning up proofs after getting them to work, or performing a review session on a proof file. Also use when the review command targets a Lean file.
allowed-tools: Read, Bash, Grep, Glob
---

# Proof Review Checklist

Mechanical cleanup steps for Lean proof quality reviews. Follow this
checklist in order for each file.

## Phase 1: Metrics (Before)

Record starting metrics before making any changes:

```bash
# Bare simp count (the primary quality metric)
grep -c 'simp\b' File.lean          # total simp occurrences
grep -c 'simp only' File.lean       # simp only occurrences
grep -c 'simp \[' File.lean         # simp [...] (bare with args)
grep -c 'simp at' File.lean         # simp at h (bare on hyps)
# Difference = bare simp count
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

**Caveat**: Only merge when both target the same location (`at h` or
`at ⊢`). Don't merge `simp only [ha] at h` with `simp only [hb]`
(different targets).

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

For each bare `simp` (without `only`), follow this decision tree:

### Step 1: Try `simp?`

Run `simp?` in place of `simp` to get the minimal lemma set. If it
produces a `simp only [...]` that works, use it.

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
| `simp [hx]` then contradiction | `simp only [hx] at h; exact nomatch h` |
| `simp [bind, Option.bind]` | `dsimp only [bind, Option.bind]` |
| `simp [hx, bind, Option.bind]` | `rw [hx]; dsimp only [bind, Option.bind]` |
| `simp only []` | Keep — match iota reduction |
| `simp [Prod.mk.injEq]` | `simp only [Except.ok.injEq, Prod.mk.injEq]` |
| `simp; omega` (array size preservation) | `rw [Array.size_set!]; omega` or `rw [Array.size_replicate]; omega` |
| `simp at h` (negated comparison) | `simp only [ge_iff_le, Nat.not_le] at h` or `simp only [gt_iff_lt, Nat.not_lt] at h` |
| `simp_all` (beq→eq + close) | `simp only [beq_iff_eq] at h; exact h` |
| `by simp` (struct field = literal) | `by show <literal_eq>; omega` or `Or.inl rfl` or `rfl` |

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
