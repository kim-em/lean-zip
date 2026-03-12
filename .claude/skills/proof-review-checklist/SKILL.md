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

# Also check for bare simpa (simpa without 'only' is just as fragile as bare simp)
grep -n 'simpa\b' File.lean | grep -v 'simpa only\|simpa?'
```

**Note**: bare `simpa` (without `only`) uses the full simp database,
just like bare `simp`. Issue descriptions often miss these because the
grep pattern `simp\b` doesn't match `simpa`. Always check both.

If the actual count differs significantly from the issue (e.g., issue
says 61 but master has 0), the file was already cleaned by another PR.
Use `coordination skip` and move on — don't waste time investigating.

## Phase 1: Metrics (Before)

Record starting metrics before making any changes:

```bash
# Bare simp count (the primary quality metric — use the accurate grep from Phase 0)
grep -n 'simp\b' File.lean | grep -v 'simp only\|simp_all\|simp?\|simp_wf\|dsimp\|simp_rfl\|simp (config'

# Bare simpa count
grep -n 'simpa\b' File.lean | grep -v 'simpa only\|simpa?'
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

**Extraction heuristic (≥3 rule):** Only extract a helper when:
- The pattern appears **3+ times** in the file, OR
- It appears **2 times** AND each instance is **6+ lines** (significant
  savings)

**Don't extract** when:
- Only 2 call sites with short patterns (<5 lines each)
- The pattern is parameterized differently at each site (different
  tables, different types) — extraction adds complexity without reuse
- The "pattern" is just a common tactic sequence that reads clearly
  inline (e.g., `rw [h]; omega`)

When extracting, use `private theorem` or `private lemma` to keep the
helper local to the file.

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
| (**caveat**: `nomatch (▸)` maxRecDepth) | After unfolding large definitions (e.g. `inflateRaw`), `▸` may hit `maxRecDepth`. Keep the two-step `simp only [h] at h; exact absurd h nofun` for those cases. |
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

## Phase 3a: Bare `simpa` Conversion

Bare `simpa` (without `only`) uses the full simp database, just like
bare `simp`. The `simpa` tactic is `simp` + `assumption`, so
`simpa using term` applies `simp` to both the goal and `term`, then
checks if they match.

**Conversion**: Replace `simpa` with `simpa?`, build, and use the
suggested `simpa only [...]`.

**Common patterns**:

| `simpa` usage | Targeted replacement |
|---------------|---------------------|
| `simpa using term` (Bool decide) | `simpa only [gt_iff_lt, decide_eq_true_eq, Nat.not_lt] using term` |
| `simpa using size_theorem` | `simpa only [Array.size_replicate] using size_theorem` |

**Note**: `simpa only []` (empty list) is valid and common — it does
structural reduction + `assumption`. Don't flag it as bare.

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
| `simp_all` reducing `if` in hypothesis | `rw [if_pos h]` / `rw [if_neg h] at hsize` — use `if_pos`/`if_neg` lemmas directly when `simp_all` is just reducing a conditional whose branch is known |
| `simp_all [beq_iff_eq]` for contradiction | `simp only [beq_iff_eq] at *; omega` — when the goal is arithmetic contradiction after BEq→Prop conversion |

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

### When `simp_all?` fails: use `grind`

If `simp_all?` doesn't produce a usable suggestion (e.g., when `simp_all`
is handling deeply nested case-splitting across multiple hypotheses), try
`grind` as a replacement. `grind` handles the same class of problems as
`simp_all` (hypothesis rewriting + case splitting) but through a different
mechanism. This was discovered in the Fse.lean review (PR #909) where
`simp_all only [...]` blocked on hypothesis rewriting side effects but
`grind` closed the goal directly.

**Decision tree for `simp_all` resistance**:
1. Try `simp_all?` → use suggestion if it works
2. Try `grind` → use if it closes the goal
3. Try decomposition: `simp only [...] at *; omega` or per-hypothesis targeting
4. Accept `simp_all only [...]` with best-effort lemma list

### Campaign status

Both bare `simp` and bare `simp_all` campaigns are complete across the
entire codebase as of 2026-03-08. New code should maintain zero bare
`simp` and zero bare `simp_all`. The batch-then-apply workflow from
Phase 3 was the key efficiency breakthrough, reducing per-file review
time from ~20 build cycles to 2-3.

### Post-campaign: next review targets

With bare simp/simp_all elimination complete, future review sessions
should focus on (in priority order):

1. **Dead hypotheses**: `have` bindings whose names never appear in
   later tactics (but verify they're not implicitly used by `omega`
   or `simp` — see Phase 2c above)
2. **Redundant lemmas**: Private theorems used only once, or theorems
   whose statement is a trivial consequence of another
3. **Proof compression**: Multi-line proofs that could be shortened
   via `grind`, tactic chaining (`<;>`), or helper extraction
4. **`sorry` elimination**: Track E content theorems with remaining
   `sorry` placeholders
5. **Consistency**: Ensure naming conventions match across similar
   theorem families (e.g., all position-advancement theorems use
   `_pos_gt` suffix consistently)

### Review campaign completion status (2026-03-12)

**DEFLATE write-side** — all audited:
BitstreamWriteCorrect, BitWriterCorrect, DeflateDynamicHeader,
DeflateDynamicEmit, DeflateDynamicCorrect, DeflateDynamicFreqs,
DeflateEncode, DeflateEncodeProps,
DeflateEncodeDynamic, DeflateEncodeDynamicProps, HuffmanEncode,
HuffmanEncodeCorrect, DynamicTreesCorrect, DynamicTreesComplete,
GzipCorrect, ZlibCorrect, DeflateRoundtrip

**DEFLATE read-side** — all audited:
BitstreamCorrect, BitstreamComplete, DecodeCorrect, DecodeComplete,
InflateCorrect, InflateComplete, InflateLoopBounds, InflateRawSuffix,
HuffmanCorrect, HuffmanCorrectLoop, DeflateSuffix,
DeflateStoredCorrect, DeflateFixedCorrect,
LZ77NativeCorrect, EmitTokensCorrect

**Foundational / cross-cutting** — all audited:
BinaryCorrect, BitReaderInvariant

**Checksum + Huffman base** — all audited:
Adler32, Crc32, Huffman, DeflateFixedTables

**Remaining unaudited spec files** (for future review sessions):
HuffmanKraft, HuffmanTheorems,
LZ77, LZ77Lazy,
XxHash (4 intentional sorries, special status),
Zstd spec files (ZstdFrame, ZstdHuffman, ZstdSequence, Fse, Zstd, Deflate)

### Patterns discovered during the review campaign

**UInt8-to-Nat `have` for omega**: When `split` gives UInt8 comparison
hypotheses (e.g., `hlen_pos : sym.len > 0` where `sym.len : UInt8`),
`omega` cannot reduce the UInt8 comparison. A `have hlen_pos_nat :
sym.len.toNat > 0 := by ...` is NOT dead — it's an intentional type
annotation that provides the Nat version `omega` needs. Don't remove.

**`exact nomatch (h ▸ h)` limitation**: This concise error-branch
closer hits `maxRecDepth` after unfolding large definitions (e.g.,
`inflateRaw`). For those cases, retain the two-step pattern:
`simp only [h] at h; exact absurd h nofun`.

**Stale counts in issues**: Always verify the issue's bare simp counts
against master before starting. Multiple agents may clean the same
files in overlapping sessions. Use `coordination skip` if the file is
already clean.

**`show ... from` wrappers**: After `simp only` unfolds let-bindings,
`show T from h` wrappers become redundant when `h` already has type `T`.
Remove these to reduce noise.

**Identical split branches**: Use `<;>` combinator to merge identical
branches in multi-case `split` blocks (e.g., GzipCorrect/ZlibCorrect
compress theorems).

**`List.length_replicate` over expansion**: Replace verbose
`List.reduceReplicate` + `List.length_cons` + `List.length_nil` chains
with direct `List.length_replicate`.

**`brAppend` `bitPos` equality for `omega`**: When `brAppend` (an
`abbrev` preserving `pos` and `bitOff`) is used, `omega` cannot see
that `(brAppend br suffix).bitPos = br.bitPos` because `bitPos` is a
`def`. The anonymous `have : (brAppend br suffix).bitPos = br.bitPos
:= rfl` is NOT dead — it provides the equality that `omega` needs.

**Tactic macro hygiene**: `set_option hygiene false` local tactic
macros CAN capture names introduced by `obtain` destructuring (e.g.,
`bfinal` from `obtain ⟨bfinal, br₁⟩ := p`). This is useful for DRYing
repeated tactic blocks — see `bfinal_suffix_dispatch` in
`InflateRawSuffix.lean` which captures `bfinal`, `br'`, `out'`, `h`,
`ih` from the surrounding proof context.

**Tactic macro quotation syntax**: When extracting repeated tactic
blocks into `local macro "name" : tactic`, the `·` (bullet/focus dot)
syntax does NOT work inside `\`(tactic| ...)` quotations. Use `next =>`
instead. Wrap the entire tactic in parentheses to parse correctly:
```lean
set_option hygiene false in
local macro "my_tactic" : tactic =>
  `(tactic| (
    by_cases h : condition
    next => tactic_for_true
    next => tactic_for_false))
```

**`show T; omega` for structure projections**: `omega` cannot reduce
structure projections (e.g., `(BitReader.mk data startPos 0).bitOff`).
Use `show 0 < 8; omega` to explicitly narrow the goal before calling
`omega`. Do NOT simplify to `by omega` — it will fail.

**`obtain/subst/constructor` → `obtain/exact` compression**: Replace:
```lean
obtain ⟨hval, hbr'⟩ := h
subst hbr'; constructor
· exact hval
· rfl
```
With the more concise one-liner:
```lean
obtain ⟨hval, hbr'⟩ := h; subst hbr'; exact ⟨hval, rfl⟩
```

**Multi-step injection → single expression**: Replace:
```lean
have : some (a, b) = some (a, c) := h₁.symm.trans h₂
have heq := Option.some.inj this
have : b = c := (Prod.mk.inj heq).2
rw [this]; exact hfinal
```
With:
```lean
rw [(Prod.mk.inj (Option.some.inj (h₁.symm.trans h₂))).2]; exact hfinal
```

**Tactic macro quotation syntax**: When extracting repeated tactic
blocks into `local macro "name" : tactic`, the `·` (bullet/focus dot)
syntax does NOT work inside `\`(tactic| ...)` quotations. Use `next =>`
instead. Wrap the entire tactic in parentheses to parse correctly:
```lean
set_option hygiene false in
local macro "my_tactic" : tactic =>
  `(tactic| (
    by_cases h : condition
    next => tactic_for_true
    next => tactic_for_false))
```

**`show T; omega` for structure projections**: `omega` cannot reduce
structure projections (e.g., `(BitReader.mk data startPos 0).bitOff`).
Use `show 0 < 8; omega` to explicitly narrow the goal before calling
`omega`. Do NOT simplify to `by omega` — it will fail.

## Phase 3c: Proof Compression

After bare-simp cleanup, look for opportunities to shorten proofs
without changing theorem statements. Discovered across PRs #885, #886,
#900, #908:

### `grind` for deeply nested monadic case-splitting

When a proof requires 4+ nested `split at h` blocks to handle monadic
branches, `grind` often closes the goal in one step. This is the
correct use case for `grind` — deeply nested case-splitting where
manual `split` would produce 20+ lines.

**When to use**: Monadic chains with 3+ sequential `bind` operations
where each has error/ok branches.

**When NOT to use**: Simple goals where `omega`, `simp only`, or a
single `split` suffices. `grind` is a sledgehammer — don't use it for
nails.

### Tactic chaining with `<;>`

Compress repeated case-handling patterns:

```lean
-- Before (6 lines per error branch, 8 branches = 48 lines)
split at h
· exact nomatch h
split at h
· exact nomatch h
...

-- After (2 lines for all 8 branches)
split at h; next => exact nomatch h
split at h; next => exact nomatch h
```

Or for multiple identical closers:

```lean
-- Before
· omega
· omega
· omega

-- After (all three goals)
all_goals omega
```

### Local tactic macros for repeated patterns

When a proof pattern repeats 3+ times in a file, extract a local
tactic macro:

```lean
set_option hygiene false in
local macro "unfold_except" : tactic =>
  `(tactic| simp only [bind, Except.bind, pure, Except.pure] at h)
```

**Note**: `set_option hygiene false` is needed to capture `h` by name.
Always scope as `local` to avoid global pollution.

### Helper lemma extraction

When 3+ proofs share the same monadic unfolding pattern (unfold →
case-split errors → extract key fact), extract a private helper:

```lean
private theorem myFunction_elim ...
    (h : myFunction x = .ok (a, b)) :
    subCallA x = .ok intermediateResult ∧ ... := by
  -- 13 lines of monadic unfolding, done once
```

Each downstream proof then becomes 2-3 lines instead of 13.

### Dead code removal

Search for unused private theorems and helper definitions:
```bash
# Find private theorem definitions
grep -n 'private theorem\|private def' File.lean
# For each, check if it's referenced elsewhere in the file
grep -n 'theoremName' File.lean
```

Remove unreferenced private definitions.

### Unused `termination_by` / `decreasing_by` clauses

When Lean can infer termination automatically, explicit
`termination_by` and `decreasing_by` clauses are unnecessary. Remove
them to reduce noise, but only after verifying the file still builds.

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
