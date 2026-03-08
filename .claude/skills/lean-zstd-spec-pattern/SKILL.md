---
name: lean-zstd-spec-pattern
description: Use when creating or extending Zstd specification files in Zip/Spec/. Covers the standard file structure, naming conventions, predicate design, and proof difficulty scoping for Zstd validity predicates.
allowed-tools: Read, Edit, Write, Bash, Glob, Grep
---

# Zstd Spec File Creation Pattern

Patterns distilled from creating `Zip/Spec/Fse.lean`, `Zip/Spec/Zstd.lean`,
`Zip/Spec/ZstdHuffman.lean`, and `Zip/Spec/ZstdSequence.lean` across 8+ PRs.

## Standard File Structure

Every Zstd spec file follows this skeleton:

```lean
import Zip.Native.X           -- Import the implementation types

/-!
# Title (RFC 8878 §N.N)

Brief description of what this module specifies.

The specification is structured in layers:
1. **Layer one**: ...
2. **Layer two**: ...
3. **Layer three**: ...

All predicates have `Decidable` instances for use with `decide`.
-/

namespace Zstd.Spec.ModuleName

open Zip.Native (Type1 Type2)    -- Open only what's needed

/-! ## Helper computations -/

-- Pure functions used by predicates (e.g. weightSum, cellCount)

/-! ## Validity predicates -/

-- Predicates with Decidable instances

/-! ## Correctness theorems -/

-- Theorems connecting implementation functions to predicates
-- (some proven, some sorry)

/-! ## Concrete validation examples -/

-- `by decide` tests on specific inputs

end Zstd.Spec.ModuleName
```

## Naming Conventions

| Kind | Pattern | Examples |
|------|---------|---------|
| Validity predicate | `Valid*` | `ValidWeights`, `ValidDistribution`, `ValidFseTable`, `ValidBlockHeader` |
| Boolean predicate | `is*` / `valid*` (lowercase) | `isPow2`, `validMagic`, `isSkippableMagic` |
| Characterization theorem | `*_iff` | `isPow2_iff` |
| Bound theorem | `*_pos`, `*_le`, `*_ge` | `decodeFseDistribution_accuracyLog_ge`, `buildZstdHuffmanTable_maxBits_pos` |
| Size/structural theorem | `*_tableSize`, `*_size` | `buildZstdHuffmanTable_tableSize` |
| Concrete example | descriptive name | `weightSum_empty`, `kraft_two_ones`, `predefined_litLen_valid` |
| Completeness predicate | `*Complete` | `KraftComplete` |
| Helper computation | camelCase noun | `weightSum`, `cellCount` |

## Predicate Design

### Always include `Decidable` instances

Every predicate must have a `Decidable` instance so concrete examples
can be proved by `decide`:

```lean
def ValidWeights (weights : Array UInt8) : Prop :=
  weights.size >= 1 /\
  (exists i : Fin weights.size, weights[i].toNat > 0) /\
  (forall i : Fin weights.size, weights[i].toNat <= 13)

instance {weights : Array UInt8} : Decidable (ValidWeights weights) :=
  inferInstanceAs (Decidable (_ /\ _ /\ _))
```

The `inferInstanceAs` pattern works because Lean can synthesize
`Decidable` for conjunctions, disjunctions, quantifiers over `Fin`,
and basic arithmetic comparisons automatically.

### Structure predicates as conjunctions

Use `_ /\ _ /\ _` for multi-property predicates rather than nested
structures. This lets `inferInstanceAs (Decidable (_ /\ _ /\ _))` work
directly.

### Import only the implementation module

Each spec file imports exactly one `Zip.Native.*` module and uses
`open Zip.Native (...)` to bring in only the needed types. Don't import
other spec files unless there's a genuine dependency.

## Proof Difficulty Scoping

### Prove immediately (with `decide`, `rfl`, or simple case analysis)

- Concrete validation examples on specific inputs
- `rfl` for definitional equalities (e.g., `weightSum_eq_inline`)
- `decide` for finite predicate checking (e.g., `predefined_litLen_valid`)
- Simple case splits on small enums (e.g., `parseBlockHeader_type_ne_reserved`)

### Defer with `sorry` (document what technique is needed)

- **Monadic unfolding** of functions with 20+ lines of `if`/`match` —
  see `lean-monad-proofs` skill for the `by_cases` + `rw [if_pos/if_neg]`
  pattern
- **Loop invariant reasoning** over `while` or `for` loops with mutable
  state (e.g., `decodeFseDistribution_sum_correct`)
- **Fold induction** over `Array.foldl` accumulation
  (e.g., `weightSum_pos_of_exists_nonzero`)
- **Bitwise arithmetic** properties like `isPow2_iff` requiring
  `Nat.land` reasoning

Add a docstring to each sorry'd theorem explaining why it's deferred
and what proof strategy is expected.

### Intermediate: monadic guard proofs

Proofs about early guards in monadic functions (e.g., "if the function
succeeds, then condition X holds") are tractable with the patterns in
`lean-monad-proofs`:
- Unfold the function
- `cases` on each monadic operation
- `exact nomatch h` for error branches
- `simp only [Except.ok.injEq, Prod.mk.injEq]` to extract equalities
- Close with `omega` or `rfl`

These are worth attempting in the same session that creates the spec file,
especially for bound theorems (`*_ge`, `*_le`).

## Registering New Spec Files

After creating a new spec file, register it in the project's import tree:
1. Add `import Zip.Spec.NewModule` to `Zip.lean`
2. Verify with `lake build Zip.Spec.NewModule`

## Worked Example: Creating a New Spec File

When creating `Zip/Spec/ZstdFoo.lean`:

1. Read the implementation (`Zip/Native/ZstdFoo.lean`) to identify:
   - Key types and structures
   - Validation checks (guards, bounds, invariants)
   - Constants from RFC sections

2. Design predicates around the validation checks — each guard in the
   implementation suggests a predicate

3. Write concrete examples using known-good inputs (from tests or
   predefined tables)

4. Attempt guard proofs for the simplest theorems (bound checks)

5. Leave loop/fold theorems as `sorry` with docstrings

## Theorem Statement Validation

**Before investing proof effort, validate theorem statements with concrete
examples.** Two false theorems were discovered and corrected during this
project (`parseBlockHeader_blockSize_le` in PR #639, `weightsToMaxBits_valid`
in PR #622). Both cost multiple sessions of wasted proof attempts before
counterexamples were found.

### Validation checklist

1. **`#eval` on concrete inputs**: Test the theorem's conclusion on 2-3
   known-good inputs (from test vectors or RFC examples):
   ```lean
   -- Before proving: parseHeader returns blockSize ≤ 128*1024
   #eval do
     let input := ByteArray.mk #[0x21, 0x00, 0x00]  -- known test vector
     let hdr ← parseBlockHeader input 0
     return hdr.blockSize ≤ 128 * 1024  -- true? or false?
   ```

2. **`decide` on small instances**: For predicates with `Decidable` instances,
   test on boundary cases:
   ```lean
   #eval decide (ValidWeights #[1, 2, 0, 3])  -- should be true
   #eval decide (ValidWeights #[0, 0, 0])      -- should be false
   ```

3. **Check what the implementation actually enforces**: Read the implementation
   code carefully. A parser that reads a 21-bit field does NOT enforce
   `value ≤ 128*1024` — it only enforces `value < 2^21`. The theorem
   should match what the code does, not what the RFC recommends.

4. **Boundary cases**: Test at the edges of claimed bounds:
   - Maximum-size inputs
   - All-zero inputs
   - Inputs that trigger error paths

### When to weaken a theorem

If validation reveals the theorem is false, **weaken it to what's actually
provable** rather than abandoning it:
- `blockSize ≤ 128*1024` → `blockSize < 2^21` (what the parser enforces)
- `weight > 0` → `∃ i, weights[i] > 0` (existence, not universality)

Document the weakening with a comment explaining the original intent and
why it was too strong.

## Size and Content Theorems for WF Helper Functions

Functions like `copyBytes` and `copyMatch` use well-founded recursion
(termination by `count` or `length - k`). Their spec theorems follow a
consistent 3-theorem pattern:

1. **Size theorem**: `f_size` — output size equals input size + amount copied
2. **Preservation theorem**: `f_getElem_lt` — existing bytes are unchanged
3. **Content theorem**: `f_getElem_ge` — new bytes have expected values

### Proof structure

All three use **induction matching the WF recursion**:

```lean
theorem copyBytes_size (dst src : ByteArray) (srcPos count : Nat) :
    (copyBytes dst src srcPos count).size = dst.size + count := by
  induction count generalizing dst srcPos with
  | zero => simp [copyBytes]
  | succ n ih =>
    rw [copyBytes.eq_1]               -- one-level unfold via equation lemma
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    rw [ih, ByteArray.size_push]; omega
```

Key patterns:
- **`rw [f.eq_1]`** for one-level unfold (never `simp only [f]` — it loops)
- **`generalizing dst srcPos`** when the function modifies these per step
- **Size lemmas compose**: `rw [copyMatch_size, copyBytes_size] at this; omega`
  chains through multiple operations in loop invariant proofs

### Content theorems: non-overlapping vs overlapping

Non-overlapping `copyMatch` (`offset ≥ length`) is straightforward: each
new byte reads from the original buffer at a fixed position.

Overlapping `copyMatch` (`offset < length`) requires tracking that each
new byte reads from the *growing* buffer, creating a repeating pattern.
The proof threads a `hprefix` invariant through the induction:
```lean
(hprefix : ∀ i, i < buf.size → b[i]! = buf[i]!)
```

## Table Correctness via `rcases` Case Split

For proving properties about lookup tables (`litLenExtraBits`,
`matchLenExtraBits`, offset baseline tables), the standard approach is:

```lean
theorem decodeLitLenValue_small (code : Nat) (extraBits : UInt32) (h : code ≤ 15) :
    decodeLitLenValue code extraBits = .ok (code + extraBits.toNat) := by
  have hlt : code < litLenExtraBits.size := by simp only [litLenExtraBits_size]; omega
  unfold decodeLitLenValue
  simp only [hlt, ↓reduceDIte]
  rcases code with _ | _ | _ | _ | _ | _ | _ | _ |
                   _ | _ | _ | _ | _ | _ | _ | _ | _
  all_goals first | omega | rfl
```

**Pattern**: Eliminate `dite`/bounds check → `rcases` into N+1 arms
(N valid + 1 impossible) → close each with `rfl` or `omega`.

**Scaling**: This works for tables up to ~50 entries (tested with 32-entry
match length table). Beyond that, build times may become excessive.

## Exhaustive Case Analysis for Branch-Heavy Functions

Functions like `resolveOffset` that branch on multiple conditions
(rawOffset value × literalLength zero/nonzero) benefit from exhaustive
`rcases` decomposition:

```lean
rcases rawOffset with _ | _ | _ | _ | n
· omega  -- rawOffset = 0, impossible
· -- rawOffset = 1
  simp only [resolveOffset, show ¬(1 > 3) from by omega,
    show litLen > 0 from hlit, ↓reduceIte]
  exact h0pos
· -- rawOffset = 2 ...
· -- rawOffset = 3 ...
· -- rawOffset = n + 4 > 3
  simp only [resolveOffset, show n + 4 > 3 from by omega, ↓reduceIte]
  omega
```

**Key techniques**:
- **Inline `show` proofs**: `show ¬(N > 3) from by omega` provides the
  condition directly to `simp only` without a separate `have`
- **`↓reduceIte`**: reduces `if true/false then A else B` after the
  condition is resolved
- **`split` for inner branches**: after resolving the outer condition,
  `split` handles `if litLen > 0 then ... else ...` cleanly

For ValidOffsetHistory preservation through each branch:
```lean
refine ⟨rfl, ?_, ?_, ?_⟩ <;> simp <;> omega
```
This handles all three positivity goals at once. The bare `simp` reduces
`#[a, b, c][0]!` etc., and `omega` closes the arithmetic.

**Array literal access exemption**: When the goal involves `#[a,b,c][i]!`
for a *known* array literal with *concrete* index, bare `simp` is
acceptable — `simp only` requires listing `Array.getElem!_eq_getD`,
`Array.getD`, `Array.get_push_lt/eq`, and `List.get` lemmas that vary
by position and produce linter warnings. Add comment:
`-- bare simp: array literal access`

## Loop Invariant Theorems via Equation Lemma Matching

For WF-recursive loop functions like `executeSequences.loop`, the loop
invariant proof matches the function's equation lemmas:

```lean
theorem executeSequences_loop_inv (seqs : List ZstdSequence) ... := by
  induction seqs generalizing output history litPos with
  | nil =>
    rw [executeSequences.loop.eq_1] at h  -- base case equation
    simp at h; obtain ⟨rfl, _, rfl⟩ := h; ...
  | cons seq rest ih =>
    rw [executeSequences.loop.eq_2] at h  -- recursive case equation
    split at h  -- split on first guard
    · simp at h  -- error branch: contradiction
    · ...
      split at h  -- next guard
      dsimp only [letFun] at h  -- reduce letFun between splits
      split at h; · simp at h  -- error
      · ...
        have ⟨ih_size, ih_le, ih_bound⟩ := ih _ _ _ hlp' h
        rw [copyMatch_size, copyBytes_size] at ih_size  -- compose sizes
```

**Key patterns**:
- **`rw [f.eq_N]` not `unfold f`**: equation lemmas target specific cases
- **`dsimp only [letFun]`** between `split at h` steps: Lean inserts
  `letFun` wrappers that block further `split`
- **`simp at h` for error branches**: closes `Except.error = Except.ok`
  contradictions (or use `exact nomatch h`)
- **Compose size lemmas**: chain `rw [f_size, g_size]` in the hypothesis
  before using `omega`

## Position-Advancement Proofs

Parser functions in `Except` monad return `(result, pos')`. Proving
`pos' > pos` (or `pos' = pos + k`) is the standard way to establish
that a parser consumes input, which feeds WF termination obligations.

### Naming convention: `_pos_gt` vs `_pos_ge` vs `_pos_eq` vs `_le_size`

Choose the suffix based on the tightest bound you can prove:

| Suffix | Meaning | When to use |
|--------|---------|-------------|
| `_pos_eq` | `pos' = pos + k` (exact) | Parser reads a fixed number of bytes (e.g., `parseBlockHeader` always reads 3) |
| `_pos_gt` | `pos' > pos` (strict) | Parser reads at least 1 byte but exact count varies (e.g., `decompressFrame`) |
| `_pos_ge` | `pos' ≥ pos` (weak) | Some branches don't advance (e.g., `resolveSingleFseTable` with `repeat` mode returns `pos' = pos`) |
| `_le_size` | `pos' ≤ data.size` | Returned position stays within data bounds (feeds `getElem` preconditions) |
| `_pos_bounded` | `pos' ≤ pos + k` | Upper bound complement to `_pos_gt` (together give tight range) |

**Prefer the tightest bound**: `_pos_eq` > `_pos_gt` > `_pos_ge`. Stricter bounds
are more useful for callers (exact bounds compose better than inequalities).

**Deriving weaker from stronger**: A `_pos_eq` theorem trivially implies `_pos_gt`
and `_pos_ge` via `omega`. A `_pos_gt` implies `_pos_ge`. Don't prove both unless
callers specifically need the weaker form for API compatibility.

### Standard proof template

```lean
theorem myParser_pos_gt (data : ByteArray) (pos : Nat)
    (result : ResultType) (pos' : Nat)
    (h : myParser data pos = .ok (result, pos')) :
    pos' > pos := by
  -- 1. Unfold and reduce monadic plumbing
  simp only [myParser, bind, Except.bind, pure, Except.pure] at h
  -- 2. Case-split each guard/branch
  split at h
  · exact nomatch h          -- error branch
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h     -- extract pos' = pos + k
    omega
```

### Multi-branch functions: prove a range, derive components

When a function has N branches that each advance by different amounts,
prove the conjunction in a private helper and derive separate theorems:

```lean
private theorem myParser_pos_range ... (h : ...) :
    pos < pos' ∧ pos' ≤ pos + 4 := by
  simp only [myParser, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  split at h
  · exact nomatch h
  · split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, -, rfl⟩ := h; omega
    · -- ... repeat for each branch
      sorry

theorem myParser_pos_gt ... (h : ...) : pos' > pos :=
  (myParser_pos_range ... h).1

theorem myParser_pos_bounded ... (h : ...) : pos' ≤ pos + 4 :=
  (myParser_pos_range ... h).2
```

This avoids duplicating the case analysis across two separate proofs.

### Composing position-advancing functions

When function A calls B then C sequentially, compose their position
specs rather than re-unfolding both:

```lean
theorem composed_pos_gt ... := by
  -- Extract intermediate position from monadic chain
  cases hB : B data pos with
  | error => simp only [hB] at h; exact nomatch h
  | ok val =>
    obtain ⟨resultB, posB⟩ := val
    simp only [hB] at h; dsimp only [bind, Except.bind] at h
    -- Use B's spec
    have hB_gt := B_pos_gt ... hB
    -- Continue with C
    cases hC : C data posB with
    | error => simp only [hC] at h; exact nomatch h
    | ok val =>
      have hC_gt := C_pos_gt ... hC
      omega
```

### Worked composition example: `decompressFrame_pos_gt`

`decompressFrame` calls `parseFrameHeader` then `decompressBlocksWF`. Rather
than re-unfolding both functions, compose their position specs:

```lean
theorem decompressFrame_pos_gt ... (h : decompressFrame data pos = .ok (output, pos')) :
    pos' > pos := by
  unfold decompressFrame at h
  cases hph : parseFrameHeader data pos with
  | error e => simp only [hph, bind, Except.bind] at h; exact nomatch h
  | ok val =>
    obtain ⟨header, afterHeader⟩ := val
    have hgt1 := parseFrameHeader_pos_gt _ _ _ _ hph    -- afterHeader > pos
    simp only [hph, bind, Except.bind, pure, Except.pure] at h
    ...
    cases hdb : decompressBlocksWF data afterHeader ... with
    | error e => simp only [hdb] at h; exact nomatch h
    | ok val2 =>
      obtain ⟨content, afterBlocks⟩ := val2
      have hgt2 := decompressBlocksWF_pos_gt _ _ _ _ _ _ _ _ _ hdb  -- afterBlocks > afterHeader
      ...  -- omega closes: pos' ≥ afterBlocks > afterHeader > pos
```

**Pattern**: At each monadic bind, case-split on the sub-call, dismiss error
with `nomatch`, extract the ok result, and invoke the sub-call's `_pos_gt`
theorem as a `have`. After all binds are processed, `omega` (or `grind`)
chains the inequalities.

### Mode-dispatched functions (`resolveSingleFseTable` pattern)

Functions like `resolveSingleFseTable` that dispatch on a compression
mode enum (predefined/RLE/repeat/fseCompressed) need per-mode theorems:

| Mode | Position change | Proof sketch |
|------|----------------|--------------|
| `predefined` | `pos' = pos` | Direct — returns `(buildFromPredefined ..., pos)` |
| `rle` | `pos' = pos + 1` | Reads one byte for symbol |
| `repeat` | `pos' = pos` | Returns `(prevTable, pos)` |
| `fseCompressed` | `pos' ≥ pos + 1` | Calls `decodeFseDistribution` + byte-alignment |

Each theorem uses the same structure:
1. `simp only [resolveSingleFseTable, bind, Except.bind, pure, Except.pure] at h`
2. `split at h` to match the mode
3. Close impossible branches with `exact nomatch h`
4. Extract position from `Except.ok.injEq, Prod.mk.injEq`

The fseCompressed case is harder because it involves `BitReader`
byte-alignment: `if br'.bitOff == 0 then br'.pos else br'.pos + 1`.
This introduces a `by_cases` or `split` on `bitOff` and requires a
separate lemma about `decodeFseDistribution` advancing the bit position.

### Position specs feed WF termination

These position-advancement theorems are not standalone — they serve as
building blocks for `termination_by data.size - pos` obligations in
WF-recursive functions like `decompressBlocksWF` and `decompressZstdWF`.
The chain is:

1. Per-parser `_pos_gt` theorems prove strict advancement
2. WF function adds guard `if hadv : afterPos ≤ pos then throw`
3. Guard gives `¬(afterPos ≤ pos)`, combined with `_pos_gt` gives
   `afterPos > pos`, which proves `data.size - afterPos < data.size - pos`
4. `omega` closes the termination obligation

See `lean-wf-recursion` skill, "Non-Advancement Guard Pattern".

### `_le_size` proofs: position stays within data bounds

The `_le_size` theorems prove that a parser's returned position doesn't exceed
`data.size`. These feed `getElem` preconditions when subsequent code accesses
`data[pos']`.

**Standard template** (completely mechanical):

```lean
theorem myParser_le_size (data : ByteArray) (pos : Nat)
    (result : ResultType) (pos' : Nat)
    (h : myParser data pos = .ok (result, pos')) :
    pos' ≤ data.size := by
  -- Option A: derive from _pos_eq + guard negation
  have hpos := myParser_pos_eq data pos result pos' h
  unfold myParser at h
  split at h
  · exact nomatch h                -- error: guard `pos + k > data.size` held
  · subst hpos; omega              -- success: guard failed, so pos + k ≤ data.size
  -- Option B: derive directly from _pos_eq + _pos_gt when available
  -- have hpe := myParser_pos_eq ... h
  -- have hgt := myParser_pos_gt ... h   -- only if the function also has _pos_gt
  -- omega
```

**The key insight**: parser functions check `if pos + n > data.size then throw`
as a guard. On the success path, the guard's negation gives `pos + n ≤ data.size`,
and since `pos' = pos + n` (from `_pos_eq`), we get `pos' ≤ data.size`.

**Layering**: prove `_pos_eq` first (exact value), then derive both `_pos_gt` and
`_le_size` as trivial corollaries. This avoids duplicating the unfolding work.

**Established `_le_size` theorems**:
- `parseBlockHeader_le_size` — derives from `_pos_eq`, unfold + nomatch + omega
- `decompressRawBlock_le_size` — same pattern
- `decompressRLEBlock_le_size` — same pattern
- `skipSkippableFrame_le_size` — same pattern
- `parseFrameHeader_le_size` — multi-branch, uses `_pos_eq` per branch
- `parseSequencesHeader_le_size` — multi-branch with 1/2/3-byte encodings

### Bitwise bound lemmas for value specs

When proving bounds on parsed values that use bitmask operations:

| Lemma | Use case |
|-------|----------|
| `Nat.and_le_right` | `x &&& mask ≤ mask` — bitmask extracts at most `mask` |
| `Nat.or_lt_two_pow` | `x ||| y < 2^n` when both `x < 2^n` and `y < 2^n` |
| `UInt32.toNat_or` | Bridge `(a ||| b).toNat = a.toNat ||| b.toNat` |
| `UInt32.toNat_shiftLeft` | Bridge `(a <<< n).toNat` |
| `Nat.shiftLeft_eq` | `x <<< n = x * 2^n` |

These appear in `parseCompressedLiteralsHeader_regen_bound` and
`readBits_value_lt_pow2`. The pattern is: convert UInt operations to
Nat via bridge lemmas, apply the Nat bound lemma, close with `omega`.

## Table Validity Composition

Build functions like `buildFseTable` and `buildZstdHuffmanTable` produce
tables that satisfy structural validity predicates (`ValidFseTable`,
`ValidHuffmanTable`). Validity proofs compose from per-property theorems.

### Validity predicate pattern

```lean
def ValidHuffmanTable (table : Array HuffmanCell) (maxBits : Nat) : Prop :=
  table.size = 1 <<< maxBits ∧
  (∀ i : Fin table.size, table[i].numBits ≤ maxBits) ∧
  (∀ i : Fin table.size, table[i].symbol.toNat ≤ 255)

instance : Decidable (ValidHuffmanTable table maxBits) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))
```

### Composition theorem

Prove each conjunct separately, then compose:

```lean
theorem buildZstdHuffmanTable_valid (weights : Array UInt8)
    (result : ZstdHuffmanTable)
    (h : buildZstdHuffmanTable weights = .ok result) :
    ValidHuffmanTable result.table result.maxBits :=
  ⟨buildZstdHuffmanTable_tableSize weights result h,
   fun i => buildZstdHuffmanTable_numBits_le weights result h i,
   fun i => Nat.lt_succ_iff.mp (UInt8.toNat_lt result.table[i].symbol)⟩
```

### Per-property proof patterns

**Size/tableSize** (`_tableSize`): unfold + induction on build loop,
tracking `Array.size_set!` through each step.

**Bound preservation** (`_numBits_le`, `_symbol_lt`): prove for each
`set!` operation using `Array.getElem_set!` case analysis — either the
element was just set (prove for the new value) or it was untouched (use
the induction hypothesis).

**Generic property preservation through `set!`**: When a loop sets array
entries, extract a helper lemma:
```lean
theorem huffman_set!_preserves_forall (table : Array HuffmanCell)
    (P : HuffmanCell → Prop) (hall : ∀ i : Fin table.size, P table[i])
    (idx : Nat) (cell : HuffmanCell) (hcell : P cell)
    (hsz : (table.set! idx cell).size = table.size) :
    ∀ i : Fin (table.set! idx cell).size, P (table.set! idx cell)[i]
```
This factors out the `if idx = i then ... else ...` case split and
avoids duplicating it across multiple property proofs.

### ValidOffsetHistory threading

For offset history validity through loops (`executeSequences.loop`),
prove per-step preservation:

1. **Per-mode theorems**: `resolveOffset_gt3_valid`, `resolveOffset_repeat_valid`
2. **Unified theorem**: `resolveOffset_valid` combining all modes
3. **Loop invariant**: `executeSequences_loop_history_valid` threading
   `ValidOffsetHistory` through the list induction

Use `validOffsetHistory_mk3` to handle the common case of 3-element
arrays: `ValidOffsetHistory #[a, b, c]` when `a > 0 ∧ b > 0 ∧ c > 0`.

## Anti-Patterns

- **Don't restate the implementation**: `f x = fImpl x` proves nothing.
  Predicates should express properties (bounds, invariants, structural
  constraints) independently of implementation details.

- **Don't skip Decidable instances**: Every predicate needs one. Without
  it, concrete examples can't be proved by `decide`.

- **Don't attempt loop proofs in a spec creation session**: These are
  genuinely hard and deserve their own focused session. Creating the
  predicate and stating the theorem is the deliverable.

- **Don't forget the module docstring**: Each spec file begins with
  `/-! ... -/` describing the RFC section, the specification layers,
  and what predicates are defined.

- **Don't validate theorem statements by attempting proof only**: Use
  `#eval` on concrete inputs first to catch false statements early.
  Three false theorems were discovered during this project, each
  costing multiple sessions. See "Theorem Statement Validation" above.

## Cross-References

- **WF recursion patterns** (unfolding, `f.induct`, termination measures):
  `lean-wf-recursion` skill
- **Non-advancement guard for WF termination**:
  `lean-wf-recursion` skill, "Non-Advancement Guard Pattern"
- **Monadic unfolding** (`Except.bind` chains, `nomatch` for contradictions):
  `lean-monad-proofs` skill
- **Bool-to-Prop bridging** (`beq_iff_eq`, `Bool.and_eq_true`):
  `lean-monad-proofs` skill, "`eq_of_beq` for BEq-to-Eq Conversion"
- **Array literal indexing** (`rcases` + `rfl`/`omega`):
  `lean-simp-tactics` skill, "Array Literal Indexing After `rcases` Case Split"
- **`1 <<< n` and `2^n`** in offset decoding proofs:
  `lean-simp-tactics` skill, "`omega` Cannot Handle Exponentiation"
- **Auto-generated dagger lemmas** (`UInt32.reduceBEq✝`):
  `lean-simp-tactics` skill, "Dagger Lemmas" — use `decide` or `show ... from by decide`
- **Content preservation** (`_getElem_lt`, `_prefix` proofs):
  `lean-content-preservation` skill
