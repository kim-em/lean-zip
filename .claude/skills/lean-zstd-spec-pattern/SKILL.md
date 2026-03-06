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
