---
name: lean-zstd-spec-pattern
description: Use when creating or extending Zstd specification files in Zip/Spec/ (Fse.lean, Zstd.lean, ZstdHuffman.lean, ZstdSequence.lean, ZstdFrame.lean). Covers file structure, naming conventions, predicate/Decidable design, position-advancement theorems, table-validity composition, two-block matrix, and frame-level lifting.
allowed-tools: Read, Edit, Write, Bash, Glob, Grep
---

# Zstd Spec File Creation Pattern

Files: `Zip/Spec/Fse.lean`, `Zip/Spec/Zstd.lean`, `Zip/Spec/ZstdHuffman.lean`,
`Zip/Spec/ZstdSequence.lean`, `Zip/Spec/ZstdFrame.lean`.

## File Skeleton

```lean
import Zip.Native.X           -- the implementation types (exactly one Native module)

/-!
# Title (RFC 8878 §N.N)
Layers: 1. helper computations  2. validity predicates  3. correctness theorems.
All predicates have `Decidable` instances for use with `decide`.
-/

namespace Zstd.Spec.ModuleName
open Zip.Native (Type1 Type2)        -- open only what's needed

/-! ## Helper computations -/      -- pure fns: weightSum, cellCount
/-! ## Validity predicates -/      -- predicates + Decidable instances
/-! ## Correctness theorems -/     -- impl fn ↔ predicate
/-! ## Concrete validation examples -/   -- `by decide` on specific inputs

end Zstd.Spec.ModuleName
```

After creating: add `import Zip.Spec.NewModule` to `Zip.lean`; verify with
`lake build Zip.Spec.NewModule`.

## Naming Conventions

| Kind | Pattern | Examples |
|------|---------|---------|
| Validity predicate | `Valid*` | `ValidWeights`, `ValidFseTable`, `ValidBlockHeader` |
| Boolean predicate | `is*` / `valid*` (lowercase) | `isPow2`, `validMagic`, `isSkippableMagic` |
| Characterization | `*_iff` | `isPow2_iff` |
| Bound | `*_pos`, `*_le`, `*_ge` | `buildZstdHuffmanTable_maxBits_pos` |
| Size/structural | `*_tableSize`, `*_size` | `buildZstdHuffmanTable_tableSize` |
| Completeness | `*Complete` | `KraftComplete` |
| Helper computation | camelCase noun | `weightSum`, `cellCount` |
| Concrete example | descriptive | `predefined_litLen_valid` |

## Predicate Design

Structure multi-property predicates as flat conjunctions `_ ∧ _ ∧ _` (not nested
structures), so `inferInstanceAs` synthesizes `Decidable` directly. Lean handles
conjunctions, disjunctions, quantifiers over `Fin`, and arithmetic comparisons.

```lean
def ValidWeights (weights : Array UInt8) : Prop :=
  weights.size >= 1 ∧
  (∃ i : Fin weights.size, weights[i].toNat > 0) ∧
  (∀ i : Fin weights.size, weights[i].toNat <= 13)

instance {weights : Array UInt8} : Decidable (ValidWeights weights) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))
```

Every predicate needs a `Decidable` instance or concrete examples can't `decide`.

## Theorem Statement Validation

Validate statements with `#eval`/`decide` on known-good and boundary inputs
BEFORE proving — false theorems cost multiple wasted sessions to discover.
Check what the code *enforces*, not what the RFC recommends: a parser reading a
21-bit field enforces `value < 2^21`, NOT `value ≤ 128*1024`. If a statement is
false, weaken to what's provable (e.g. `blockSize < 2^21`; `∃ i, weights[i] > 0`
instead of universal) and comment the original intent.

## Proof Difficulty Scoping

Prove now: concrete examples (`decide`), definitional equalities (`rfl`), small
enum case splits, monadic guard bound theorems (`*_ge`/`*_le`). Defer with a
docstring naming the technique: loop-invariant reasoning, `Array.foldl` fold
induction, bitwise arithmetic (`Nat.land`). Stating the predicate + theorem is
the deliverable for a spec-creation session; loop proofs deserve their own.

## Size/Content Theorems for WF Helpers

`copyBytes`/`copyMatch` (WF recursion, terminating on `count` or `length-k`)
follow a 3-theorem pattern, all proved by induction matching the recursion:

1. `f_size` — output size = input size + amount copied
2. `f_getElem_lt` — existing bytes unchanged (preservation)
3. `f_getElem_ge` — new bytes have expected values (content)

```lean
theorem copyBytes_size (dst src : ByteArray) (srcPos count : Nat) :
    (copyBytes dst src srcPos count).size = dst.size + count := by
  induction count generalizing dst srcPos with
  | zero => simp [copyBytes]
  | succ n ih =>
    rw [copyBytes.eq_1]               -- one-level unfold; never `simp only [f]` (loops)
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    rw [ih, ByteArray.size_push]; omega
```

- `generalizing dst srcPos` when the function mutates these per step.
- Size lemmas compose: `rw [copyMatch_size, copyBytes_size] at this; omega`.
- Content: non-overlapping `copyMatch` (`offset ≥ length`) reads from the
  original buffer at a fixed position; overlapping (`offset < length`) reads from
  the *growing* buffer — thread `(hprefix : ∀ i, i < buf.size → b[i]! = buf[i]!)`.

## Table Lookup via `rcases` Case Split

For lookup-table properties (`litLenExtraBits`, `matchLenExtraBits`, offset
baselines): eliminate the `dite`/bounds check, then `rcases` the code into N+1
arms (N valid + 1 impossible), close each with `rfl` or `omega`.

```lean
have hlt : code < litLenExtraBits.size := by simp only [litLenExtraBits_size]; omega
unfold decodeLitLenValue
simp only [hlt, ↓reduceDIte]
rcases code with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
all_goals first | omega | rfl
```

Scales to ~50 entries (tested 32-entry match-length table); beyond that build
times balloon.

## Branch-Heavy Functions (`resolveOffset` pattern)

Functions branching on multiple conditions benefit from exhaustive `rcases`:
- Inline `show` proofs feed conditions to `simp only` without a `have`:
  `simp only [resolveOffset, show ¬(N > 3) from by omega, ↓reduceIte]`.
- `↓reduceIte` reduces `if true/false`; `split` handles inner `if litLen > 0`.
- For `ValidOffsetHistory` preservation across branches:
  `refine ⟨rfl, ?_, ?_, ?_⟩ <;> simp <;> omega` (bare `simp` reduces
  `#[a,b,c][0]!` etc.; `omega` closes arithmetic).

**Array-literal access exemption**: for `#[a,b,c][i]!` with a known literal and
concrete index, bare `simp` is acceptable (`simp only` needs position-varying
`Array.getElem!_eq_getD`/`getD`/`get_push_lt/eq`/`List.get` lemmas and emits
linter warnings). Comment: `-- bare simp: array literal access`.

## Loop Invariants via Equation-Lemma Matching

WF-recursive loops (`executeSequences.loop`) prove invariants by matching the
function's equation lemmas:
- `rw [f.eq_N] at h` (not `unfold f`) — equation lemmas target specific cases
  (`.eq_1` base, `.eq_2` recursive).
- `dsimp only [letFun] at h` between `split at h` steps — Lean inserts `letFun`
  wrappers that block further `split`.
- `simp at h` (or `exact nomatch h`) closes `Except.error = Except.ok` branches.
- Compose size lemmas in the hypothesis before `omega`:
  `rw [copyMatch_size, copyBytes_size] at ih_size`.

## Position-Advancement Proofs

Parsers in `Except` return `(result, pos')`. Proving advancement feeds WF
termination obligations (`termination_by data.size - pos`).

| Suffix | Meaning | When |
|--------|---------|------|
| `_pos_eq` | `pos' = pos + k` (exact) | parser reads a fixed byte count (`parseBlockHeader` reads 3) |
| `_pos_gt` | `pos' > pos` (strict) | reads ≥1 byte, count varies (`decompressFrame`) |
| `_pos_ge` | `pos' ≥ pos` (weak) | some branches don't advance (`resolveSingleFseTable` `repeat` mode → `pos' = pos`) |
| `_le_size` | `pos' ≤ data.size` | returned position within bounds (feeds `getElem` preconditions) |
| `_pos_bounded` | `pos' ≤ pos + k` | upper-bound complement to `_pos_gt` |

Prefer the tightest: `_pos_eq` > `_pos_gt` > `_pos_ge`. `_pos_eq` implies the
others via `omega`; don't prove weaker forms unless a caller needs them.

```lean
-- standard template
simp only [myParser, bind, Except.bind, pure, Except.pure] at h
split at h
· exact nomatch h                                   -- error branch
· simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h; omega                        -- extract pos' = pos + k
```

**Multi-branch**: prove the conjunction `pos < pos' ∧ pos' ≤ pos + k` in a
`private` helper, then derive `_pos_gt := (...).1` and `_pos_bounded := (...).2`
to avoid duplicating case analysis.

**Composition** (A calls B then C): at each bind, `cases hB : B data pos`,
dismiss error with `nomatch`, `obtain` the ok result, invoke `B_pos_gt` as a
`have`; after all binds, `omega`/`grind` chains the inequalities. Used by
`decompressFrame_pos_gt` (composes `parseFrameHeader_pos_gt` then
`decompressBlocksWF_pos_gt`).

**Mode-dispatched** (`resolveSingleFseTable`): per-mode theorems —
`predefined` `pos'=pos`, `rle` `pos'=pos+1`, `repeat` `pos'=pos`, `fseCompressed`
`pos'≥pos+1`. fseCompressed is hardest: `BitReader` byte-alignment
`if br'.bitOff == 0 then br'.pos else br'.pos+1` forces a `by_cases`/`split` on
`bitOff` plus a lemma about `decodeFseDistribution` advancing the bit position.

**`_le_size`** is mechanical: parsers guard `if pos + n > data.size then throw`;
the success-path guard negation gives `pos + n ≤ data.size`, and `_pos_eq` gives
`pos' = pos + n`. Prove `_pos_eq` first, derive `_le_size` and `_pos_gt` as
corollaries. Established: `parseBlockHeader_le_size`, `decompressRawBlock_le_size`,
`decompressRLEBlock_le_size`, `skipSkippableFrame_le_size`,
`parseFrameHeader_le_size` (multi-branch), `parseSequencesHeader_le_size`.

**Bitwise value bounds**: convert UInt ops to Nat via bridges
(`UInt32.toNat_or`, `UInt32.toNat_shiftLeft`, `Nat.shiftLeft_eq`), apply the Nat
bound (`Nat.and_le_right`, `Nat.or_lt_two_pow`), close with `omega`. Appears in
`parseCompressedLiteralsHeader_regen_bound`, `readBits_value_lt_pow2`.

## Table Validity Composition (five-layer chain)

```
Per-cell properties (symbol_lt, numBits_le, cells_size)
  → ValidFseTable composition (buildFseTable_valid, buildRleFseTable_valid)
  → Predefined validity (buildPredefinedFseTables_*_valid)
  → Resolver validity (resolveSingleFseTable_*_valid)
  → Composed validity (resolveSequenceFseTables_valid)
```

Predicate is a flat conjunction; compose the validity theorem from per-conjunct
theorems:

```lean
theorem buildZstdHuffmanTable_valid (weights) (result)
    (h : buildZstdHuffmanTable weights = .ok result) :
    ValidHuffmanTable result.table result.maxBits :=
  ⟨buildZstdHuffmanTable_tableSize weights result h,
   fun i => buildZstdHuffmanTable_numBits_le weights result h i,
   fun i => Nat.lt_succ_iff.mp (UInt8.toNat_lt result.table[i].symbol)⟩
```

Per-property proofs: `_tableSize` — induction on build loop tracking
`Array.size_set!`; bound preservation (`_numBits_le`, `_symbol_lt`) — per `set!`
via `Array.getElem_set!` case analysis (just-set value vs untouched → IH).
Factor the `if idx = i then ... else ...` split into a reusable helper
(`huffman_set!_preserves_forall`) to avoid duplication across property proofs.

**Layer preconditions**:
- `buildFseTable_valid` needs `0 < probs.size`: cells default to `symbol = 0`;
  empty `probs` leaves `symbol.toNat < probs.size` as `0 < 0` (unprovable).
  Required by `buildFseTable_valid` and `_symbol_lt`, NOT `_numBits_le`.
- `buildRleFseTable_valid` (al=0, 1 cell) needs `symbol.toNat < numSymbols`;
  the cell has `numBits = 0`, proved by `decide`.
- Predefined tables discharge `hpos` by `decide`: `_litLen_valid` (al=6, 36),
  `_matchLen_valid` (al=6, 53), `_offset_valid` (al=5, 29). Extract the build
  call from the bind chain via `Except.bind_eq_ok'`, then `buildFseTable_valid`.
- Resolver dispatches on mode: `predefined`→predefined validity,
  `rle`→`buildRleFseTable_valid` (prove `symbol < maxSymbols`),
  `repeat`→caller's hypothesis (prior block's table), `fseCompressed`→
  `buildFseTable_valid` after existential-extracting the decoded distribution.

**ValidOffsetHistory threading**: per-mode (`resolveOffset_gt3_valid`,
`resolveOffset_repeat_valid`) → unified `resolveOffset_valid` → loop invariant
`executeSequences_loop_history_valid` over the list induction. Use
`validOffsetHistory_mk3` for the common 3-element case.

## Frame-Level Composition

Frame loop `decompressZstdWF` uses WF recursion. Hierarchy:
`decompressZstdWF_base` → `_single_standard_frame` → `_single_skippable_frame`
→ `_skip_then_standard` → `_standard_then_standard`.

Single-frame proof: unfold; discharge `pos < data.size` guard from `hsize`+omega;
rewrite magic via `hmagic`; rewrite frame via `hframe`; simplify advancement via
`hadv`; apply `_base` when `pos' ≥ data.size`. Multi-frame theorems chain
linearly — unfold to the dispatch, simplify, apply the single-frame theorem at
the new position, threading `output` and `pos`.

Magic: skippable range `[0x184D2A50, 0x184D2A5F]` uses two bounds hypotheses
(`≥ lo`, `≤ hi`) + `decide_eq_true` for the `Bool.and`; standard `0xFD2FB528`
via `parseFrameHeader_magic`.

**API lifting (WF → public)**: wrap with `pos=0`, `output=ByteArray.empty`.
Extract implicit preconditions from the successful `decompressFrame`:

```lean
have ⟨hdr, afterHdr, hph⟩ : ∃ hdr afterHdr,
    parseFrameHeader data 0 = .ok (hdr, afterHdr) := by
  unfold decompressFrame at hframe
  cases hc : parseFrameHeader data 0 with
  | error e => simp only [hc, bind, Except.bind] at hframe; exact nomatch hframe
  | ok val => exact ⟨val.1, val.2, rfl⟩
```

Then `parseFrameHeader_magic`/`_le_size` and `decompressFrame_pos_gt`; finish
with `ByteArray.empty_append content`.

WF-level induction theorems (`_output_size_ge`, `_prefix`) use
`induction pos, output using decompressZstdWF.induct (data := data) generalizing result`
with three cases: base (`_base`), error (contradict `.ok`), main (dispatch on
magic, apply IH per branch).

## Two-Block Composition Matrix

Proves `decompressBlocksWF` on a two-block frame yields
`output ++ block1 ++ block2`. A 4×4 matrix over block types (raw, RLE,
compressed-literals/numSeq=0, compressed-sequences/numSeq>0). Enumerated, not
parameterized: the four types are too heterogeneous (raw/RLE pass state through;
comp-literals updates Huffman only; comp-sequences updates Huffman + FSE +
offset history) for a clean generic dependent-type theorem.

Each theorem's proof is always two `rw` calls — a step theorem (non-last block)
plus a single-block theorem (last block); the hard work lives in those, not the
composition:

```lean
rw [decompressBlocksWF_typeA_step ...]    -- block 1 (non-last)
rw [decompressBlocksWF_single_typeB ...]  -- block 2 (last)
```

Prerequisites for a new cell `typeA_then_typeB`: `decompressBlocksWF_typeA_step`
and `decompressBlocksWF_single_typeB`. Compressed-block hypothesis lists run 60+
because of state threading (Huffman `huffTree1`→block2, FSE `fseTables1`, offset
`history1`, window over `output ++ block1`).

### Huffman `if let` dependent-match alpha-equivalence workaround

When block 2 is compressed, `hlit2` references
`(if let some ht := huffTree1 then some ht else prevHuff)`. Lean elaborates this
`if let` as a dependent match capturing `hlit1` as an extra discriminant; the
step theorem's output builds its own match with different bound-variable names,
producing an alpha-equivalence mismatch the kernel rejects. Mandatory fix for
compressed+compressed cells:

1. `subst hpos_eq1` immediately after `obtain` — eliminates `afterHdr1` so
   `hlit1` is never rewritten (no `hlit1'`), keeping the discriminant identity
   consistent.
2. After `rw [step_theorem]`, `cases huffTree1` — fully reduces the `if let`
   match in both goal and `hlit2`, bypassing the mismatch.

```lean
-- DON'T: exact single_block_theorem ... hlit2   -- alpha mismatch
cases huffTree1 <;> exact single_block_theorem ... hlit2
```

Only needed when block 2 is compressed (has `hlit2`); raw/RLE block-2 theorems
lack it. The 4×4 matrix is complete at all three levels (block, frame, API).

### Scaling beyond two blocks: WellFormedBlocks induction

Do NOT start 3-block enumeration (grows as 4^N). Define a `WellFormedBlocks`
inductive predicate (each block parses; non-last have `lastBlock = false`; final
has `lastBlock = true`), parameterized by block *type* at each step (not
content), carrying state threading in its hypotheses. Prove `decompressBlocksWF`
succeeds on any `WellFormedBlocks` input by induction: base case `lastBlock=true`
(single-block-succeeds theorems), step `lastBlock=false` (step theorems + IH).
See `lean-content-preservation` skill.

## Content Pipeline: Block → Frame → API Lifting

Three layers; highly mechanical.

- **Block** (`decompressBlocksWF_*`, in `Zip/Spec/Zstd.lean`): hardest — WF
  unfolding, state threading, block-type decompression.
- **Frame** (`decompressFrame_*_content`, in `Zip/Spec/Zstd.lean`): proof is
  (1) establish position bound, (2) invoke the block-level theorem as `hblocks`,
  (3) `frame_from_blocks`.
- **API** (`decompressZstd_*_content`, in `Zip/Spec/ZstdFrame.lean`): apply the
  frame-level theorem, then `decompressZstd_single_standard_frame_content`
  (finishing with `ByteArray.empty_append`).

### `frame_from_blocks` macro

A ~19-line `local macro` near the top of `Zstd.lean`, used by ~20 frame-level
theorems. Assumes context has `hframe` (frame result), `hh` (frame header parse),
`hblocks` (block-level result). Mechanically handles the `decompressFrame` →
`decompressBlocks` → `decompressBlocksWF` unfolding chain:

```lean
local macro "frame_from_blocks" : tactic =>
  `(tactic| (
    unfold Zip.Native.decompressFrame at hframe
    dsimp only [Bind.bind, Except.bind] at hframe
    rw [hh] at hframe                              -- frame header
    simp only [pure, Except.pure] at hframe
    split at hframe                                 -- dictionary check
    · split at hframe                               -- window size check
      · exact nomatch hframe
      · unfold Zip.Native.decompressBlocks at hframe
        rw [hblocks] at hframe                      -- block-level result
        simp only [ByteArray.empty_append] at hframe
        grind
    · unfold Zip.Native.decompressBlocks at hframe
      rw [hblocks] at hframe
      simp only [ByteArray.empty_append] at hframe
      grind))
```

### File organization (both files past 1000 lines, chronic merge conflicts)

| Layer | File | Size |
|-------|------|------|
| Block + Frame | `Zip/Spec/Zstd.lean` | ~6280 lines (needs split into block / frame / composition) |
| API | `Zip/Spec/ZstdFrame.lean` | ~2600 lines (separate API-succeeds from content) |

## Anti-Patterns

- Don't restate the implementation (`f x = fImpl x`); predicates express
  bounds/invariants/structure independent of implementation.
- Don't skip `Decidable` instances — concrete examples need `decide`.
- Don't attempt loop proofs in a spec-creation session; the predicate + stated
  theorem is the deliverable.
- Don't omit the module `/-! ... -/` docstring (RFC section, layers, predicates).
- Don't validate statements by proof attempts alone — `#eval`/`decide` first.

## Cross-References

- WF recursion (unfolding, `f.induct`, termination, Non-Advancement Guard):
  `lean-wf-recursion`
- Monadic unfolding (`Except.bind` chains, `nomatch`), Bool↔Prop bridging:
  `lean-monad-proofs`
- Array-literal indexing, `1 <<< n`/`2^n`, dagger lemmas (`UInt32.reduceBEq✝` →
  `decide`): `lean-simp-tactics`
- Content preservation (`_getElem_lt`, `_prefix`): `lean-content-preservation`
- Proof cleanup (bare-simp conversion, helper extraction): `proof-review-checklist`
