---
name: lean-fuel-induction
description: Use when Lean 4 proofs involve fuel-based recursion, proving fuel independence, loop invariants, copyLoop-style patterns, suffix/append extension lemmas, or maxRecDepth/maxHeartbeats tuning.
allowed-tools: Read, Bash, Grep
---

# Lean 4 Fuel Induction and Loop Invariant Patterns

For generic `termination_by` / `decreasing_by` / `f.induct` / single-step
unfolding (`rw [f.eq_1]`) mechanics, see the `lean-wf-recursion` skill. This
file covers the fuel-specific and project-specific patterns.

## Avoid `forIn` on `Range` in Proofs

`for i in [:n]` compiles to `Std.Legacy.Range.forIn'` with a well-founded
`loop✝` that CANNOT be unfolded by name. `with_unfolding_all rfl` only works
for concrete bounds (`[:0]`, `[:1]`), not symbolic `n`. `while` loops are the
same (`Lean.Loop.forIn`'s `loop✝`).

If you must prove a property of such a loop, refactor it to explicit/WF
recursion (see `copyLoop` in `Inflate.lean`). Discover this early — do not
burn iterations trying to unfold `forIn`.

## Fuel Independence

`f x (fuel + 1) = some r → ∀ k, f x (fuel + k) = some r`. Induct on fuel:

1. `conv => lhs; rw [show n+1+k = (n+k)+1 from by omega]` before
   `unfold f at h ⊢`, so both sides unfold at the same successor level.
2. `cases` on each non-recursive operation; `ih` for recursive calls.
3. For `if` in `h`, use `rw [if_pos/if_neg]`, NOT `simp [cond]` — simp strips
   `some`/`pure` wrappers.
4. For `guard` in do-blocks, `by_cases` the condition then
   `simp only [guard, hcond, ↓reduceIte]`. The guard is `Alternative.guard`,
   NOT `Option.guard`.

## copyLoop-Style Loop Invariants

For `copyLoop buf start distance k length`, prove a generalized invariant by WF
induction carrying the full buffer state:
1. State the invariant relating `buf` to the original `output`.
2. Base case `k = length`: `copyLoop` returns `buf`, use hypothesis.
3. Step: `buf.push x` satisfies the invariant for `k+1`.

Key lemmas: `push_getElem_lt` (push preserves earlier elements),
`push_data_toList` (`(buf.push b).data.toList = buf.data.toList ++ [b]`),
`List.ofFn_succ_last` (snoc decomposition of `List.ofFn`).

## Bundled Invariant Lemmas for Stateful Chains

When a chain of operations on a stateful type (e.g. `BitReader`) must preserve
several properties at once, return a single `∧` rather than separate lemmas:

```lean
private theorem op_inv (br br' : BitReader) ...
    (h : op br = .ok (result, br'))
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (hple : br.pos ≤ br.data.size) :
    br'.data = br.data ∧
    (br'.bitOff = 0 ∨ br'.pos < br'.data.size) ∧
    br'.pos ≤ br'.data.size
```

Chain: `have ⟨hd₁, hpos₁, hple₁⟩ := op_inv ...` then
`exact ⟨hd'.trans hd₁, hpos', hple'⟩`. See `GzipCorrect.lean`
(`readBit_inv` … `decode_inv`).

### Threading through long call chains

For `inflateLoop_endPos_le`-style proofs through 5+ sequential ops:

```lean
have ⟨hd₁, hpos₁, hple₁⟩ := readBits_inv br br₁ _ _ h_readBits hpos hple
have ⟨hd₂, hpos₂, hple₂⟩ := decode_inv tree br₁ br₂ _ h_decode hpos₁ hple₁
have ⟨hd₃, hpos₃, hple₃⟩ := readBits_inv br₂ br₃ _ _ h_readBits₂ hpos₂ hple₂
-- compose data equalities right-to-left:
exact ⟨hd_final.trans (hd₃.trans (hd₂.trans hd₁)), hpos_final, hple_final⟩
```

- Each `_inv` takes the previous op's **output** invariants as input.
- Data equalities compose via `.trans` right-to-left.
- For recursive (induction) steps, pass the final state's invariants to `ih`,
  then `.trans` the recursive result with the accumulated chain.

### Multi-path case splits

When a function branches on a decoded symbol (literal / end-of-block /
length-distance), cover every path:

```lean
split at h
· -- literal byte
  have ⟨hd', hp', hl'⟩ := ih br₁ _ h hpos₁ hple₁
  exact ⟨hd'.trans hd₁, hp', hl'⟩
· split at h
  · -- end of block — state unchanged
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    exact ⟨hd₁, hpos₁, hple₁⟩
  · -- length+distance — chain more operations
    exact ⟨hd'.trans (hd₄.trans (hd₃.trans (hd₂.trans hd₁))), hp', hl'⟩
```

Each sub-op's error path closes via `simp [h_op] at h` (`.error = .ok`
contradiction).

## Suffix/Append vs Fuel-Independence Proofs

The two differ in how `simp only` interacts with hypothesis and goal:

- **Fuel-independence**: `simp only [hds] at h ⊢` processes both at once (same
  call in `h` and `⊢`).
- **Suffix/append**: `h` has `f bits`, `⊢` has `f (bits ++ suffix)` —
  `simp only [hds]` won't match the goal.

Suffix/append pattern:
1. `simp only [hds, bind, Option.bind] at h` — process hypothesis.
2. `rw [f_append ...]` — transform the goal.
3. `simp only [bind, Option.bind]` — reduce `Option.bind (some _) (fun _ => _)`.

For `if` on both sides: `by_cases hcond : condition` then
`rw [if_pos/if_neg hcond] at h ⊢`. Note: `split at h ⊢` (multiple targets) is
NOT supported — use `by_cases`.

### Except suffix invariance: avoid spurious simp/dsimp

In `f (brAppend br suffix) = ... brAppend br' suffix` proofs, two false patterns
waste iterations:
- After `cases hx : pure_func args | ok val =>`: `cases` already reduces the
  goal's `match` for `.ok`. Apply `simp only [hx]` to `h` only, not `⊢`.
- After `rw [if_neg hcond] at h ⊢`: the `if` is fully reduced; a following
  `simp only [pure, Except.pure]` / `dsimp` usually makes no progress.

Rule: start minimal, add `dsimp`/`simp` only when the build shows the goal is
unreduced.

## `termination_by` Proofs vs `Nat.strongRecOn`

When proving about a `termination_by expr` function, prefer giving the theorem
the same `termination_by` + `decreasing_by` and making recursive calls directly:

```lean
private theorem f_property (data : ByteArray) (pos : Nat) (hpos : pos ≤ data.size) :
    P (f data pos) := by
  by_cases h : base_case
  · ...
  · have h_rec := f_property data (pos + step) (by omega)
    ...
  termination_by data.size - pos
  decreasing_by omega
```

`Nat.strongRecOn` introduces an induction variable `n` separate from the measure
`data.size - pos`, which (1) elaborates the full recursive term → `maxRecDepth`
blowups, and (2) leaves `n` instead of the measure in arithmetic goals, forcing
`subst`. Direct `termination_by` keeps the measure concrete.

## `maxRecDepth` / `maxHeartbeats` Tuning

After proofs work, shrink these to the minimum — speeds compilation, catches
stray unfolding.
1. Start at whatever works (e.g. 4096 / 4,000,000).
2. Try halving (2048 / 2,000,000).
3. Table-correspondence lemmas (non-recursive simp chains) often work at 512.
4. Non-recursive proofs often need no `set_option` — remove it entirely first.

By proof type:
- Recursive monadic chain (5+ ops): `maxRecDepth 2048` or `4096`.
- Single unfold + case split: `maxRecDepth 512` or default.
- Pure `simp` / `omega`: none.

## Opaque Loop Catalog and WF-Refactoring Priority (Zip/Native/)

A *generic* `Range.forIn` invariant lemma is impractical: the `forIn` wrapper's
hidden `loop✝` can't be named/unfolded, a generic invariant would parameterize
over monad/body/accumulator, and every loop here has a different state shape.
**Use per-function WF refactoring** for loops needing spec proofs; leave the
rest opaque.

### Priority 1 — needs WF refactoring (blocks sorry proofs)

| Function | File | Loop | Blocking theorem |
|----------|------|------|------------------|
| `buildFseTable` (fill loops) | Fse.lean | 4× `for [:n]` + `while` | `buildFseTable_cells_size` (sorry) |
| `decompressZstd` | ZstdFrame.lean | `while pos < data.size` | top-level decompression specs |

### Priority 2 — would benefit, not urgent

| Function | File | Loop | Notes |
|----------|------|------|-------|
| `decodeSequences` | ZstdSequence.lean | `for [:numSeq]` | interleaved FSE decoding; complex state |
| `xxHash64` (stripe loop) | XxHash.lean | `while pos < stripeEnd` | blocked by UInt64 kernel eval anyway |
| `decodeHuffmanStream` | ZstdHuffman.lean | `for [:count]` | no spec theorems yet |

### Priority 3 — probably leave as-is

| Function | File | Notes |
|----------|------|-------|
| `parseHuffmanWeightsDirect` | ZstdHuffman.lean | simple accumulation, no spec unfold |
| `weightsToMaxBits` | ZstdHuffman.lean | summation — has WF alt `findMaxBitsWF` |
| `buildZstdHuffmanTable` | ZstdHuffman.lean | `tableSize` theorem needs only fill loops |
| `parseHuffmanTreeDescriptor` (trim) | ZstdHuffman.lean | trailing-zero trim, no spec impact |
| `decodeFseSymbols` / `decodeFseSymbolsAll` | Fse.lean | no/no-impact spec theorems |
| `Gzip.decompress` (member loop) | Gzip.lean | bounded `[:1000]`, specs don't unfold it |
| `deflateStored` | Deflate.lean | compression, not spec'd |

### Already WF-friendly

`findMaxBitsWF`, `decompressBlocksWF` (ZstdFrame), `copyBytes` / `copyMatch` /
`executeSequences.loop` (ZstdSequence), `processRemaining8` / `processRemaining1`
(XxHash), `decodeFseLoop` (fuel + equation lemmas + spec), `pushZeros` /
`decodeZeroRepeats` (Fse).

### Effort estimates

- **buildFseTable**: high — 4 loops, different state shapes. Refactor only the
  fill loops `cells_size` needs, not all 4.
- **decompressZstd**: low — simple position-advancing loop; depends on
  `decompressFrame` → `decompressBlocks` (now refactored).
- **decodeSequences**: high — interleaved FSE transitions, 4+ interdependent
  state vars.

## Cross-References

- `lean-wf-recursion` — `termination_by`, `f.induct`, `rw [f.eq_1]` single-step
  unfolding, dependent `if` guards (`dif_pos`/`dif_neg`), fuel-to-WF migration.
- `lean-roundtrip-proofs` — suffix invariance chains (`_append` lemmas), goR
  (decode-with-remaining), accumulator equivalence.
