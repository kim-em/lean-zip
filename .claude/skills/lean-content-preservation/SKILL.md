---
name: lean-content-preservation
description: Use when proving that Lean 4 functions preserve existing bytes (prefix/content preservation), compose getElem_lt proofs through recursive structures, prove append-only buffer invariants, or characterize what new bytes a function produces (raw extract, RLE all-equal, element-wise correspondence).
allowed-tools: Read, Bash, Grep
---

# Content Preservation Proof Patterns

Proving buffer-modifying functions preserve existing content (append-only / prefix
invariants), and characterizing the new bytes they produce.

## Three-theorem pattern for buffer operations

Every buffer-modifying function gets three theorems, proved in this order
(each feeds the next):

| Theorem | Suffix | States |
|---------|--------|--------|
| Size | `_size` | `(f buf ...).size = buf.size + k` |
| Preservation | `_getElem_lt` | `i < buf.size → (f buf ...)[i]! = buf[i]!` |
| Content | `_getElem_ge` / `_content` | `j ≥ buf.size → (f buf ...)[j]! = expected` |

Size feeds preservation (recursive calls need `i < (f buf).size`); preservation
feeds content (need prior bytes stable).

### Size and preservation (induction on count)

```lean
theorem copyBytes_size (dst src : ByteArray) (srcPos count : Nat) :
    (copyBytes dst src srcPos count).size = dst.size + count := by
  induction count generalizing dst srcPos with
  | zero => simp only [copyBytes, ↓reduceIte]
  | succ n ih =>
    rw [copyBytes.eq_1]
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    rw [ih, ByteArray.size_push]; omega

theorem copyBytes_getElem_lt (dst src : ByteArray) (srcPos count i : Nat)
    (hi : i < dst.size) :
    (copyBytes dst src srcPos count)[i]! = dst[i]! := by
  induction count generalizing dst srcPos with
  | zero => simp only [copyBytes, ↓reduceIte]
  | succ n ih =>
    rw [copyBytes.eq_1]
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    rw [ih (dst.push src[srcPos]!) (srcPos + 1)
      (by simp only [ByteArray.size_push]; omega)]
    exact ByteArray.push_getElem!_lt dst src[srcPos]! i hi
```

Single-byte building blocks:
- `ByteArray.push_getElem!_lt`: `i < ba.size → (ba.push b)[i]! = ba[i]!`
- `ByteArray.push_getElem!_eq`: `(ba.push b)[ba.size]! = b`
- `ByteArray.size_push`: `(ba.push b).size = ba.size + 1`

### Lifting through a `loop` helper with an extra counter

Prove `_loop_getElem_lt` with the counter `k` as a parameter, then instantiate
`k = 0` for the public theorem.

```lean
private theorem copyMatch_loop_getElem_lt (offset length start : Nat)
    (b : ByteArray) (k : Nat) (_hk : k ≤ length) (i : Nat) (hi : i < b.size) :
    (copyMatch.loop offset length start b k)[i]! = b[i]! := by
  rw [copyMatch.loop.eq_1]
  split
  · rw [copyMatch_loop_getElem_lt _ _ _ _ (k + 1) (by omega) i
      (by simp only [ByteArray.size_push]; omega)]
    exact ByteArray.push_getElem!_lt b _ i hi
  · rfl
  termination_by length - k

theorem copyMatch_getElem_lt (buf : ByteArray) (offset length i : Nat)
    (hi : i < buf.size) :
    (copyMatch buf offset length)[i]! = buf[i]! :=
  copyMatch_loop_getElem_lt _ _ _ buf 0 (Nat.zero_le _) i hi
```

## Composing preservation through a sequence of operations

Chain `_getElem_lt` theorems with `.trans`, outermost back to innermost. Each
step needs an `i < intermediate.size` bound, derived from the `_size` theorem.

```lean
have hcb_size := copyBytes_size output literals litPos seq.literalLength
have hi_cb : i < (copyBytes output literals litPos seq.literalLength).size := by
  rw [hcb_size]; omega
exact (copyMatch_getElem_lt _ _ _ _ hi_cb)
  |>.trans (copyBytes_getElem_lt _ _ _ _ _ hi)
```

`(copyMatch_getElem_lt ...).trans (copyBytes_getElem_lt ...)` reads "copyMatch
preserves what copyBytes produced" — so the copyMatch bound is for the copyBytes
output size. Wrong-order chaining will not typecheck.

## Recursive structure preservation

### List induction (executeSequences.loop)

```lean
theorem executeSequences_loop_getElem_lt (seqs : List ZstdSequence) ...
    (h : executeSequences.loop seqs ... = .ok result)
    (i : Nat) (hi : i < output.size) :
    result.1[i]! = output[i]! := by
  induction seqs generalizing output history litPos with
  | nil =>
    rw [executeSequences.loop.eq_1] at h
    simp only [Except.ok.injEq] at h
    obtain ⟨rfl, _, _⟩ := h; rfl
  | cons seq rest ih =>
    rw [executeSequences.loop.eq_2] at h
    split at h; · exact nomatch h   -- peel error branches with split/nomatch
    ...
    exact ih _ _ _ h (by rw [copyMatch_size, copyBytes_size]; omega)
      |>.trans (copyMatch_getElem_lt _ _ _ _ hi_cb)
      |>.trans (copyBytes_getElem_lt _ _ _ _ _ hi)
```

### WF recursion (decompressBlocksWF)

```lean
theorem decompressBlocksWF_prefix ...
    (h : decompressBlocksWF data off ... output ... = .ok (result, pos'))
    (i : Nat) (hi : i < output.size) :
    result[i]! = output[i]! := by
  unfold decompressBlocksWF at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h; next => exact nomatch h   -- peel error branches
  ...
  split at h   -- lastBlock check
  · -- last block: result = output ++ blockContent
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
    exact getElem!_ba_append_left _ _ _ hi
  · -- not last: recurse
    split at h; next => exact nomatch h   -- position guard
    have ih := decompressBlocksWF_prefix _ _ _ _ _ _ _ _ _ h i
      (by simp only [ByteArray.size_append]; omega)
    rw [ih, getElem!_ba_append_left _ _ _ hi]
  termination_by data.size - off
  decreasing_by all_goals omega
```

Last-block case: `result = output ++ blockContent`, use `getElem!_ba_append_left`.
Recursive case: invoke `ih` with the adjusted size bound
(`by simp only [ByteArray.size_append]; omega`), then chain with
`getElem!_ba_append_left`.

## Helper lemmas

```lean
theorem getElem!_ba_append_left (a b : ByteArray) (i : Nat) (hi : i < a.size) :
    (a ++ b)[i]! = a[i]!   -- prove via ByteArray.getElem_append_left if absent
```

Size-bound obligations:
- `i < (output ++ blockContent).size` → `by simp only [ByteArray.size_append]; omega`
- `i < (copyBytes output ...).size` → `by rw [copyBytes_size]; omega`

## Content characterization

Preservation says old bytes are unchanged; characterization says what the new
bytes ARE. Prefer implementation-independent statements.

### Raw data — extract slice

Function copies a contiguous input range to output. Existentially quantify the
header end to avoid baking a header-size formula into the statement.

```lean
theorem parseLiteralsSection_raw_eq_extract ...
    (hlit : (data[pos]! &&& 3).toNat = 0)
    (h : parseLiteralsSection data pos prevHuffTree = .ok (literals, pos', huffTable)) :
    ∃ afterHeader, afterHeader > pos ∧ afterHeader ≤ pos' ∧
      literals = data.extract afterHeader pos'
```

Building block: `ByteArray.getElem_extract` reduces `(data.extract a b)[i]` to
`data[a + i]`.

### RLE — all-equal property

Function produces repeated copies of one byte. State it as `∀ i j, x[i] = x[j]`
rather than referencing `Array.replicate`.

```lean
theorem parseLiteralsSection_rle_all_eq ...
    (hlit : (data[pos]! &&& 3).toNat = 1)
    (h : parseLiteralsSection data pos prevHuffTree = .ok (literals, pos', huffTable))
    (i j : Nat) (hi : i < literals.size) (hj : j < literals.size) :
    literals[i] = literals[j]
```

Technique: reduce via `ByteArray.getElem_eq_getElem_data` then
`Array.getElem_replicate`; both indices resolve to the same value.

### Element-wise input mapping (raw block)

```lean
theorem decompressRawBlock_content ...
    (h : decompressRawBlock data pos blockSize = .ok (result, pos'))
    (i : Nat) (hi : i < result.size) :
    result[i] = data[pos + i]'(...)
```

The `data[pos + i]` bound derives from `result.size = blockSize.toNat`,
`pos' = pos + blockSize.toNat`, and the parser guard `pos + blockSize ≤ data.size`.

### Constant byte value (RLE block)

```lean
theorem decompressRLEBlock_content ...
    (h : decompressRLEBlock data pos blockSize = .ok (result, pos'))
    (i : Nat) (hi : i < result.size) :
    result[i] = data[pos]!   -- via Array.getElem_replicate
```

### Composing content through multi-block operations

Case-split on whether `i` is in the preserved prefix
(use `_getElem_lt` / `getElem!_ba_append_left`) or in the new content (use the
block-specific content theorem). The `_size` theorem sets the boundary.

```lean
theorem decompressBlocksWF_single_raw_content ... :
    result[i] = data[dataOffset + i]'(...) := by
  -- 1. show single block (isLastBlock = true)  → result = output ++ rawBlockContent
  -- 2. i < output.size:  getElem!_ba_append_left
  -- 3. i ≥ output.size:  decompressRawBlock_content
```

## N-block content via `decompressBlocksWF.induct`

Two-block theorems use enumeration (`rw [step]; rw [single]`), which is `4^N`
theorems for N blocks. For N-block frames, induct on the WF recursion instead —
one theorem covers all counts.

```lean
theorem decompressBlocksWF_content_general
    (h : decompressBlocksWF data off windowSize output prevHuff prevFse history
           = .ok (result, pos')) :
    ∃ blocks : List ByteArray,
      result = output ++ blocks.foldl (· ++ ·) ByteArray.empty := by
  induction off, output, prevHuff, prevFse, history
    using decompressBlocksWF.induct (data := data) (windowSize := windowSize)
    generalizing result with
  | base hoff => ...                                  -- pos ≥ data.size: no blocks
  | step hoff hparse hbs hws htype hdecomp hnotlast hadv ih => ...  -- one block + recurse
```

The step must thread all mutable state into the next iteration: `output ++ blockContent`
as the new output, plus updated Huffman table, FSE tables, and offset history —
mirroring the function's own recursion. Two-block theorems are instances of this
general result.

## Anti-patterns

- Don't unfold the buffer operation at each call site; use `_getElem_lt`
  compositionally.
- Don't omit the `i < intermediate.size` obligation on each `_getElem_lt` application.
- Don't chain `.trans` inner-to-outer; it must go outermost to innermost.

## Cross-references

- `lean-zstd-spec-pattern`: size theorems, two-block composition template
- `lean-wf-recursion`: WF recursion unfolding
- `lean-monad-proofs`: `nomatch` for error branches
- `lean-array-list`: ByteArray indexing
