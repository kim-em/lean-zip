---
name: lean-content-preservation
description: Use when proving that Lean 4 functions preserve existing bytes (prefix/content preservation), compose getElem_lt proofs through recursive structures, prove append-only buffer invariants, or characterize what new bytes a function produces (raw extract, RLE all-equal, element-wise correspondence).
allowed-tools: Read, Bash, Grep
---

# Content Preservation Proof Patterns

Patterns for proving that buffer-modifying functions preserve existing content
(prefix preservation / append-only invariants). Distilled from the Zstd
`copyBytes`, `copyMatch`, `executeSequences`, `decompressBlocksWF`, and
`decompressFrame` proof chains.

## The Three-Theorem Pattern for Buffer Operations

Every buffer-modifying function needs three theorems (in this order):

| Theorem | Suffix | States |
|---------|--------|--------|
| Size | `_size` | `(f buf ...).size = buf.size + k` |
| Preservation | `_getElem_lt` | `i < buf.size -> (f buf ...)[i]! = buf[i]!` |
| Content | `_getElem_ge` | `j >= buf.size -> (f buf ...)[j]! = expected` |

**Prove in this order**: size feeds preservation (need `i < (f buf).size` for
recursive calls), preservation feeds content (need prior bytes stable).

### Size theorem pattern

```lean
theorem copyBytes_size (dst src : ByteArray) (srcPos count : Nat) :
    (copyBytes dst src srcPos count).size = dst.size + count := by
  induction count generalizing dst srcPos with
  | zero => simp only [copyBytes, ↓reduceIte]
  | succ n ih =>
    rw [copyBytes.eq_1]
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    rw [ih, ByteArray.size_push]; omega
```

### Preservation theorem pattern (`_getElem_lt`)

The key theorem: for `i < buf.size`, the byte at index `i` is unchanged.

```lean
theorem copyBytes_getElem_lt (dst src : ByteArray) (srcPos count : Nat)
    (i : Nat) (hi : i < dst.size) :
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

**Key building blocks**:
- `ByteArray.push_getElem!_lt`: `i < ba.size -> (ba.push b)[i]! = ba[i]!`
- `ByteArray.push_getElem!_eq`: `(ba.push b)[ba.size]! = b`
- `ByteArray.size_push`: `(ba.push b).size = ba.size + 1`

### Lifting through `loop` helpers

When the function delegates to a `loop` with an extra counter `k`:

1. Prove `_loop_getElem_lt` with the counter as an extra parameter
2. Derive the public theorem by instantiating `k = 0`

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

theorem copyMatch_getElem_lt (buf : ByteArray) (offset length : Nat) (i : Nat)
    (hi : i < buf.size) :
    (copyMatch buf offset length)[i]! = buf[i]! :=
  copyMatch_loop_getElem_lt _ _ _ buf 0 (Nat.zero_le _) i hi
```

## Composing Preservation Through Sequences

When a function applies multiple buffer operations in sequence (e.g.,
`copyBytes` then `copyMatch`), compose their `_getElem_lt` theorems using
transitivity:

```lean
-- After copyBytes: i < output.size -> (copyBytes output ...)[i]! = output[i]!
-- After copyMatch: i < cb.size -> (copyMatch cb ...)[i]! = cb[i]!
-- Need: i < output.size -> (copyMatch (copyBytes output ...) ...)[i]! = output[i]!

have hcb_size := copyBytes_size output literals litPos seq.literalLength
have hi_cb : i < (copyBytes output literals litPos seq.literalLength).size := by
  rw [hcb_size]; omega
exact (copyMatch_getElem_lt _ _ _ _ hi_cb)
  |>.trans (copyBytes_getElem_lt _ _ _ _ _ hi)
```

**Pattern**: Chain `.trans` from outermost operation back to innermost:
```
outermost_getElem_lt.trans middle_getElem_lt.trans innermost_getElem_lt
```

Each step needs a size proof that `i` is within the intermediate buffer's
bounds. Use the `_size` theorem to derive these bounds.

## Recursive Structure Preservation

For WF-recursive functions like `executeSequences.loop` or
`decompressBlocksWF`, preservation follows the recursion structure:

### List induction pattern (executeSequences.loop)

```lean
theorem executeSequences_loop_getElem_lt
    (seqs : List ZstdSequence) ...
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
    -- peel off error branches with split/nomatch
    split at h; · exact nomatch h
    ...
    -- In the recursive case, compose:
    exact ih _ _ _ h (by rw [copyMatch_size, copyBytes_size]; omega)
      |>.trans (copyMatch_getElem_lt _ _ _ _ hi_cb)
      |>.trans (copyBytes_getElem_lt _ _ _ _ _ hi)
```

### WF recursion pattern (decompressBlocksWF)

```lean
theorem decompressBlocksWF_prefix ...
    (h : decompressBlocksWF data off ... output ... = .ok (result, pos'))
    (i : Nat) (hi : i < output.size) :
    result[i]! = output[i]! := by
  unfold decompressBlocksWF at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  -- Peel error branches
  split at h; next => exact nomatch h
  ...
  -- For each block type (raw/rle/compressed):
  split at h  -- lastBlock check
  · -- Last block: result = output ++ blockContent
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
    exact getElem!_ba_append_left _ _ _ hi
  · -- Not last: recurse
    split at h; next => exact nomatch h  -- position guard
    have ih := decompressBlocksWF_prefix _ _ _ _ _ _ _ _ _ h i
      (by simp only [ByteArray.size_append]; omega)
    rw [ih, getElem!_ba_append_left _ _ _ hi]
  termination_by data.size - off
  decreasing_by all_goals omega
```

**Key insight for last-block vs recursive cases**:
- **Last block**: `result = output ++ blockContent`, use `getElem!_ba_append_left`
- **Recursive case**: invoke `ih` with adjusted size bound
  (`ByteArray.size_append` + `omega`), then chain with `getElem!_ba_append_left`

## Helper Lemmas

### `getElem!_ba_append_left`

The fundamental lemma for ByteArray append preservation:
```lean
theorem getElem!_ba_append_left (a b : ByteArray) (i : Nat) (hi : i < a.size) :
    (a ++ b)[i]! = a[i]!
```

If this doesn't exist yet, prove it via `ByteArray.getElem_append_left`.

### `ByteArray.push_getElem!_lt` / `ByteArray.push_getElem!_eq`

For single-byte operations:
```lean
-- Existing byte unchanged
theorem ByteArray.push_getElem!_lt (ba : ByteArray) (b : UInt8) (i : Nat)
    (hi : i < ba.size) : (ba.push b)[i]! = ba[i]!

-- New byte at the end
theorem ByteArray.push_getElem!_eq (ba : ByteArray) (b : UInt8) :
    (ba.push b)[ba.size]! = b
```

## Common Proof Obligations

When the recursive call operates on `output ++ blockContent`, the size
bound obligation is:
```
i < (output ++ blockContent).size
```
Close with: `by simp only [ByteArray.size_append]; omega`

When composing through `copyBytes` then `copyMatch`:
```
i < (copyBytes output ...).size
```
Close with: `by rw [copyBytes_size]; omega`

## Anti-Patterns

- **Don't unfold the buffer operation**: Use `_getElem_lt` compositionally
  rather than re-proving preservation from scratch at each call site.

- **Don't forget the size obligation**: Each `_getElem_lt` application
  requires `i < intermediate.size`. Always provide this explicitly.

- **Don't chain in the wrong order**: `.trans` chains from outermost to
  innermost. `(copyMatch_getElem_lt ...).trans (copyBytes_getElem_lt ...)`
  means "copyMatch preserves what copyBytes produced", which requires
  that the copyMatch index bound is for the copyBytes output size.

## Content Characterization Patterns

Content preservation (above) proves existing bytes are unchanged. Content
characterization proves what the NEW bytes actually ARE. These are
complementary: preservation says "didn't break old data", characterization
says "new data is correct".

Distilled from PRs #952 (parseLiteralsSection content) and #955
(decompressBlocksWF single-block content).

### Pattern 1: Raw Data — Extract Slice

When a function copies a contiguous byte range from input to output,
characterize the output as `data.extract`:

```lean
theorem parseLiteralsSection_raw_eq_extract (data : ByteArray) (pos : Nat)
    (prevHuffTree : Option ZstdHuffmanTable)
    (literals : ByteArray) (pos' : Nat) (huffTable : Option ZstdHuffmanTable)
    (hlit : (data[pos]! &&& 3).toNat = 0)
    (h : parseLiteralsSection data pos prevHuffTree = .ok (literals, pos', huffTable)) :
    ∃ afterHeader, afterHeader > pos ∧ afterHeader ≤ pos' ∧
      literals = data.extract afterHeader pos'
```

**Key technique**: Use existential quantification over the intermediate
position (header end), then prove `literals = data.extract ...`.
The existential avoids committing to a specific header-size formula
in the theorem statement.

**Proof structure**: Unfold the function, case-split on header format,
extract the `ByteArray.extract` call from the success path, use
`ByteArray.extract_eq_extract` or `rfl` when the output is directly
the extract result.

### Pattern 2: RLE — All-Equal Property

When a function produces repeated copies of one byte, characterize
via universal quantification over indices:

```lean
theorem parseLiteralsSection_rle_all_eq (data : ByteArray) (pos : Nat)
    ...
    (hlit : (data[pos]! &&& 3).toNat = 1)
    (h : parseLiteralsSection data pos prevHuffTree = .ok (literals, pos', huffTable))
    (i j : Nat) (hi : i < literals.size) (hj : j < literals.size) :
    literals[i] = literals[j]
```

**Why this form**: `∀ i j, literals[i] = literals[j]` is more mathematical
than referencing `Array.replicate`. It's implementation-independent — whether
the function uses `replicate`, a loop, or any other mechanism, the spec
captures the same property.

**Proof technique**: Reduce to `ByteArray.getElem_eq_getElem_data` then
`Array.getElem_replicate`. Both indices resolve to the same replicated
value.

### Pattern 3: Raw Block — Element-Wise Input Mapping

When a function copies input bytes verbatim to output, characterize the
per-element correspondence:

```lean
theorem decompressRawBlock_content (data : ByteArray) (pos : Nat)
    (blockSize : UInt32) (result : ByteArray) (pos' : Nat)
    (h : decompressRawBlock data pos blockSize = .ok (result, pos'))
    (i : Nat) (hi : i < result.size) :
    result[i] = data[pos + i]'(...)
```

**Key technique**: The bound proof for `data[pos + i]` derives from
the size theorem (`result.size = blockSize.toNat`) and the position
theorem (`pos' = pos + blockSize.toNat`), combined with the guard
negation (parser checked `pos + blockSize ≤ data.size`).

**Proof building block**: `ByteArray.getElem_extract` — reduces
`(data.extract a b)[i]` to `data[a + i]`.

### Pattern 4: RLE Block — Constant Byte Value

When a function repeats a single byte, characterize each element:

```lean
theorem decompressRLEBlock_content (data : ByteArray) (pos : Nat)
    (blockSize : UInt32) (result : ByteArray) (pos' : Nat)
    (h : decompressRLEBlock data pos blockSize = .ok (result, pos'))
    (i : Nat) (hi : i < result.size) :
    result[i] = data[pos]!
```

**Proof building block**: `Array.getElem_replicate` — reduces
`(Array.replicate n v)[i]` to `v`.

### Composing Content Through Multi-Block Operations

Single-block content theorems compose into multi-block theorems via
case analysis on block type:

```lean
theorem decompressBlocksWF_single_raw_content ...
    (htype : blockType = .raw) ...
    (i : Nat) (hi : i < result.size) :
    result[i] = data[dataOffset + i]'(...) := by
  -- 1. Prove it's a single block (isLastBlock = true)
  -- 2. Reduce to: result = output ++ rawBlockContent
  -- 3. For i < output.size: use preservation (getElem!_ba_append_left)
  -- 4. For i ≥ output.size: use decompressRawBlock_content
```

**Pattern**: Case-split on whether `i` falls in the preserved prefix
(use `_getElem_lt` / `getElem!_ba_append_left`) or the new content
(use the block-specific content theorem). The size theorem determines
the boundary.

### Hierarchy: Size → Preservation → Characterization

Always prove in this order for each function:
1. **`_size`**: How big is the output?
2. **`_getElem_lt`** (preservation): Are existing bytes unchanged?
3. **`_content`** or **`_getElem_ge`** (characterization): What are the new bytes?

Each level depends on the previous: characterization proofs need size
bounds, and often need preservation to handle the recursive/compositional
case.

## Cross-References

- **Size theorems**: `lean-zstd-spec-pattern` skill, "Size and Content
  Theorems for WF Helper Functions"
- **WF recursion unfolding**: `lean-wf-recursion` skill
- **`nomatch` for error branches**: `lean-monad-proofs` skill
- **ByteArray indexing**: `lean-array-list` skill
