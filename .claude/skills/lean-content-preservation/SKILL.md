---
name: lean-content-preservation
description: Use when proving that Lean 4 functions preserve existing bytes (prefix/content preservation), compose getElem_lt proofs through recursive structures, or prove append-only buffer invariants.
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

## Cross-References

- **Size theorems**: `lean-zstd-spec-pattern` skill, "Size and Content
  Theorems for WF Helper Functions"
- **WF recursion unfolding**: `lean-wf-recursion` skill
- **`nomatch` for error branches**: `lean-monad-proofs` skill
- **ByteArray indexing**: `lean-array-list` skill
