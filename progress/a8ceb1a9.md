# Session a8ceb1a9 — decompressBlocksWF raw/RLE step theorems

**Issue**: #954
**Branch**: agent/a8ceb1a9
**Status**: Complete

## What was done

Added two step theorems to `Zip/Spec/Zstd.lean`:

- `decompressBlocksWF_raw_step`: when `decompressBlocksWF` encounters a non-last
  raw block, it equals a recursive call with `output ++ block` and the advanced
  position. Huffman table, FSE tables, and offset history are unchanged.

- `decompressBlocksWF_rle_step`: same for RLE blocks.

## Proof technique

The key challenge was unfolding the WF recursive function on only the LHS of an
equality goal. Previous approaches failed:

- `conv_lhs => unfold` — not supported in Lean 4 v4.29.0-rc4
- `Eq.trans` with `unfold` + `simp only` — `?mid` metavariable remained unsynthesized
- Direct `simp only` with guard hypotheses — couldn't handle the nested bind/ite chain

The working approach uses `generalize` to hide the RHS:
```lean
generalize heq : f afterBlock ... = rhs
unfold f
simp only [hoff, ↓reduceDIte, hparse, hbs, hws, htype, hraw, hnotlast, hadv,
  bind, Except.bind, pure, Except.pure, ↓reduceIte, Bool.false_eq_true]
exact heq
```

`generalize` makes the RHS opaque, so `unfold` only targets the LHS. After simp
reduces all guard conditions and monadic binds, the goal becomes `f afterBlock ... = rhs`,
which `exact heq` closes.

## Quality

- sorry count: 4 (unchanged, all in XxHash)
- All tests pass
- Clean build with no warnings
