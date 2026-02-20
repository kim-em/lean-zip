# Current Plan

<!-- Rewritten at the start of each work session. -->
<!-- If a session ends with unchecked items, the next session continues here. -->

## Status: In progress

## Session type: implementation

## Goal: Connect Huffman proofs to IsPrefixFree + ValidLengths for fixed codes

### Deliverables

- [ ] `allCodes_prefix_free`: Prove the codewords from `allCodes` form a
  prefix-free list when `ValidLengths` holds. Bridges `canonical_prefix_free`
  (pairwise on symbols) to `IsPrefixFree` (on the `allCodes` output list).
- [ ] `allCodes_nodup`: Distinct positions in `allCodes` correspond to distinct
  symbols (needed by `allCodes_prefix_free`).
- [ ] `fixedLitLengths_valid`: Prove `ValidLengths fixedLitLengths 15` (concrete
  computation — the fixed literal/length Kraft sum = 2^15 exactly).
- [ ] `fixedDistLengths_valid`: Prove `ValidLengths fixedDistLengths 5` (concrete
  computation — 32 codes of length 5).

### Approach

`allCodes_prefix_free` needs a helper showing that `allCodes` maps distinct
list positions to distinct symbols. Since `filterMap` preserves order and
`codeFor` produces at most one codeword per symbol, different positions in
the output correspond to different symbols. Then `canonical_prefix_free`
gives the prefix-free property.

For `fixedLitLengths_valid` and `fixedDistLengths_valid`: these are decidable
propositions on concrete data. Try `decide` first, fall back to `decide_cbv`
or manual unfolding if `decide` is too slow.
