# Current Plan

## Status: In progress

## Session type: implementation

## Goal: Fix inflateLoop_correct and prove inflate_correct

### Root cause of previous failures

1. `decodeHuffman_correct` uses `∃ specFuel` but `decode.go` calls
   `decodeSymbols` with default fuel 10000000 — simp can't unify
2. Missing `↓reduceIte` in spec-side simp calls

### Steps

1. [ ] Fix `decodeHuffman_correct`: change `∃ specFuel` → use native `fuel`
   - Also add `br'.bitOff = 0 ∨ br'.pos < br'.data.size` to conclusion
   - Mechanical change: replace `sf` with `n`, remove existential
2. [ ] Fix `inflateLoop_correct`:
   - Add `↓reduceIte` to all spec-side simp calls
   - `hds` now has fuel 10000000 matching `decode.go`'s default
   - Fix `hout_eq` direction: use `← hout_eq` where needed
3. [ ] Verify build succeeds
4. [ ] Commit and update docs

### Architecture

```
inflate_correct
  ├── decodeStored_correct (DONE)
  ├── decodeHuffman_correct (DONE — fixing fuel)
  │   ├── huffTree_decode_correct (DONE)
  │   ├── literal/end-of-block/length-distance (DONE)
  │   └── copyLoop_eq_ofFn (DONE)
  ├── decodeDynamicTrees_correct (sorry — separate concern)
  └── inflateLoop_correct (fixing)
      └── fuel matching + ↓reduceIte (current focus)
```
