# Proven-bounds data access in Deflate.lean — LZ77 data byte reads

**Date**: 2026-03-13
**Session**: b25bb6d6 (feature)
**Issue**: #1423

## Accomplished

Converted 30 `]!` runtime bounds checks to proven-bounds `]` access in the
LZ77 matching functions across 4 variants (lz77Greedy, lz77GreedyIter,
lz77Lazy, lz77LazyIter).

### Patterns converted

| Pattern | Count | Technique |
|---------|-------|-----------|
| hash3 byte reads (pos, pos+1, pos+2) | 9 | auto-param `(_ : pos + 2 < data.size := by omega)` |
| go/countMatch comparison reads | 6 | explicit bounds-check guards `if h1 : p1 + i < data.size` |
| trailing literal reads | 4 | capture `if h : pos < data.size` |
| mainLoop literal fallbacks | 11 | omega from `hlt : pos + 2 < data.size` |

### Proof updates

- **LZ77NativeCorrect.lean**: `go_matches` gained extra `split` cases for
  bounds-check branches, plus `getElem!_pos` bridges for `data[pos]!`↔`data[pos]`.
  `trailing_valid` and `mainLoop_valid` literal cases updated similarly.
- **DeflateFixedCorrect.lean**: `go_eq` gained extra splits; trailing
  emptiness proofs changed from `↓reduceIte` to `↓reduceDIte` (decidable if).
- **DeflateDynamicCorrect.lean**: `if_neg` → `dif_neg` for trailing emptiness.

### Key decisions

- Used auto-param `(by omega)` for hash3's proof parameter to minimize
  proof file changes — callers don't need explicit proof arguments.
- For `go` (countMatch inner loop), used explicit bounds-check guards
  rather than preconditions to avoid threading proofs through callers.
  This slightly changes behavior (graceful fallback instead of panic
  on out-of-bounds) but is functionally identical for correct usage.

## Quality metrics

- `]!` in Deflate.lean: 53 → 23 (−30)
- Sorry count: 4 → 4 (unchanged, all XxHash)
- Build: passes (except pre-existing zstd_ffi.o missing header)
- Tests: could not run (no zstd.h in environment), but all Lean compiles

## What remains

23 `]!` patterns remain in Deflate.lean — these are hash table lookups
(`hashTable[h]!`, `hashValid[h]!`), constant code table lookups
(`fixedLitCodes[...]!`, `fixedDistCodes[...]!`), and `canonicalCodes`
internal lookups. These require different proof techniques (table size
invariants, UInt8 range bounds) and belong in separate issues.
