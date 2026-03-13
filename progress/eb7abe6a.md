# Summarize: Proven-bounds campaign + Zstd splitting (14-PR batch)

- **Date**: 2026-03-13 UTC
- **Session type**: summarize
- **Issue**: #1422

## PRs covered (14 PRs since summarize #1396)

### Track E completeness (3 PRs)
- #1393: API-level `WellFormedBlocks` succeeds (full predicate)
- #1398: Frame-level and API-level `WellFormedSimpleBlocks` succeeds
- #1401: Frame/API-level `WellFormedSimpleBlocks` succeeds (dedup of #1398)

### Proven-bounds campaign (5 PRs)
- #1414: Deflate.lean — encoding helpers + constant tables (22 `]!` → proven)
- #1417: DEFLATE length/distance tables — 4 `]!` in `decodeHuffman.go`
- #1426: ZstdHuffman.lean — 13 data byte reads in `parseCompressedLiteralsHeader`
- #1427: Fix merge conflict for ZstdFrame.lean proven-bounds PR #1413
- #1428: ZstdSequence.lean — data byte reads + history array access

### Zstd splitting (1 PR)
- #1409: Split Zstd.lean — extracted ZstdBase.lean (L1, 542 lines) and
  ZstdBlockLoop.lean (L2, 493 lines) from the 6011-line Spec/Zstd.lean

### Quality reviews (3 PRs)
- #1394: ZstdSequence.lean proof quality audit
- #1397: Zstd.lean file organization — splitting plan
- #1402: Zstd.lean proof quality audit (frame characterization + compressed two-block)

### Infrastructure (2 PRs)
- #1410: Rebase PR #1402 onto master (merge conflict resolution)
- #1420: Meditate — proven-bounds skill creation + Zstd splitting readiness

## Key observations

### Proven-bounds campaign status
The campaign converts `[i]!` runtime bounds checks to proven-bounds `[i]`
access across native implementation files. Current `]!` counts:

| File | Remaining `]!` | Notes |
|------|----------------|-------|
| Deflate.lean | 53 | Largest — many in LZ77 matching loops |
| ZstdSequence.lean | 29 | History array + data byte reads |
| Fse.lean | 18 | Table construction loops |
| ZstdHuffman.lean | 14 | Weight arrays + table fill |
| Gzip.lean | 12 | Header parsing |
| DeflateDynamic.lean | 11 | Huffman code tables + frequency arrays |
| Inflate.lean | 4 | Mostly covered |
| ZstdFrame.lean | 4 | Nearly done |
| BitReader.lean | 3 | Nearly done |
| XxHash.lean | 1 | Nearly done |
| **Total** | **149** | Down from ~200+ pre-campaign |

Files fully converted: Crc32.lean, Adler32.lean, BitWriter.lean

### Zstd spec splitting
Spec/Zstd.lean was split via #1409:
- **ZstdBase.lean** (542 lines): Base predicates, correctness theorems (L1)
- **ZstdBlockLoop.lean** (493 lines): Block loop specs (L2)
- **Zstd.lean** remains at 6011 lines — still 6× the 1000-line limit
- Further splitting planned (issue #1432 — two-block completeness extraction)

### WellFormedBlocks completion
The `WellFormedBlocks`/`WellFormedSimpleBlocks` predicates now have full
frame and API-level succeeds theorems, completing the induction-based
completeness approach for arbitrary block sequences.

## Quality metrics delta

| Metric | Before (#1396) | After | Delta |
|--------|---------------|-------|-------|
| Sorries | 4 | 4 | 0 |
| Merged PRs | ~586 | 600 | +14 |
| Spec files | 49 | 51 | +2 (ZstdBase, ZstdBlockLoop) |
| Zstd spec lines | 15,811 | 16,470 | +659 |
| Zstd spec decls | 501 | 549 | +48 |
| Native `]!` | ~200+ | 149 | reduced |
| Total source files | ~105 | 106 | +1 |
