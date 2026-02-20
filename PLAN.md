# Current Plan

<!-- Rewritten at the start of each work session. -->
<!-- If a session ends with unchecked items, the next session continues here. -->

## Status: Complete

## Session type: review

## Goal: Deep review of Spec/Deflate.lean + Lean idioms across codebase

### Focus areas

1. **Refactoring and proof improvement** — deep review of `Zip/Spec/Deflate.lean`
2. **Lean idioms** — `grind` opportunities, proven bounds, newer APIs

### Deliverables

- [x] Verify Deflate spec correctness against RFC 1951 (all block types,
  table values, bit orderings, dynamic Huffman decoding)
- [x] Add `bytesToBits_length` theorem (foundation for Phase 3 proofs)
- [x] Add `readBitsLSB_some_length` theorem (remaining bits get shorter)
- [x] Test `decide_cbv` as alternative to `decide` with `maxRecDepth 2048`
  for `fixedLitLengths_valid` — does not exist in v4.29.0-rc1
- [x] Test `grind` on existing proofs — no improvements over existing tactics
- [x] Scan for `!` accesses in spec code — invasive to convert in Huffman.lean
- [x] Slop detection: dead code, unused imports, verbose patterns — docstring fix
- [x] Documentation: docstring accuracy verified and fixed

### Future work (from Codex review)

- Consider `data.data.toList`/`data.toList` interop lemma in ZipForStd
- Consider `flatMap_length_const` helper if more length proofs arise
