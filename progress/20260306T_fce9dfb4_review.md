# Progress: ZstdHuffman.lean spec quality audit

- **Date**: 2026-03-06 UTC
- **Session**: fce9dfb4 (review)
- **Issue**: #759

## Accomplished

1. **Replaced 3 `simp_all` with `simp only`**: All three `simp_all [beq_iff_eq]`
   occurrences (lines 212, 232, 432) replaced with `simp only [beq_iff_eq] at *`.
   Straightforward mechanical replacement — all three involved `beq_iff_eq` for
   `BEq.beq x y = true ↔ x = y` conversion followed by `omega`.

2. **Deduplicated monadic bind peeling**: Extracted private helper
   `buildZstdHuffmanTable_ok_elim` that peels through the 7 monadic layers of
   `buildZstdHuffmanTable` once. Both `buildZstdHuffmanTable_tableSize` and
   `buildZstdHuffmanTable_maxBits_pos` are now thin term-mode wrappers.
   Net reduction: 36 lines (615 → 579).

## Quality metrics

- Sorry count: 6 (unchanged: 4 XxHash + 2 Fse)
- `simp_all` in ZstdHuffman.lean: 3 → 0
- File size: 615 → 579 lines
- All 48 conformance tests pass

## Decisions

- Used `constructor` + `rw [← h]` pattern instead of `subst h` for the first
  conjunct of `ok_elim`, because `subst` left struct projections unreduced.
