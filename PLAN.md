# Current Plan

<!-- Rewritten at the start of each work session. -->
<!-- If a session ends with unchecked items, the next session continues here. -->

## Status: In progress

## Session type: review

## Focus areas

Deep review of `Zip/Spec/Huffman.lean` (refactoring + proof improvement)
and secondary review of `Zip/Spec/Deflate.lean` (lean idioms + slop).

### Deliverables

- [ ] Try simplifying `kraft_ge_count` calc block with omega
- [ ] Look for cleaner `hpow_pos` proof in `count_le_pow_of_validLengths`
- [ ] Check for other proof simplifications across Huffman.lean
- [ ] Slop detection: unused code, verbose comments, dead imports
- [ ] Check the uncommitted VERIFICATION.md change
- [ ] Review Deflate.Spec for idiom/style issues
- [ ] Update CLAUDE.md if needed

## Failed approaches (for future reference)

- Simple induction on `S(b) ≤ 2^b` fails: IH too weak, doesn't leave room
  for blCount[b+1] in the step case
- `by_contra`, `push_neg`, `set` are Mathlib-only — use `by_cases`/`omega`
- `le_refl` not in scope — use `(by omega)` or `Nat.le.refl`
- `apply ih` with bullets: goal ordering is unpredictable — use `exact ih ... (by ...) ...`
