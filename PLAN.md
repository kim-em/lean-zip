# Current Plan

<!-- Rewritten at the start of each work session. -->
<!-- If a session ends with unchecked items, the next session continues here. -->

## Status: In progress

## Session type: review

## Goal: Deep review of recent proofs (InflateCorrect.lean, ZipForStd/Nat.lean)

### Focus areas

1. **Refactoring and proof improvement** (InflateCorrect.lean, deep)
   - Can `decode_go_decodeBits` branches be consolidated?
   - Can `readBits_go_spec` inductive step be simplified?
   - Are helper lemmas minimal? Can any be replaced by stdlib?
   - Check for dead code or unused hypotheses

2. **ZipForStd/Nat.lean review**
   - Is `or_two_pow_eq_add` proof minimal?
   - Are there simpler approaches using newer stdlib lemmas?
   - Any other Nat lemmas that should be added for upcoming proofs?

3. **Lean idioms scan** (Spec/ files, quick)
   - Check for `grind` opportunities in new proofs
   - Check for redundant imports
   - Any `!` indexing that could use proven bounds?

### Steps

- [ ] Deep review InflateCorrect.lean proofs — attempt simplifications
- [ ] Review ZipForStd/Nat.lean — check for simpler proof
- [ ] Quick idioms scan across Spec/ files
- [ ] Build + test
- [ ] /second-opinion on changes
- [ ] Document in PROGRESS.md and SESSION.md
