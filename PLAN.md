# Current Plan

<!-- Rewritten at the start of each work session. -->
<!-- If a session ends with unchecked items, the next session continues here. -->

## Status: In progress

## Session type: review

## Goal: Deep review of Huffman.lean proofs + documentation accuracy

### Focus 1: Refactoring and proof improvement (Huffman.lean)

- [ ] Review all proofs for minimality — can steps be combined?
- [ ] Look for `grind` opportunities (esp. equational goals)
- [ ] Check if `array_set_ne_zero`, `array_set_ne`, `array_set_self`,
      `array_set_size` can use standard `Array` lemmas from Lean 4.29
- [ ] Can `kraftSumFrom_incr` termination proof be simplified?
- [ ] Can `ncRec_kraft_conservation` induction step be tighter?
- [ ] Are there generally useful lemmas to extract to ZipForStd/?

### Focus 2: Documentation accuracy

- [ ] Fix ARCHITECTURE.md Huffman description (still says "WIP")
- [ ] Verify CLAUDE.md "Current State Summary" is accurate
- [ ] Check all file-level docstrings match current content

### Focus 3: Slop detection

- [ ] Check for unused imports across Spec/ files
- [ ] Look for verbose/redundant comments
- [ ] Check if `IsPrefixFree`, `readBitsMSB`, `finalize`, `decodeBytes`
      still have future use justification

### Focus 4: Codex review (deferred from last session)

- [ ] Run /second-opinion on the Huffman proofs
