# Session State

<!-- Overwritten at the end of each work session. -->
<!-- Records current working state for the next session to pick up. -->

## Sorry count: 2

## Incomplete proofs

- `Zip/Spec/Huffman.lean:145` — `codeFor_injective`: canonical code assigns
  distinct codewords to distinct symbols. Needs proof that the canonical
  construction never assigns the same code to different symbols.
- `Zip/Spec/Huffman.lean:155` — `canonical_prefix_free`: canonical code is
  prefix-free. Needs proof that codes of different lengths can't be prefixes
  (shorter codes are numerically smaller in the canonical tree structure).

Both have `ValidLengths` preconditions (all lengths ≤ maxBits, Kraft inequality).

## Known good commit

`c909972` — `lake build && lake exe test` passes

## Next action

Phase 3 is now in progress. Next session options:

1. **Implementation session**: Prove `codeFor_injective` and
   `canonical_prefix_free` — these are the foundational Huffman theory
   proofs. Approach: show that codes of the same length get consecutive
   code values (hence different codewords), and codes of different lengths
   have the shorter one's range disjoint from the longer one's bit patterns.

2. **Implementation session**: Write a conformance test that checks the
   spec decode function against the native inflate implementation on
   actual compressed data. This validates the spec independently of proofs.

3. **Review session**: Review the new spec files for completeness and
   correctness. Check spec vs RFC 1951 more carefully.

4. **Implementation session**: Begin the correctness theorem statement:
   `inflate data = ok output ↔ Deflate.Spec.decodeBytes data = some output.toList`.
   This doesn't require proving it yet — just getting the type right.

## Notes

- Codex review found and we fixed: alignment tracking (simplified to use
  `bits.length % 8`), `decodeStored` error handling, dynamic table overshoot,
  theorem preconditions
- Codex incorrectly flagged Huffman bit ordering as wrong — the double
  reversal (MSB-first packing into LSB-first bytes, then LSB-first reading)
  means the spec's MSB-first codewords correctly match the bit stream
- `readBitsMSB` is currently unused but may be needed for future proofs
- Toolchain v4.29.0-rc1 is current
