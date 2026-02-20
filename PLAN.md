# Current Plan

<!-- Rewritten at the start of each work session. -->
<!-- If a session ends with unchecked items, the next session continues here. -->

## Status: In progress

## Session type: implementation

## Goal: resolveLZ77 properties + main correctness theorem

### Deliverables

- [ ] Prove `resolveLZ77` basic properties:
  - `resolveLZ77_nil`: empty symbol list returns accumulator
  - `resolveLZ77_endOfBlock`: endOfBlock returns accumulator
  - `resolveLZ77_literal`: single literal appends byte
  - `resolveLZ77_reference_valid`: valid back-reference copies correctly
- [ ] Prove `resolveLZ77` compositionality:
  - `resolveLZ77_literals_append`: sequence of literals = append
- [ ] State main correctness theorem (can be sorry'd):
  - `inflate_eq_spec_decode`: native inflate agrees with spec decode
- [ ] Final build + test pass

### Context

Phase 3 deliverable: prove DEFLATE decompression correct. This session
builds the LZ77 layer of the correctness proof and states the top-level
theorem to guide future sessions.
