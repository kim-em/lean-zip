# Progress: Multi-frame composition redo

- **Date**: 2026-03-08 UTC
- **Session**: 6626fe38 (feature)
- **Issue**: #898 (Fix: redo PR #893 multi-frame composition on current master)

## Accomplished

- Closed PR #893 (had merge conflicts from #887 prefix/empty and #892 bare simp cleanup)
- Re-implemented both theorems from #889 on clean master:
  - `decompressZstdWF_standard_then_standard`: two consecutive standard frames produce concatenated output at WF-level
  - `decompressZstd_two_frames`: API-level two-frame theorem
- Created replacement PR #901

## Quality metrics

- Sorry count: 4 (unchanged, all XxHash UInt64)
- Tests: all pass, 48/48 conformance
- No `native_decide`, no bare `simp`

## Decisions

- Re-implemented from scratch rather than rebasing — the semantic conflicts (prefix/empty theorems + bare simp cleanup) made 3-way merge error-prone
- The WF theorem reuses `decompressZstdWF_single_standard_frame` for the second frame, keeping the proof compositional
- The API theorem follows the exact pattern of `decompressZstd_single_frame`, extracting parseFrameHeader success for both frames

## Remaining

- Issue #889 should also be closable once PR #901 merges (it specifies the same deliverables)
