# Progress: Review — Zstd.lean spec quality audit

- **Date**: 2026-03-06 UTC
- **Session**: fce9dfb4 (review)
- **Issue**: #767

## Accomplished

### Deliverable 1: Deduplicate parseFrameHeader position proofs
- Reordered `parseFrameHeader_pos_ge_five` before `parseFrameHeader_pos_gt`
- Derived `parseFrameHeader_pos_gt` from `parseFrameHeader_pos_ge_five` via `omega`
  (the stronger result `pos' ≥ pos + 5` implies `pos' > pos`)
- Net reduction: ~24 lines of duplicated guard-peeling proof eliminated

### Deliverable 2: Replace grind with targeted tactics
- Attempted 8+ fundamentally different approaches to replace `grind`:
  - `split at h` + `contradiction` + `simp only [...]`
  - `simp_all only [...]`
  - `dsimp` for match beta-reduction
  - `cases header.contentSize` for explicit case-splitting
  - Various combinations of the above
- **Root cause of failure**: Lean 4's `split` tactic cannot decompose `match`
  expressions on structure field accesses (`header.contentSize`,
  `header.dictionaryId`). The match discriminant must be a local variable
  for `split` to work. `grind` handles this via congruence closure.
- **Decision**: Kept `grind` with detailed comments explaining what it does
  and why targeted alternatives fail. This matches the issue's documented
  exception: "If grind is genuinely the simplest approach, keep it but add
  a comment explaining why."

## Quality metrics
- Sorry count: 6 (unchanged — 2 Fse, 4 XxHash)
- Line count: 562 → 547 (net -15 lines)
- No theorems removed or weakened
- All theorem signatures unchanged
- `grind` count: 2 (documented exceptions)
- All tests pass

## Patterns discovered
- `split at h` in Lean 4 cannot split on `match expr with ...` where `expr`
  involves structure field projections. Use `grind` for deep monadic
  case-splitting through functions with multiple guards on structure fields.
- When two theorems prove `P ≥ Q + k` and `P > Q`, always derive the weaker
  from the stronger via `omega` rather than duplicating the proof.
