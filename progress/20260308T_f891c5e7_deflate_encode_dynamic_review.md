# DeflateEncodeDynamic.lean Quality Review

- **Date**: 2026-03-08 UTC
- **Session**: f891c5e7 (review)
- **Issue**: #854

## Summary

Converted all 7 bare `simp` calls in `Zip/Spec/DeflateEncodeDynamic.lean` to
`simp only [...]` with explicit lemma lists.

## Changes

| Location | Original | Replacement |
|----------|----------|-------------|
| `countRun_le_length` nil | `simp [countRun]` | `simp only [countRun, List.length_nil, Nat.le_refl]` |
| `countRun_take` nil | `simp [countRun]` | `simp only [countRun, List.take_nil, List.replicate_zero]` |
| `take_countRun_eq_replicate` nil | `simp [countRun] at hn; simp [hn]` | `have h0 := ...; subst h0; simp only [...]` |
| `replicate_drop_eq_cons_zero` rw arg | `by simp [countRun]; omega` | `by show ...; simp only [countRun, beq_self_eq_true, ↓reduceIte]; omega` |
| `replicate_drop_eq_cons_zero` succ case | `simp [List.drop_succ_cons]` | `simp only [Nat.add_sub_cancel, List.drop_succ_cons]` |
| `rlDecodeLengths_go_rlEncodeLengths_go` nil | `simp [rlEncodeLengths.go, rlDecodeLengths.go]` | `simp only [..., List.append_nil]` |
| `rlEncodeLengths_go_valid` nil | `simp [rlEncodeLengths.go]` | `simp only [..., List.not_mem_nil, false_implies, implies_true]` |

## Boilerplate assessment

The issue requested compressing repeated `countRun` nil case patterns (lines 37,
100, 116). These are structurally different goals (proving `≤`, `take = replicate`,
`take n = replicate n` with bound) and cannot meaningfully share a helper lemma.
The three identical `decreasing_by` blocks are tied to their recursive functions
and don't benefit from extraction.

## PR #811 verification

PR #811 targeted `simp_all` → targeted tactics (5 conversions). The 7 bare
`simp` calls in this review are distinct from those changes — they use
`simp [lemma]` pattern, not `simp_all`.

## Quality metrics

- Sorry count: 4 → 4 (unchanged, all in XxHash)
- Bare simp in file: 7 → 0
- All theorem signatures unchanged
- Net: +2 lines (mostly from splitting a one-liner into clearer two-line form)
