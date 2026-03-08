# Review: DeflateDynamicHeader.lean quality — bare simp + linter pragma cleanup

**Date**: 2026-03-08T06:00 UTC
**Session**: review (6626fe38)
**Issue**: #871

## Accomplished

1. **Converted 6 bare `simp` to `simp only`** in `Zip/Spec/DeflateDynamicHeader.lean`:
   - Line 145: `simp [Deflate.Spec.encodeCLEntries]` → `simp only [Deflate.Spec.encodeCLEntries, Option.some.injEq, List.nil_eq]`
   - Line 156: `simp [hencsym]` → `simp only [hencsym, List.append_assoc, Option.pure_def, Option.bind_eq_bind, Option.bind_none, reduceCtorEq]`
   - Line 164: `simp [hencsym, hencrest]` → `simp only [hencsym, hencrest, ..., Option.bind_none, Option.bind_fun_none, reduceCtorEq]`
   - Line 167: `simp [hencsym, hencrest]` → `simp only [hencsym, hencrest, ..., Option.bind_some, Option.some.injEq]`
   - Lines 243-244: `by simp [hlitLen]` / `by simp [hdistLen]` → `by simp only [ge_iff_le, hlitLen, and_self]` / `by simp only [ge_iff_le, hdistLen, and_self]`

2. **Linter pragma**: The `set_option linter.unusedSimpArgs false` mentioned in the issue was not present in the current file — already addressed in a prior session.

3. **General quality pass**: No other bare `simp`, no `set_option` pragmas, no `sorry`, no debug artifacts. File is 382 lines, well within limits. Consistent with recently cleaned DeflateDynamicEmit.lean.

4. **Removed 5 stale "bare simp" comments** that no longer applied after conversion.

## Quality metrics

- Sorry count: 4 → 4 (unchanged, all XxHash)
- Bare simp in file: 6 → 0
- `set_option` pragmas: 0 → 0
- All theorem signatures unchanged
- All tests pass
