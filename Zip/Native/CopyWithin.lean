/-!
  Single-pass self-append primitive for the DEFLATE back-reference copy.

  `ByteArray.copyWithin a srcOff len` appends the slice `a[srcOff, srcOff + len)`
  to `a`'s own tail. The reference body — and the trusted specification of the
  `@[extern]` — is literally

      a ++ a.extract srcOff (srcOff + len)

  which is exactly the expression `Inflate.copyLoop`'s non-overlapping branch
  already computes. The C implementation (`c/copy_within_ffi.c`) does it in one
  `memcpy` with no intermediate allocation, where today the pure-Lean
  `++ extract` is two `memcpy`s plus an allocation. Measured ~+28–38% native
  decode throughput on the standard corpora (issue #2675).

  `extract` is total and clamps its upper bound to `a.size`, so this is the
  **non-overlapping** path only (`srcOff + len ≤ a.size`); the C clamps `len` to
  match, so source and destination never overlap and the body stays a faithful
  model. The overlapping / RLE case (`len > distance`) stays in pure Lean
  (`fillDouble`) and does not use this primitive.

  This is a project-local stopgap for the upstream Lean-core primitive proposed
  in lean#14158 (`feat: add ByteArray.copyWithin`); the owner has approved it as
  a temporary exception to the no-`@[extern]` rule. The C symbol is namespaced
  `lean_zip_*` so it does not clash with core's `lean_byte_array_copy_within`
  after the toolchain bump. Migration once lean#14158 lands: delete this file and
  `c/copy_within_ffi.c`, and use core's `ByteArray.copyWithin` (its `@[extern]`
  and reference body are identical, so callers and proofs are unchanged).
-/

namespace ByteArray

/-- Append the slice `a[srcOff, srcOff + len)` to `a`'s own tail in one pass.
    Non-overlapping only: intended for `srcOff + len ≤ a.size`. The reference
    body `a ++ a.extract srcOff (srcOff + len)` is the trusted specification of
    the `@[extern]`; `extract` clamps, and the C clamps `len` to match. -/
@[extern "lean_zip_byte_array_copy_within"]
def copyWithin (a : ByteArray) (srcOff len : Nat) : ByteArray :=
  a ++ a.extract srcOff (srcOff + len)

end ByteArray
