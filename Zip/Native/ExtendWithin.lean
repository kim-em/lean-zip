/-!
  Single-pass, allocation-free overlapping-match copy for the DEFLATE
  back-reference.

  `ByteArray.extendWithin a srcOff distance len` appends `len` bytes to `a`'s
  own tail, where appended byte `i` is `a[srcOff + (i % distance)]` — the
  periodic extension of the `distance`-byte window `a[srcOff, srcOff + distance)`.
  This is the LZ77 **overlapping** back-reference (`len > distance`, e.g. RLE),
  where the source window and the bytes being written overlap.

  The reference body — and the trusted specification of the `@[extern]` — is
  literally

      a ++ (fillDouble (a.extract srcOff (srcOff + distance)) len).extract 0 len

  which is exactly the expression `Inflate.copyLoop`'s overlapping branch used
  to compute inline. The pure-Lean body allocates the `distance`-byte window
  (`extract`), doubles it `⌈log₂ (len / distance)⌉` times (each an alloc plus two
  `memcpy`s), re-`extract`s the first `len` bytes, then appends — on the order of
  six allocations to copy ten bytes for `distance = 1, len = 10`. The C
  implementation (`c/extend_within_ffi.c`) grows `a` in place and smears the
  window forward with `memcpy` doublings, matching `fillDouble`'s structure with
  no intermediate allocation (and a `memset` fast path for `distance = 1` RLE).

  `fillDouble` is total: `extract` clamps its window to `a.size`, and a window of
  size `0` (empty, e.g. `distance = 0` or `srcOff ≥ a.size`) makes `fillDouble`
  return it unchanged so nothing is appended; the C clamps the effective period
  the same way, so the body stays a faithful model for every input. In the
  decoders `srcOff = a.size - distance`, so the window is always exactly
  `distance` bytes.

  This follows the extern-with-reference-body pattern of `ByteArray.copyWithin`
  (Zip/Native/CopyWithin.lean, the non-overlapping sibling); the owner has
  approved these project-local FFI primitives as temporary exceptions to the
  no-`@[extern]` rule. The C symbol is namespaced `lean_zip_*`.
-/

namespace ByteArray

/-- Periodic extension of a non-empty `seed` window to at least `length` bytes by
    repeated doubling — each step is a `ByteArray` append (a `memcpy`), so the
    whole fill is `O(log (length / seed.size))` memcpys. `seed` is the
    `distance`-byte back-reference window; doubling it preserves the period
    (`seed.size` always divides the running size), so slot `i` of the result is
    `seed[i % seed.size]`. Used by `extendWithin` for overlapping LZ77
    back-references (`distance < length`, e.g. RLE), where a per-byte copy
    otherwise dominates decode of highly repetitive data. -/
def fillDouble (seed : ByteArray) (length : Nat) : ByteArray :=
  if seed.size ≥ length ∨ seed.size = 0 then seed
  else fillDouble (seed ++ seed) length
termination_by length - seed.size
decreasing_by
  simp only [ByteArray.size_append]
  omega

/-- Append the periodic extension of the window `a[srcOff, srcOff + distance)` to
    `a`'s own tail, producing `len` new bytes (appended byte `i` is
    `a[srcOff + (i % distance)]`). This is the LZ77 overlapping back-reference
    copy. The reference body
    `a ++ (fillDouble (a.extract srcOff (srcOff + distance)) len).extract 0 len`
    is the trusted specification of the `@[extern]`; `extract`/`fillDouble` clamp
    an empty window to appending nothing, and the C clamps to match. -/
@[extern "lean_zip_byte_array_extend_within"]
def extendWithin (a : ByteArray) (srcOff distance len : Nat) : ByteArray :=
  a ++ (fillDouble (a.extract srcOff (srcOff + distance)) len).extract 0 len

end ByteArray
