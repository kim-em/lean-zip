/*
 * Word-sized little-endian ByteArray loads for the DEFLATE hot loops.
 *
 * `lean_zip_uget_u32le(a, off)` and `lean_zip_uget_u64le(a, off)` read a
 * 4-/8-byte little-endian word starting at byte `off` of `a`, returning an
 * unboxed scalar. Their Lean reference bodies are the byte-recombination
 * expressions
 *
 *     a[off] | a[off+1]<<8 | a[off+2]<<16 | a[off+3]<<24                (u32)
 *     a[off] | a[off+1]<<8 | ... | a[off+7]<<56                        (u64)
 *
 * (see `ugetUInt32LE` / `ugetUInt64LE` in `Zip/Native/Wide.lean`), and this C
 * must agree with those bodies. The recombination is written out byte-by-byte
 * so it is host-endian-independent — little-endian *by construction* — and free
 * of unaligned-access UB; on a little-endian target the optimizer folds each to
 * a single (possibly unaligned) load.
 *
 * The Lean side carries the in-bounds proof (`off + W/8 ≤ a.size`), so C does
 * no bounds check: the caller has already proven the `W/8` bytes at `off` are
 * within the array. `a` is borrowed (`b_lean_obj_arg`); the offset is a
 * `size_t` (Lean `USize`), kept unboxed so a hot loop's index arithmetic never
 * boxes.
 *
 * This is a project-local stopgap mirroring the readers of lean#14053 (`wide
 * fixed-width load/store`); the symbols are namespaced `lean_zip_*` so they do
 * not clash with core after the toolchain bump. When lean#14053 lands this file
 * and its lakefile target are deleted and core's `uget*` primitives are used
 * (the reference bodies are identical, so callers and proofs are unchanged).
 */

#include <lean/lean.h>
#include <stdint.h>

/*
 * lean_zip_uget_u32le : ByteArray → USize → UInt32
 *   (a borrowed, off an unboxed size_t; returns an unboxed uint32_t)
 */
LEAN_EXPORT uint32_t lean_zip_uget_u32le(b_lean_obj_arg a, size_t off) {
    const uint8_t *p = lean_sarray_cptr(a) + off;
    return (uint32_t)p[0]         | ((uint32_t)p[1] << 8) |
           ((uint32_t)p[2] << 16) | ((uint32_t)p[3] << 24);
}

/*
 * lean_zip_uget_u64le : ByteArray → USize → UInt64
 *   (a borrowed, off an unboxed size_t; returns an unboxed uint64_t)
 */
LEAN_EXPORT uint64_t lean_zip_uget_u64le(b_lean_obj_arg a, size_t off) {
    const uint8_t *p = lean_sarray_cptr(a) + off;
    uint64_t v = 0;
    for (int i = 0; i < 8; i++) v |= (uint64_t)p[i] << (8 * i);
    return v;
}
