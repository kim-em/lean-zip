/*
 * Word-sized little-endian ByteArray loads for the DEFLATE hot loops.
 *
 * `lean_zip_uget_u32le(a, off)` reads a 4-byte little-endian word starting at
 * byte `off` of `a`, returning an unboxed scalar. Its Lean reference body is the
 * byte-recombination expression
 *
 *     a[off] | a[off+1]<<8 | a[off+2]<<16 | a[off+3]<<24
 *
 * (see `ugetUInt32LE` in `Zip/Native/Wide.lean`), and this C must agree with it.
 * `lean_zip_uget_u64le(a, off)` is the 8-byte analog, used by the match-extension
 * inner loop (`lz77Greedy.countMatch`) to compare eight bytes per iteration.
 * The recombination is written out byte-by-byte so it is host-endian-independent
 * — little-endian *by construction* — and free of unaligned-access UB; on a
 * little-endian target the optimizer folds it to a single (possibly unaligned)
 * load.
 *
 * The Lean side carries the in-bounds proof (`off + 4 ≤ a.size`, resp.
 * `off + 8 ≤ a.size`), so C does no bounds check: the caller has already proven
 * the bytes at `off` are within the array. `a` is borrowed (`b_lean_obj_arg`);
 * the offset is a `size_t` (Lean `USize`), kept unboxed so a hot loop's index
 * arithmetic never boxes.
 *
 * This is a project-local stopgap mirroring the reader of lean#14053 (`wide
 * fixed-width load/store`); the symbols are namespaced `lean_zip_*` so they do
 * not clash with core after the toolchain bump. When lean#14053 lands this file
 * and its lakefile target are deleted and core's `uget*` primitive is used (the
 * reference body is identical, so callers and proofs are unchanged).
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
    return (uint64_t)p[0]         | ((uint64_t)p[1] << 8)  |
           ((uint64_t)p[2] << 16) | ((uint64_t)p[3] << 24) |
           ((uint64_t)p[4] << 32) | ((uint64_t)p[5] << 40) |
           ((uint64_t)p[6] << 48) | ((uint64_t)p[7] << 56);
}

/*
 * lean_zip_ctz64 : UInt64 → UInt64  (count trailing zero bits)
 *
 * Used by the match-extension loop to locate the first mismatching byte from the
 * XOR of two 8-byte words: `ctz(w1 ^ w2) >>> 3` is the little-endian byte index
 * of the first difference. `__builtin_ctzll` is undefined at zero, so the zero
 * case returns 64 to match the Lean reference body `BitVec.ctz` (its spec).
 */
LEAN_EXPORT uint64_t lean_zip_ctz64(uint64_t x) {
    return x ? (uint64_t)__builtin_ctzll(x) : 64;
}
