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
 * lean_zip_uset_u64le : ByteArray → USize → UInt64 → ByteArray
 *   (a owned, off an unboxed size_t, v an unboxed uint64_t)
 *
 * Store the 8 bytes of `v` little-endian at byte offset `off`. The Lean
 * reference body is the chain of eight `a.set` writes (see `usetUInt64LE` in
 * `Zip/Native/Wide.lean`), and this C must agree with it. As with the loads,
 * the store is written out byte-by-byte so it is little-endian by construction
 * and free of unaligned-access UB; the optimizer folds it to a single wide
 * store. The Lean side carries the in-bounds proof (`off + 8 ≤ a.size`), so C
 * does no bounds check. `a` is owned: when the caller holds the only
 * reference the store is done in place (the hot-loop case); otherwise the
 * array is copied first, exactly like `lean_byte_array_uset`.
 */
LEAN_EXPORT lean_obj_res lean_zip_uset_u64le(lean_obj_arg a, size_t off, uint64_t v) {
    lean_obj_res r;
    if (lean_is_exclusive(a)) r = a;
    else r = lean_copy_byte_array(a);
    uint8_t *p = lean_sarray_cptr(r) + off;
    p[0] = (uint8_t)(v);
    p[1] = (uint8_t)(v >> 8);
    p[2] = (uint8_t)(v >> 16);
    p[3] = (uint8_t)(v >> 24);
    p[4] = (uint8_t)(v >> 32);
    p[5] = (uint8_t)(v >> 40);
    p[6] = (uint8_t)(v >> 48);
    p[7] = (uint8_t)(v >> 56);
    return r;
}

/*
 * lean_zip_uset_u32le : ByteArray → USize → UInt32 → ByteArray
 *   (a owned, off an unboxed size_t, v an unboxed uint32_t)
 *
 * Store the 4 bytes of `v` little-endian at byte offset `off`. The Lean
 * reference body is the chain of four `a.set` writes (see `usetUInt32LE` in
 * `Zip/Native/Wide.lean`), and this C must agree with it. As with the loads,
 * the store is written out byte-by-byte so it is little-endian by construction
 * and free of unaligned-access UB; the optimizer folds it to a single wide
 * store. The Lean side carries the in-bounds proof (`off + 4 ≤ a.size`), so C
 * does no bounds check. `a` is owned: when the caller holds the only
 * reference the store is done in place (the hot-loop case); otherwise the
 * array is copied first, exactly like `lean_byte_array_uset`.
 */
LEAN_EXPORT lean_obj_res lean_zip_uset_u32le(lean_obj_arg a, size_t off, uint32_t v) {
    lean_obj_res r;
    if (lean_is_exclusive(a)) r = a;
    else r = lean_copy_byte_array(a);
    uint8_t *p = lean_sarray_cptr(r) + off;
    p[0] = (uint8_t)(v);
    p[1] = (uint8_t)(v >> 8);
    p[2] = (uint8_t)(v >> 16);
    p[3] = (uint8_t)(v >> 24);
    return r;
}

/*
 * lean_zip_push_u64le : ByteArray → UInt64 → USize → ByteArray
 *   (a owned, v an unboxed uint64_t, k an unboxed size_t, k ≤ 8)
 *
 * Append the low `k` bytes of `v`, LSB-first — the wide-store form of the
 * BitWriter's per-byte flush loop. The Lean reference body is `k` iterated
 * `a.push v.toUInt8` / `v >>> 8` steps (see `pushUInt64LE` in
 * `Zip/Native/Wide.lean`), and this C must agree with it. Hot path (exclusive
 * array with ≥ 8 spare bytes of capacity): one unconditional 8-byte store at
 * the end — bytes past `size + k` land in capacity slack, which is not part
 * of the value — then bump the size by `k`. Cold path (shared, or capacity
 * tight): fall back to the byte-wise pushes of the model, which handle
 * copy-on-write and growth. The Lean side carries the `k ≤ 8` proof.
 */
LEAN_EXPORT lean_obj_res lean_zip_push_u64le(lean_obj_arg a, uint64_t v, size_t k) {
    size_t sz = lean_sarray_size(a);
    /* cap - sz cannot underflow (size <= capacity is a sarray invariant), and
     * the subtraction form cannot overflow the way `sz + 8` in principle could. */
    if (lean_is_exclusive(a) && lean_sarray_capacity(a) - sz >= 8) {
        uint8_t *p = lean_sarray_cptr(a) + sz;
        p[0] = (uint8_t)(v);
        p[1] = (uint8_t)(v >> 8);
        p[2] = (uint8_t)(v >> 16);
        p[3] = (uint8_t)(v >> 24);
        p[4] = (uint8_t)(v >> 32);
        p[5] = (uint8_t)(v >> 40);
        p[6] = (uint8_t)(v >> 48);
        p[7] = (uint8_t)(v >> 56);
        lean_sarray_set_size(a, sz + k);
        return a;
    }
    for (size_t i = 0; i < k; i++) {
        a = lean_byte_array_push(a, (uint8_t)(v >> (8 * i)));
    }
    return a;
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
