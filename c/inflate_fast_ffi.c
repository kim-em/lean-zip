/*
 * Write-once cursor primitives for the DEFLATE fastloop decoder (issue #2799).
 *
 * The fastloop pre-extends the output buffer to its final size once, then
 * writes each literal / match at a cursor with no per-symbol capacity check.
 * Two primitives back that design:
 *
 *   lean_zip_byte_array_presize(n)
 *     Allocate a zero-filled ByteArray of size `n`. Lean reference body:
 *         ByteArray.mk (Array.replicate n 0)
 *     The C `calloc`-equivalent (lean_alloc_sarray + memset) produces exactly
 *     that: `n` zero bytes.
 *
 *   lean_zip_byte_array_copy_within_at(a, destOff, distance, len)
 *     In-place LZ77 back-reference copy at a cursor: for i in [0, len),
 *         a[destOff + i] := a[destOff - distance + (i % distance)]
 *     i.e. the forward-propagating copy `a[destOff+i] = a[destOff+i-distance]`.
 *     Lean reference body is the `set`-loop `copyWithinAtGo` (see
 *     Zip/Native/InflateFast.lean), and this C must agree with it. Unlike
 *     `copy_within` / `extend_within` (which APPEND to the tail), this writes
 *     into already-allocated space ahead of the cursor, so it never grows `a`
 *     and never reallocates.
 *
 * These are project-local FFI primitives (extern-with-reference-body pattern,
 * like `ByteArray.copyWithin` / `extendWithin`); the owner has approved such
 * primitives as temporary exceptions to the no-`@[extern]` rule. Symbols are
 * namespaced `lean_zip_*`.
 */

#include <lean/lean.h>
#include <stdint.h>

/* No <string.h>: the toolchain clang compiles this file with -nostdinc
 * (freestanding headers only, so the object can join the library's LTO
 * bitcode; see lakefile `ltoFlags`). The __builtin_mem* forms have the
 * same C semantics and need no header prototype. */

/*
 * lean_zip_byte_array_presize : Nat → ByteArray   (o_n borrowed Nat)
 *   Zero-filled ByteArray of size n. Matches `ByteArray.mk (Array.replicate n 0)`.
 */
LEAN_EXPORT lean_object *lean_zip_byte_array_presize(b_lean_obj_arg o_n) {
    size_t n = lean_usize_of_nat(o_n);
    lean_object *r = lean_alloc_sarray(1, n, n);
    __builtin_memset(lean_sarray_cptr(r), 0, n);
    return r;
}

/*
 * lean_zip_byte_array_copy_within_at : ByteArray → Nat → Nat → Nat → ByteArray
 *   (a owned; destOff, distance, len borrowed Nats)
 *
 * Writes `len` bytes at `destOff`, byte i being a[destOff - distance + i%period].
 * Requires (caller-guaranteed, from the decoder's proven bounds):
 *   distance >= 1,  distance <= destOff,  destOff + len <= a.size.
 * The reference body clamps a degenerate window to a no-op; this C mirrors that.
 */
LEAN_EXPORT lean_object *lean_zip_byte_array_copy_within_at(
        lean_object *a, b_lean_obj_arg o_dest_off, b_lean_obj_arg o_distance,
        b_lean_obj_arg o_len) {
    size_t dest_off = lean_usize_of_nat(o_dest_off);
    size_t distance = lean_usize_of_nat(o_distance);
    size_t len      = lean_usize_of_nat(o_len);
    size_t sz       = lean_sarray_size(a);

    /* Degenerate guards mirroring the reference body's totality clamps. */
    if (distance == 0 || distance > dest_off) return a;
    if (len == 0) return a;
    if (dest_off > sz || len > sz - dest_off) return a;   /* would be OOB */

    /* `a` is a single owned argument; make it exclusive so the write is in
     * place. A shared array is copied once (rare on the decode hot path). */
    if (!lean_is_exclusive(a)) {
        lean_object *c = lean_alloc_sarray(1, sz, lean_sarray_capacity(a));
        __builtin_memcpy(lean_sarray_cptr(c), lean_sarray_cptr(a), sz);
        lean_dec(a);
        a = c;
    }

    uint8_t *p   = lean_sarray_cptr(a);
    uint8_t *dst = p + dest_off;
    uint8_t *win = p + dest_off - distance;   /* the `distance`-byte window */

    if (len <= distance) {                     /* non-overlapping: disjoint memcpy */
        __builtin_memcpy(dst, win, len);
        return a;
    }
    if (distance == 1) {                        /* RLE broadcast */
        __builtin_memset(dst, win[0], len);
        return a;
    }
    /* Overlapping: smear the window forward by doublings (mirrors extendWithin).
     * win = [destOff-distance, destOff) and dst = [destOff, ...) are adjacent
     * and disjoint for the first `distance` bytes, so the seeding memcpy is
     * well-defined; each doubling copies an already-written prefix forward. */
    __builtin_memcpy(dst, win, distance);
    size_t filled = distance;
    while (filled < len) {
        size_t chunk = filled;
        if (chunk > len - filled) chunk = len - filled;
        __builtin_memcpy(dst + filled, dst, chunk);
        filled += chunk;
    }
    return a;
}
