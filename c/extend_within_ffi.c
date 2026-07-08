/*
 * Single-pass, allocation-free overlapping-match copy for the DEFLATE
 * back-reference.
 *
 * `lean_zip_byte_array_extend_within(a, srcOff, distance, len)` appends `len`
 * bytes to `a`'s own tail, where appended byte `i` is `a[srcOff + (i % period)]`
 * — the periodic extension of the window `a[srcOff, srcOff + period)`. Its Lean
 * reference body is
 *
 *     a ++ (fillDouble (a.extract srcOff (srcOff + distance)) len).extract 0 len
 *
 * (see `ByteArray.extendWithin` in Zip/Native/ExtendWithin.lean), and this C
 * must agree with that body. `extract` is total and clamps its window to
 * `a.size`, so the effective `period` is clamped to `a.size - srcOff` here; an
 * empty window (`srcOff >= a.size` or `distance == 0`) makes `fillDouble` return
 * the seed unchanged, so nothing is appended. In the decoders
 * `srcOff = a.size - distance`, so `period == distance` exactly.
 *
 * The fill mirrors `fillDouble`'s doubling: copy the `period`-byte window once,
 * then `memcpy` the already-written prefix onto itself in `filled`-sized chunks
 * (each disjoint: dest starts at `filled >= chunk` past the source), so the
 * pattern smears forward with no per-byte modulo and no intermediate
 * allocation. `filled` stays a multiple of `period` until the final clamped
 * chunk, so the last partial copy still lands on a period boundary. `period == 1`
 * (RLE) takes a `memset` fast path (libdeflate's broadcast-store case).
 *
 * Why grow `a` in place rather than `++ extract`: the pure-Lean body allocates
 * the window, doubles it O(log) times (alloc + 2x memcpy each), re-extracts, and
 * appends — ~6 allocations to copy 10 bytes at distance 1. Here `a` is a single
 * owned argument: `ensure_capacity` grows it in place when exclusive (amortized),
 * no aliased borrow, no protective `inc`. Mirrors `copy_within_ffi.c` (the
 * non-overlapping sibling).
 *
 * This is a project-local FFI primitive (extern-with-reference-body pattern,
 * like `ByteArray.copyWithin`); the symbol is namespaced `lean_zip_*`.
 */

#include <lean/lean.h>
#include <stdint.h>

/* No <string.h>: the toolchain clang compiles this file with -nostdinc
 * (freestanding headers only, so the object can join the library's LTO
 * bitcode; see lakefile `ltoFlags`). The __builtin_mem* forms lower to the
 * same libc calls the Lean runtime already links. */

/* Internal Lean runtime helper: grow `a` to capacity `>= min_cap`, in place
 * when `a` is exclusive. Exported (non-static) from the runtime but not
 * declared in <lean/lean.h>. */
extern lean_object *lean_sarray_ensure_capacity(lean_object *a, size_t min_cap,
                                               int exact);

/*
 * lean_zip_byte_array_extend_within : ByteArray → Nat → Nat → Nat → ByteArray
 *   (a owned; srcOff, distance, len borrowed Nats)
 */
LEAN_EXPORT lean_object *lean_zip_byte_array_extend_within(
        lean_object *a, b_lean_obj_arg o_src_off, b_lean_obj_arg o_distance,
        b_lean_obj_arg o_len) {
    size_t src_off = lean_usize_of_nat(o_src_off);
    size_t oldsz   = lean_sarray_size(a);
    if (src_off >= oldsz) return a;                    /* empty window */
    size_t period = lean_usize_of_nat(o_distance);
    size_t avail  = oldsz - src_off;
    if (period > avail) period = avail;                /* extract clamp */
    if (period == 0) return a;                          /* empty window */
    size_t len = lean_usize_of_nat(o_len);
    if (len == 0) return a;
    /* Unlike copy_within (where len is clamped to <= a.size), len here is
     * unbounded, so guard oldsz + len against size_t wrap: a wrapped newsz
     * would under-reserve and the fill below would write out of bounds. The
     * reference body would OOM allocating such an array anyway. */
    if (len > SIZE_MAX - oldsz) lean_internal_panic_out_of_memory();
    size_t newsz = oldsz + len;

    lean_object *r = lean_sarray_ensure_capacity(a, newsz, 0);
    if (!lean_is_exclusive(r)) {
        size_t cap = lean_sarray_capacity(r);
        if (cap < newsz) cap = newsz;
        lean_object *c = lean_alloc_sarray(1, oldsz, cap);
        __builtin_memcpy(lean_sarray_cptr(c), lean_sarray_cptr(r), oldsz);
        lean_dec(r);
        r = c;
    }
    lean_sarray_set_size(r, newsz);

    uint8_t *p   = lean_sarray_cptr(r);
    uint8_t *dst = p + oldsz;
    if (period == 1) {                                  /* RLE broadcast */
        __builtin_memset(dst, p[src_off], len);
        return r;
    }
    /* Copy the window once (source [src_off, src_off+period) ends at or before
     * oldsz, dst = oldsz: disjoint), then smear it forward by doublings. The
     * first copy is clamped to `len`: when `len <= period` the reference body's
     * `fillDouble` returns the window and `.extract 0 len` keeps only `len`
     * bytes, so nothing past `dst[len)` is written. */
    size_t first = period < len ? period : len;
    __builtin_memcpy(dst, p + src_off, first);
    size_t filled = first;
    while (filled < len) {
        size_t chunk = filled;
        if (chunk > len - filled) chunk = len - filled;
        __builtin_memcpy(dst + filled, dst, chunk);   /* dest starts filled>=chunk past src */
        filled += chunk;
    }
    return r;
}
