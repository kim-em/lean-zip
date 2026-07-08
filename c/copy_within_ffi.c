/*
 * Single-pass self-append primitive for the DEFLATE back-reference copy.
 *
 * `lean_zip_byte_array_copy_within(a, srcOff, len)` appends the slice
 * `a[srcOff, srcOff + len)` to `a`'s own tail in one `memcpy`, with no
 * intermediate allocation. Its Lean reference body is
 *
 *     a ++ a.extract srcOff (srcOff + len)
 *
 * (see `ByteArray.copyWithin` in Zip/Native/CopyWithin.lean), and this C must
 * agree with that body. `extract` is total and clamps its upper bound to
 * `a.size`, so `len` is clamped to `a.size - srcOff` here; with that clamp the
 * source `[srcOff, srcOff + len)` and destination `[oldsz, oldsz + len)` ranges
 * are disjoint (`srcOff + len <= oldsz`), so a plain `memcpy` is correct. This
 * is the NON-overlapping path only — no LZ77 forward propagation.
 *
 * Why this and not `copySlice` onto self: `copySlice` takes `src` borrowed and
 * `dest` owned, so calling it with `src = dest = a` makes the compiler emit a
 * protective `inc` around the call, which leaves `dest` non-exclusive inside —
 * forcing a full O(a.size) buffer copy on every call (quadratic over a decode).
 * Here `a` is a single owned argument: no aliased borrow, no protective `inc`,
 * `a` stays exclusive, and `ensure_capacity` grows it in place (amortized).
 *
 * This is a project-local stopgap for lean#14158 (`ByteArray.copyWithin`); the
 * symbol is namespaced `lean_zip_*` so it does not clash with core's
 * `lean_byte_array_copy_within` after the toolchain bump. When lean#14158 lands
 * this file and the lakefile target are deleted and core's primitive is used.
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
 * lean_zip_byte_array_copy_within : ByteArray → Nat → Nat → ByteArray
 *   (a owned, srcOff and len borrowed Nats)
 */
LEAN_EXPORT lean_object *lean_zip_byte_array_copy_within(
        lean_object *a, b_lean_obj_arg o_src_off, b_lean_obj_arg o_len) {
    size_t src_off = lean_usize_of_nat(o_src_off);
    size_t oldsz   = lean_sarray_size(a);
    if (src_off > oldsz) return a;                     /* match extract clamp */
    size_t len = lean_usize_of_nat(o_len);
    if (len > oldsz - src_off) len = oldsz - src_off;  /* non-overlapping */
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

    uint8_t *p = lean_sarray_cptr(r);
    __builtin_memcpy(p + oldsz, p + src_off, len);   /* src_off + len <= oldsz: disjoint */
    return r;
}
