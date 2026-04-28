/*
 * Lean FFI shim for miniz_oxide (Track D Phase 0c comparator).
 *
 * This file deliberately avoids referring to any miniz_oxide types: the
 * Rust crate exposes a tiny C-ABI surface from rust/miniz_oxide_shim/
 * (see src/lib.rs there). We forward to those three functions when
 * HAVE_MINIZ_OXIDE is defined at compile time, and otherwise return an
 * IO error explaining how to enable the comparator. This keeps `lake
 * build` working in environments without cargo+rustc.
 *
 * Error wording follows the conventions in
 * .claude/skills/error-wording-catalogue/SKILL.md — every IO error
 * begins with the operation label ("miniz_oxide compress" /
 * "miniz_oxide decompress") so callers can `String.contains` the family
 * keyword.
 */

#include <lean/lean.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#ifdef HAVE_MINIZ_OXIDE
/* C-ABI symbols exported by rust/miniz_oxide_shim/src/lib.rs. */
extern int lean_miniz_oxide_compress(const uint8_t *input, size_t input_len,
                                     uint8_t level, uint8_t **out_ptr,
                                     size_t *out_len);
extern int lean_miniz_oxide_decompress(const uint8_t *input, size_t input_len,
                                       uint64_t max_output, uint8_t **out_ptr,
                                       size_t *out_len);
extern void lean_miniz_oxide_free(uint8_t *ptr, size_t len);
#endif

static lean_obj_res mk_io_error(const char *msg) {
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(msg)));
}

#ifndef HAVE_MINIZ_OXIDE
#define MINIZ_DISABLED_MSG \
    "miniz_oxide: not built with Rust support — install cargo+rustc " \
    "and re-run `lake clean && lake build` (see BENCH.md)"
#endif

/*
 * Compress raw DEFLATE via miniz_oxide.
 *
 * lean_miniz_oxide_compress_ffi : @& ByteArray → UInt8 → IO ByteArray
 */
LEAN_EXPORT lean_obj_res lean_miniz_oxide_compress_ffi(b_lean_obj_arg data,
                                                       uint8_t level,
                                                       lean_obj_arg _w) {
    (void)_w;
#ifndef HAVE_MINIZ_OXIDE
    (void)data;
    (void)level;
    return mk_io_error(MINIZ_DISABLED_MSG);
#else
    const uint8_t *src = lean_sarray_cptr(data);
    size_t src_len = lean_sarray_size(data);
    uint8_t *out = NULL;
    size_t out_len = 0;
    int rc = lean_miniz_oxide_compress(src, src_len, level, &out, &out_len);
    if (rc != 0) {
        return mk_io_error("miniz_oxide compress: failed");
    }
    lean_obj_res arr = lean_alloc_sarray(1, out_len, out_len);
    if (out_len > 0) {
        memcpy(lean_sarray_cptr(arr), out, out_len);
    }
    lean_miniz_oxide_free(out, out_len);
    return lean_io_result_mk_ok(arr);
#endif
}

/*
 * Decompress raw DEFLATE via miniz_oxide.
 *
 * `max_output == 0` means unlimited (bomb-unsafe — only use for trusted
 * input). Output-limit overruns return an IO error containing
 * "exceeds limit", matching the wording used by RawDeflate.decompress.
 *
 * lean_miniz_oxide_decompress_ffi : @& ByteArray → UInt64 → IO ByteArray
 */
LEAN_EXPORT lean_obj_res lean_miniz_oxide_decompress_ffi(b_lean_obj_arg data,
                                                         uint64_t max_output,
                                                         lean_obj_arg _w) {
    (void)_w;
#ifndef HAVE_MINIZ_OXIDE
    (void)data;
    (void)max_output;
    return mk_io_error(MINIZ_DISABLED_MSG);
#else
    const uint8_t *src = lean_sarray_cptr(data);
    size_t src_len = lean_sarray_size(data);
    uint8_t *out = NULL;
    size_t out_len = 0;
    int rc = lean_miniz_oxide_decompress(src, src_len, max_output, &out, &out_len);
    if (rc == 3) {
        char buf[160];
        snprintf(buf, sizeof(buf),
                 "miniz_oxide decompress: decompressed size exceeds limit "
                 "(%llu bytes)",
                 (unsigned long long)max_output);
        return mk_io_error(buf);
    }
    if (rc != 0) {
        return mk_io_error("miniz_oxide decompress: failed");
    }
    lean_obj_res arr = lean_alloc_sarray(1, out_len, out_len);
    if (out_len > 0) {
        memcpy(lean_sarray_cptr(arr), out, out_len);
    }
    lean_miniz_oxide_free(out, out_len);
    return lean_io_result_mk_ok(arr);
#endif
}
