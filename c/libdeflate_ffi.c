/*
 * Lean FFI shim for libdeflate (Track D reference comparator).
 *
 * libdeflate is a plain C library, so unlike the miniz_oxide shim there is no
 * Rust layer — we call it directly when HAVE_LIBDEFLATE is defined at compile
 * time, and otherwise return an IO error explaining how to enable it. This
 * keeps `lake build` working in environments without libdeflate.
 *
 * Error wording follows .claude/skills/error-wording-catalogue/SKILL.md — every
 * IO error begins with the operation label ("libdeflate compress" /
 * "libdeflate decompress").
 */

#include <lean/lean.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#ifdef HAVE_LIBDEFLATE
#include <libdeflate.h>
#endif

static lean_obj_res mk_io_error(const char *msg) {
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(msg)));
}

#ifndef HAVE_LIBDEFLATE
#define LIBDEFLATE_DISABLED_MSG \
    "libdeflate: not built with libdeflate support — install libdeflate " \
    "(headers+lib) and re-run `lake clean && lake build` (see BENCH.md)"
#endif

/*
 * Compress raw DEFLATE via libdeflate at the given level (1–12).
 *
 * lean_libdeflate_compress_ffi : @& ByteArray → UInt8 → IO ByteArray
 */
LEAN_EXPORT lean_obj_res lean_libdeflate_compress_ffi(b_lean_obj_arg data,
                                                      uint8_t level,
                                                      lean_obj_arg _w) {
    (void)_w;
#ifndef HAVE_LIBDEFLATE
    (void)data;
    (void)level;
    return mk_io_error(LIBDEFLATE_DISABLED_MSG);
#else
    const uint8_t *src = lean_sarray_cptr(data);
    size_t src_len = lean_sarray_size(data);
    struct libdeflate_compressor *c = libdeflate_alloc_compressor((int)level);
    if (c == NULL) {
        return mk_io_error("libdeflate compress: alloc_compressor failed");
    }
    size_t bound = libdeflate_deflate_compress_bound(c, src_len);
    uint8_t *out = (uint8_t *)malloc(bound > 0 ? bound : 1);
    if (out == NULL) {
        libdeflate_free_compressor(c);
        return mk_io_error("libdeflate compress: out of memory");
    }
    size_t out_len = libdeflate_deflate_compress(c, src, src_len, out, bound);
    libdeflate_free_compressor(c);
    if (out_len == 0) {
        free(out);
        return mk_io_error("libdeflate compress: failed");
    }
    lean_obj_res arr = lean_alloc_sarray(1, out_len, out_len);
    memcpy(lean_sarray_cptr(arr), out, out_len);
    free(out);
    return lean_io_result_mk_ok(arr);
#endif
}

/*
 * Decompress raw DEFLATE via libdeflate. `max_output` bounds the output buffer.
 *
 * lean_libdeflate_decompress_ffi : @& ByteArray → UInt64 → IO ByteArray
 */
LEAN_EXPORT lean_obj_res lean_libdeflate_decompress_ffi(b_lean_obj_arg data,
                                                        uint64_t max_output,
                                                        lean_obj_arg _w) {
    (void)_w;
#ifndef HAVE_LIBDEFLATE
    (void)data;
    (void)max_output;
    return mk_io_error(LIBDEFLATE_DISABLED_MSG);
#else
    const uint8_t *src = lean_sarray_cptr(data);
    size_t src_len = lean_sarray_size(data);
    struct libdeflate_decompressor *d = libdeflate_alloc_decompressor();
    if (d == NULL) {
        return mk_io_error("libdeflate decompress: alloc_decompressor failed");
    }
    size_t cap = (size_t)max_output;
    uint8_t *out = (uint8_t *)malloc(cap > 0 ? cap : 1);
    if (out == NULL) {
        libdeflate_free_decompressor(d);
        return mk_io_error("libdeflate decompress: out of memory");
    }
    size_t actual = 0;
    enum libdeflate_result r =
        libdeflate_deflate_decompress(d, src, src_len, out, cap, &actual);
    libdeflate_free_decompressor(d);
    if (r != LIBDEFLATE_SUCCESS) {
        free(out);
        return mk_io_error("libdeflate decompress: failed");
    }
    lean_obj_res arr = lean_alloc_sarray(1, actual, actual);
    if (actual > 0) {
        memcpy(lean_sarray_cptr(arr), out, actual);
    }
    free(out);
    return lean_io_result_mk_ok(arr);
#endif
}
