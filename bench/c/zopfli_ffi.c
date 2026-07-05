/*
 * Lean FFI shim for zopfli (Track D maximum-ratio reference comparator).
 *
 * zopfli is a plain C encoder (compress only — its output is ordinary DEFLATE,
 * decoded by any inflate), so we call it directly when HAVE_ZOPFLI is defined,
 * and otherwise return an IO error. It is the compression-ratio *ceiling*: very
 * slow, very small output. `level` is mapped to zopfli's `numiterations`.
 *
 * Error wording follows .claude/skills/error-wording-catalogue/SKILL.md — the
 * IO error begins with the operation label ("zopfli compress").
 */

#include <lean/lean.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#ifdef HAVE_ZOPFLI
#include <zopfli.h>
#endif

static lean_obj_res mk_io_error(const char *msg) {
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(msg)));
}

#ifndef HAVE_ZOPFLI
#define ZOPFLI_DISABLED_MSG \
    "zopfli: not built with zopfli support — install zopfli (headers+lib) " \
    "and re-run `lake clean && lake build` (see BENCH.md)"
#endif

/*
 * Compress raw DEFLATE via zopfli. `iterations` is zopfli's numiterations knob
 * (the more iterations, the smaller and slower); 0 keeps zopfli's default (15).
 *
 * lean_zopfli_compress_ffi : @& ByteArray → UInt32 → IO ByteArray
 */
LEAN_EXPORT lean_obj_res lean_zopfli_compress_ffi(b_lean_obj_arg data,
                                                  uint32_t iterations,
                                                  lean_obj_arg _w) {
    (void)_w;
#ifndef HAVE_ZOPFLI
    (void)data;
    (void)iterations;
    return mk_io_error(ZOPFLI_DISABLED_MSG);
#else
    const uint8_t *src = lean_sarray_cptr(data);
    size_t src_len = lean_sarray_size(data);
    ZopfliOptions options;
    ZopfliInitOptions(&options);
    if (iterations > 0) {
        options.numiterations = (int)iterations;
    }
    unsigned char *out = NULL;
    size_t out_len = 0;
    ZopfliCompress(&options, ZOPFLI_FORMAT_DEFLATE, src, src_len, &out, &out_len);
    if (out == NULL) {
        return mk_io_error("zopfli compress: failed");
    }
    lean_obj_res arr = lean_alloc_sarray(1, out_len, out_len);
    if (out_len > 0) {
        memcpy(lean_sarray_cptr(arr), out, out_len);
    }
    free(out);
    return lean_io_result_mk_ok(arr);
#endif
}
