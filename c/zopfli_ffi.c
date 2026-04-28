#include <lean/lean.h>
#include <zopfli.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <limits.h>

/*
 * Zopfli FFI shim. Zopfli is encode-only (no decompress entry point) and
 * intentionally very slow — typically ~100× zlib level 9. Used as the
 * compression-ratio quality ceiling in Track D benchmarks; not on any
 * production hot path.
 *
 * Output is appended to a heap buffer that ZopfliCompress allocates via
 * malloc/realloc. We copy it into a Lean ByteArray and free the original.
 */

static lean_obj_res mk_byte_array(const uint8_t *data, size_t len) {
    lean_obj_res arr = lean_alloc_sarray(1, len, len);
    memcpy(lean_sarray_cptr(arr), data, len);
    return arr;
}

static lean_obj_res mk_io_error(const char *msg) {
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(msg)));
}

/*
 * Compress `data` with zopfli, raw deflate framing.
 *
 * lean_zopfli_deflate : @& ByteArray → UInt32 → IO ByteArray
 *
 * `numIterations` controls the optimization budget; must be ≥ 1.
 * Zopfli treats it as `int`, so we reject values that would not round-trip.
 */
LEAN_EXPORT lean_obj_res lean_zopfli_deflate(b_lean_obj_arg data,
                                             uint32_t numIterations,
                                             lean_obj_arg _w) {
    const uint8_t *src = lean_sarray_cptr(data);
    size_t src_len = lean_sarray_size(data);

    if (numIterations == 0) {
        return mk_io_error("zopfli deflate: numIterations must be >= 1");
    }
    if (numIterations > (uint32_t)INT_MAX) {
        return mk_io_error("zopfli deflate: numIterations too large");
    }

    ZopfliOptions options;
    ZopfliInitOptions(&options);
    options.numiterations = (int)numIterations;

    unsigned char *out = NULL;
    size_t out_len = 0;
    ZopfliCompress(&options, ZOPFLI_FORMAT_DEFLATE, src, src_len, &out, &out_len);

    /* ZopfliCompress always emits at least one deflate block (e.g. an empty
     * stored block for empty input), so out should be non-NULL on success.
     * If the underlying realloc failed, zopfli aborts the process — there is
     * no error-return path. Guard anyway in case of API drift. */
    if (out == NULL) {
        return mk_io_error("zopfli deflate: output buffer is null");
    }

    lean_obj_res result = mk_byte_array(out, out_len);
    free(out);
    return lean_io_result_mk_ok(result);
}
