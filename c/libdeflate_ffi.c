#include <lean/lean.h>
#include <libdeflate.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <stdint.h>
#include <limits.h>

/*
 * libdeflate FFI: raw DEFLATE compress/decompress for Track D ratio/runtime
 * comparison against zlib. Whole-buffer only — libdeflate has no streaming
 * API, which is the comparator-relevant point (zlib leaves room above it).
 *
 * Error wording follows the existing family in c/zlib_ffi.c so callers can
 * `msg.contains "exceeds limit"` (see error-wording-catalogue skill).
 */

static lean_obj_res mk_byte_array(const uint8_t *data, size_t len) {
    lean_obj_res arr = lean_alloc_sarray(1, len, len);
    memcpy(lean_sarray_cptr(arr), data, len);
    return arr;
}

static lean_obj_res mk_io_error(const char *msg) {
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(msg)));
}

/* Translate a libdeflate_result into a human-readable suffix. */
static const char *libdeflate_result_str(enum libdeflate_result r) {
    switch (r) {
        case LIBDEFLATE_SUCCESS:             return "success";
        case LIBDEFLATE_BAD_DATA:             return "bad data";
        case LIBDEFLATE_SHORT_OUTPUT:         return "short output";
        case LIBDEFLATE_INSUFFICIENT_SPACE:   return "insufficient output space";
        default:                              return "unknown";
    }
}

/*
 * lean_libdeflate_compress : @& ByteArray → UInt8 → IO ByteArray
 *
 * Raw DEFLATE compression. `level` ranges 0..12 (libdeflate's range);
 * callers passing zlib-style 0..9 work unchanged because libdeflate
 * accepts the same lower range.
 */
LEAN_EXPORT lean_obj_res lean_libdeflate_compress(b_lean_obj_arg data, uint8_t level, lean_obj_arg _w) {
    const uint8_t *src = lean_sarray_cptr(data);
    size_t src_len = lean_sarray_size(data);

    if (level > 12) {
        return mk_io_error("libdeflate compress: invalid level (must be 0..12)");
    }

    struct libdeflate_compressor *c = libdeflate_alloc_compressor((int)level);
    if (!c) {
        return mk_io_error("libdeflate compress: out of memory or invalid level");
    }

    size_t bound = libdeflate_deflate_compress_bound(c, src_len);
    lean_obj_res arr = lean_alloc_sarray(1, 0, bound);
    uint8_t *dest = lean_sarray_cptr(arr);

    size_t out_len = libdeflate_deflate_compress(c, src, src_len, dest, bound);
    libdeflate_free_compressor(c);
    if (out_len == 0) {
        lean_dec_ref(arr);
        return mk_io_error("libdeflate compress: did not fit into compress_bound buffer");
    }

    lean_sarray_set_size(arr, out_len);
    return lean_io_result_mk_ok(arr);
}

/*
 * lean_libdeflate_decompress : @& ByteArray → UInt64 → IO ByteArray
 *
 * Raw DEFLATE decompression. libdeflate has no streaming API and requires
 * a sized output buffer; we start with a 4× guess and double on
 * LIBDEFLATE_INSUFFICIENT_SPACE, capping at `max_output` (0 = unlimited).
 *
 * Honours `maxDecompressedSize` with the shared "exceeds limit" wording.
 */
LEAN_EXPORT lean_obj_res lean_libdeflate_decompress(b_lean_obj_arg data, uint64_t max_output, lean_obj_arg _w) {
    const uint8_t *src = lean_sarray_cptr(data);
    size_t src_len = lean_sarray_size(data);
    char errbuf[256];

    struct libdeflate_decompressor *d = libdeflate_alloc_decompressor();
    if (!d) {
        return mk_io_error("libdeflate decompress: out of memory");
    }

    size_t buf_size;
    if (src_len <= SIZE_MAX / 4) {
        buf_size = src_len * 4;
        if (buf_size < 1024) buf_size = 1024;
    } else {
        buf_size = src_len;
    }
    if (max_output > 0 && (uint64_t)buf_size > max_output) {
        buf_size = (size_t)max_output;
        if (buf_size == 0) buf_size = 1;
    }

    uint8_t *buf = (uint8_t *)malloc(buf_size);
    if (!buf) {
        libdeflate_free_decompressor(d);
        return mk_io_error("libdeflate decompress: out of memory");
    }

    size_t actual_out = 0;
    enum libdeflate_result r;
    for (;;) {
        r = libdeflate_deflate_decompress(d, src, src_len, buf, buf_size, &actual_out);
        if (r == LIBDEFLATE_SUCCESS) break;
        if (r != LIBDEFLATE_INSUFFICIENT_SPACE) {
            free(buf);
            libdeflate_free_decompressor(d);
            snprintf(errbuf, sizeof(errbuf), "libdeflate decompress: %s", libdeflate_result_str(r));
            return mk_io_error(errbuf);
        }
        /* Insufficient space: double the buffer, but respect max_output. */
        if (max_output > 0 && (uint64_t)buf_size >= max_output) {
            free(buf);
            libdeflate_free_decompressor(d);
            snprintf(errbuf, sizeof(errbuf),
                     "libdeflate decompress: decompressed size exceeds limit (%llu bytes)",
                     (unsigned long long)max_output);
            return mk_io_error(errbuf);
        }
        if (buf_size > SIZE_MAX / 2) {
            free(buf);
            libdeflate_free_decompressor(d);
            return mk_io_error("libdeflate decompress: output buffer overflow");
        }
        size_t new_size = buf_size * 2;
        if (max_output > 0 && (uint64_t)new_size > max_output) {
            new_size = (size_t)max_output;
        }
        uint8_t *newbuf = (uint8_t *)realloc(buf, new_size);
        if (!newbuf) {
            free(buf);
            libdeflate_free_decompressor(d);
            return mk_io_error("libdeflate decompress: out of memory");
        }
        buf = newbuf;
        buf_size = new_size;
    }
    libdeflate_free_decompressor(d);

    if (max_output > 0 && (uint64_t)actual_out > max_output) {
        free(buf);
        snprintf(errbuf, sizeof(errbuf),
                 "libdeflate decompress: decompressed size exceeds limit (%llu bytes)",
                 (unsigned long long)max_output);
        return mk_io_error(errbuf);
    }

    lean_obj_res result = mk_byte_array(buf, actual_out);
    free(buf);
    return lean_io_result_mk_ok(result);
}
