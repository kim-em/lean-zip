#include <lean/lean.h>
#include <zlib.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <stdint.h>

/*
 * Helper: create a Lean ByteArray from a buffer.
 */
static lean_obj_res mk_byte_array(const uint8_t *data, size_t len) {
    lean_obj_res arr = lean_alloc_sarray(1, len, len);
    memcpy(lean_sarray_cptr(arr), data, len);
    return arr;
}

/*
 * Helper: create an IO error result from a formatted string.
 */
static lean_obj_res mk_io_error(const char *msg) {
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(msg)));
}

/*
 * Helper: create an IO error with zlib return code detail.
 */
static lean_obj_res mk_zlib_error(const char *prefix, int ret, const char *zmsg) {
    /* Use zlib's message if available, otherwise zError for the return code */
    const char *detail = zmsg ? zmsg : zError(ret);
    char buf[256];
    snprintf(buf, sizeof(buf), "%s: %s", prefix, detail);
    return mk_io_error(buf);
}

/*
 * Helper: grow a buffer, with overflow check.
 * Returns NULL on overflow or allocation failure. Frees old buffer on failure.
 */
static uint8_t *grow_buffer(uint8_t *buf, size_t *buf_size) {
    if (*buf_size > SIZE_MAX / 2) {
        free(buf);
        return NULL;
    }
    *buf_size *= 2;
    uint8_t *newbuf = (uint8_t *)realloc(buf, *buf_size);
    if (!newbuf) {
        free(buf);
        return NULL;
    }
    return newbuf;
}

/*
 * Helper: compute initial decompression buffer size with overflow guard.
 */
static size_t initial_decompress_buf(size_t src_len) {
    if (src_len <= SIZE_MAX / 4) {
        size_t sz = src_len * 4;
        return sz < 1024 ? 1024 : sz;
    }
    return src_len; /* src_len is already huge, don't multiply */
}

/*
 * Raw deflate compression (zlib format, no gzip header).
 *
 * lean_zlib_compress : @& ByteArray → UInt8 → IO ByteArray
 */
LEAN_EXPORT lean_obj_res lean_zlib_compress(b_lean_obj_arg data, uint8_t level, lean_obj_arg _w) {
    const uint8_t *src = lean_sarray_cptr(data);
    size_t src_len = lean_sarray_size(data);

    uLongf dest_len = compressBound(src_len);
    uint8_t *dest = (uint8_t *)malloc(dest_len);
    if (!dest) {
        return mk_io_error("zlib compress: out of memory");
    }

    int ret = compress2(dest, &dest_len, src, src_len, (int)level);
    if (ret != Z_OK) {
        free(dest);
        return mk_zlib_error("zlib compress", ret, NULL);
    }

    lean_obj_res result = mk_byte_array(dest, dest_len);
    free(dest);
    return lean_io_result_mk_ok(result);
}

/*
 * Raw deflate decompression (zlib format).
 *
 * We don't know the uncompressed size ahead of time, so we grow the buffer.
 *
 * lean_zlib_decompress : @& ByteArray → IO ByteArray
 */
LEAN_EXPORT lean_obj_res lean_zlib_decompress(b_lean_obj_arg data, lean_obj_arg _w) {
    const uint8_t *src = lean_sarray_cptr(data);
    size_t src_len = lean_sarray_size(data);

    z_stream strm;
    memset(&strm, 0, sizeof(strm));
    int ret = inflateInit(&strm);
    if (ret != Z_OK) {
        return mk_zlib_error("zlib decompress: inflateInit", ret, strm.msg);
    }

    strm.next_in = (Bytef *)src;
    strm.avail_in = src_len;

    size_t buf_size = initial_decompress_buf(src_len);
    uint8_t *buf = (uint8_t *)malloc(buf_size);
    if (!buf) {
        inflateEnd(&strm);
        return mk_io_error("zlib decompress: out of memory");
    }
    size_t total = 0;

    do {
        if (total >= buf_size) {
            buf = grow_buffer(buf, &buf_size);
            if (!buf) {
                inflateEnd(&strm);
                return mk_io_error("zlib decompress: out of memory");
            }
        }
        strm.next_out = buf + total;
        strm.avail_out = buf_size - total;
        ret = inflate(&strm, Z_NO_FLUSH);
        if (ret != Z_OK && ret != Z_STREAM_END) {
            free(buf);
            inflateEnd(&strm);
            return mk_zlib_error("zlib decompress", ret, strm.msg);
        }
        total = buf_size - strm.avail_out;
    } while (ret != Z_STREAM_END);

    inflateEnd(&strm);

    lean_obj_res result = mk_byte_array(buf, total);
    free(buf);
    return lean_io_result_mk_ok(result);
}

/*
 * Gzip compression (with gzip header/trailer).
 *
 * Uses deflateInit2 with MAX_WBITS + 16 to produce gzip format.
 *
 * lean_gzip_compress : @& ByteArray → UInt8 → IO ByteArray
 */
LEAN_EXPORT lean_obj_res lean_gzip_compress(b_lean_obj_arg data, uint8_t level, lean_obj_arg _w) {
    const uint8_t *src = lean_sarray_cptr(data);
    size_t src_len = lean_sarray_size(data);

    z_stream strm;
    memset(&strm, 0, sizeof(strm));
    int ret = deflateInit2(&strm, (int)level, Z_DEFLATED, MAX_WBITS + 16, 8, Z_DEFAULT_STRATEGY);
    if (ret != Z_OK) {
        return mk_zlib_error("gzip compress: deflateInit2", ret, strm.msg);
    }

    size_t buf_size = deflateBound(&strm, src_len);
    uint8_t *buf = (uint8_t *)malloc(buf_size);
    if (!buf) {
        deflateEnd(&strm);
        return mk_io_error("gzip compress: out of memory");
    }

    strm.next_in = (Bytef *)src;
    strm.avail_in = src_len;
    strm.next_out = buf;
    strm.avail_out = buf_size;

    ret = deflate(&strm, Z_FINISH);
    if (ret != Z_STREAM_END) {
        free(buf);
        deflateEnd(&strm);
        return mk_zlib_error("gzip compress: deflate", ret, strm.msg);
    }

    size_t out_len = buf_size - strm.avail_out;
    deflateEnd(&strm);

    lean_obj_res result = mk_byte_array(buf, out_len);
    free(buf);
    return lean_io_result_mk_ok(result);
}

/*
 * Gzip decompression (handles gzip header/trailer).
 *
 * Uses inflateInit2 with MAX_WBITS + 32 to auto-detect zlib or gzip format.
 * Handles concatenated gzip streams by resetting inflate after each Z_STREAM_END
 * while input remains.
 *
 * lean_gzip_decompress : @& ByteArray → IO ByteArray
 */
LEAN_EXPORT lean_obj_res lean_gzip_decompress(b_lean_obj_arg data, lean_obj_arg _w) {
    const uint8_t *src = lean_sarray_cptr(data);
    size_t src_len = lean_sarray_size(data);

    z_stream strm;
    memset(&strm, 0, sizeof(strm));
    /* MAX_WBITS + 32 = auto-detect gzip or zlib */
    int ret = inflateInit2(&strm, MAX_WBITS + 32);
    if (ret != Z_OK) {
        return mk_zlib_error("gzip decompress: inflateInit2", ret, strm.msg);
    }

    strm.next_in = (Bytef *)src;
    strm.avail_in = src_len;

    size_t buf_size = initial_decompress_buf(src_len);
    uint8_t *buf = (uint8_t *)malloc(buf_size);
    if (!buf) {
        inflateEnd(&strm);
        return mk_io_error("gzip decompress: out of memory");
    }
    size_t total = 0;

    for (;;) {
        /* Inflate current stream until Z_STREAM_END */
        do {
            if (total >= buf_size) {
                buf = grow_buffer(buf, &buf_size);
                if (!buf) {
                    inflateEnd(&strm);
                    return mk_io_error("gzip decompress: out of memory");
                }
            }
            strm.next_out = buf + total;
            strm.avail_out = buf_size - total;
            ret = inflate(&strm, Z_NO_FLUSH);
            if (ret != Z_OK && ret != Z_STREAM_END) {
                free(buf);
                inflateEnd(&strm);
                return mk_zlib_error("gzip decompress", ret, strm.msg);
            }
            total = buf_size - strm.avail_out;
        } while (ret != Z_STREAM_END);

        /* If no more input, we're done */
        if (strm.avail_in == 0) break;

        /* More input remains: this is a concatenated gzip stream.
         * Reset inflate to process the next member. */
        ret = inflateReset2(&strm, MAX_WBITS + 32);
        if (ret != Z_OK) {
            free(buf);
            inflateEnd(&strm);
            return mk_zlib_error("gzip decompress: inflateReset2", ret, strm.msg);
        }
    }

    inflateEnd(&strm);

    lean_obj_res result = mk_byte_array(buf, total);
    free(buf);
    return lean_io_result_mk_ok(result);
}
