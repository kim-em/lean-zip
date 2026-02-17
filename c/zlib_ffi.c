#include <lean/lean.h>
#include <zlib.h>
#include <stdlib.h>
#include <string.h>

/*
 * Helper: create a Lean ByteArray from a buffer.
 */
static lean_obj_res mk_byte_array(const uint8_t *data, size_t len) {
    lean_obj_res arr = lean_alloc_sarray(1, len, len);
    memcpy(lean_sarray_cptr(arr), data, len);
    return arr;
}

/*
 * Helper: create an IO error result from a string.
 */
static lean_obj_res mk_io_error(const char *msg) {
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(msg)));
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
        const char *msg = ret == Z_MEM_ERROR ? "zlib compress: out of memory"
                        : ret == Z_BUF_ERROR ? "zlib compress: buffer too small"
                        : ret == Z_STREAM_ERROR ? "zlib compress: invalid compression level"
                        : "zlib compress: unknown error";
        return mk_io_error(msg);
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
    /* inflateInit for zlib format */
    int ret = inflateInit(&strm);
    if (ret != Z_OK) {
        return mk_io_error("zlib decompress: inflateInit failed");
    }

    strm.next_in = (Bytef *)src;
    strm.avail_in = src_len;

    size_t buf_size = src_len * 4;
    if (buf_size < 1024) buf_size = 1024;
    uint8_t *buf = (uint8_t *)malloc(buf_size);
    if (!buf) {
        inflateEnd(&strm);
        return mk_io_error("zlib decompress: out of memory");
    }
    size_t total = 0;

    do {
        if (total >= buf_size) {
            buf_size *= 2;
            uint8_t *newbuf = (uint8_t *)realloc(buf, buf_size);
            if (!newbuf) {
                free(buf);
                inflateEnd(&strm);
                return mk_io_error("zlib decompress: out of memory");
            }
            buf = newbuf;
        }
        strm.next_out = buf + total;
        strm.avail_out = buf_size - total;
        ret = inflate(&strm, Z_NO_FLUSH);
        if (ret != Z_OK && ret != Z_STREAM_END) {
            free(buf);
            inflateEnd(&strm);
            const char *msg = strm.msg ? strm.msg : "zlib decompress: inflate failed";
            return mk_io_error(msg);
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
    /* MAX_WBITS + 16 = gzip format */
    int ret = deflateInit2(&strm, (int)level, Z_DEFLATED, MAX_WBITS + 16, 8, Z_DEFAULT_STRATEGY);
    if (ret != Z_OK) {
        return mk_io_error("gzip compress: deflateInit2 failed");
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
        return mk_io_error("gzip compress: deflate failed");
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
 * Uses inflateInit2 with MAX_WBITS + 16 for gzip format.
 * Also handles concatenated gzip streams.
 *
 * lean_gzip_decompress : @& ByteArray → IO ByteArray
 */
LEAN_EXPORT lean_obj_res lean_gzip_decompress(b_lean_obj_arg data, lean_obj_arg _w) {
    const uint8_t *src = lean_sarray_cptr(data);
    size_t src_len = lean_sarray_size(data);

    z_stream strm;
    memset(&strm, 0, sizeof(strm));
    /* MAX_WBITS + 16 = gzip format (auto-detect also works with +32) */
    int ret = inflateInit2(&strm, MAX_WBITS + 32);
    if (ret != Z_OK) {
        return mk_io_error("gzip decompress: inflateInit2 failed");
    }

    strm.next_in = (Bytef *)src;
    strm.avail_in = src_len;

    size_t buf_size = src_len * 4;
    if (buf_size < 1024) buf_size = 1024;
    uint8_t *buf = (uint8_t *)malloc(buf_size);
    if (!buf) {
        inflateEnd(&strm);
        return mk_io_error("gzip decompress: out of memory");
    }
    size_t total = 0;

    do {
        if (total >= buf_size) {
            buf_size *= 2;
            uint8_t *newbuf = (uint8_t *)realloc(buf, buf_size);
            if (!newbuf) {
                free(buf);
                inflateEnd(&strm);
                return mk_io_error("gzip decompress: out of memory");
            }
            buf = newbuf;
        }
        strm.next_out = buf + total;
        strm.avail_out = buf_size - total;
        ret = inflate(&strm, Z_NO_FLUSH);
        if (ret != Z_OK && ret != Z_STREAM_END) {
            free(buf);
            inflateEnd(&strm);
            const char *msg = strm.msg ? strm.msg : "gzip decompress: inflate failed";
            return mk_io_error(msg);
        }
        total = buf_size - strm.avail_out;
    } while (ret != Z_STREAM_END);

    inflateEnd(&strm);

    lean_obj_res result = mk_byte_array(buf, total);
    free(buf);
    return lean_io_result_mk_ok(result);
}
