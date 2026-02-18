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
         * Reset inflate to process the next member (preserves window bits
         * from the original inflateInit2). */
        ret = inflateReset(&strm);
        if (ret != Z_OK) {
            free(buf);
            inflateEnd(&strm);
            return mk_zlib_error("gzip decompress: inflateReset", ret, strm.msg);
        }
    }

    inflateEnd(&strm);

    lean_obj_res result = mk_byte_array(buf, total);
    free(buf);
    return lean_io_result_mk_ok(result);
}

/* ========================================================================
 * Streaming compression/decompression via external objects
 * ======================================================================== */

#include <pthread.h>

typedef struct {
    z_stream strm;
    int      finished;  /* 1 after deflateEnd/inflateEnd has been called */
} deflate_state;

typedef struct {
    z_stream strm;
    int      finished;
} inflate_state;

static lean_external_class *g_deflate_class = NULL;
static lean_external_class *g_inflate_class = NULL;
static pthread_once_t g_classes_once = PTHREAD_ONCE_INIT;

static void noop_foreach(void *p, b_lean_obj_arg f) { (void)p; (void)f; }

static void deflate_finalizer(void *p) {
    deflate_state *s = (deflate_state *)p;
    if (!s->finished) deflateEnd(&s->strm);
    free(s);
}

static void inflate_finalizer(void *p) {
    inflate_state *s = (inflate_state *)p;
    if (!s->finished) inflateEnd(&s->strm);
    free(s);
}

static void register_classes(void) {
    g_deflate_class = lean_register_external_class(deflate_finalizer, noop_foreach);
    g_inflate_class = lean_register_external_class(inflate_finalizer, noop_foreach);
}

static void ensure_classes(void) {
    pthread_once(&g_classes_once, register_classes);
}

/*
 * Create a new gzip deflate (compression) state.
 *
 * lean_gzip_deflate_new : UInt8 → IO DeflateState
 */
LEAN_EXPORT lean_obj_res lean_gzip_deflate_new(uint8_t level, lean_obj_arg _w) {
    ensure_classes();
    deflate_state *s = (deflate_state *)calloc(1, sizeof(deflate_state));
    if (!s) return mk_io_error("gzip deflate new: out of memory");

    int ret = deflateInit2(&s->strm, (int)level, Z_DEFLATED, MAX_WBITS + 16, 8, Z_DEFAULT_STRATEGY);
    if (ret != Z_OK) {
        const char *msg = s->strm.msg;
        free(s);
        return mk_zlib_error("gzip deflate new", ret, msg);
    }

    return lean_io_result_mk_ok(lean_alloc_external(g_deflate_class, s));
}

/*
 * Push a chunk of data through the deflate stream (Z_NO_FLUSH).
 * Loops until all input is consumed.
 * Returns compressed output produced so far.
 *
 * lean_gzip_deflate_push : @& DeflateState → @& ByteArray → IO ByteArray
 */
LEAN_EXPORT lean_obj_res lean_gzip_deflate_push(b_lean_obj_arg state_obj,
                                                 b_lean_obj_arg chunk,
                                                 lean_obj_arg _w) {
    deflate_state *s = (deflate_state *)lean_get_external_data(state_obj);
    if (s->finished) return mk_io_error("gzip deflate push: stream already finished");

    s->strm.next_in = (Bytef *)lean_sarray_cptr(chunk);
    s->strm.avail_in = lean_sarray_size(chunk);

    size_t buf_size = 65536;
    uint8_t *buf = (uint8_t *)malloc(buf_size);
    if (!buf) return mk_io_error("gzip deflate push: out of memory");
    size_t total = 0;

    /* Loop until all input is consumed */
    int ret;
    while (s->strm.avail_in > 0) {
        if (total >= buf_size) {
            buf = grow_buffer(buf, &buf_size);
            if (!buf) return mk_io_error("gzip deflate push: out of memory");
        }
        s->strm.next_out = buf + total;
        s->strm.avail_out = buf_size - total;
        ret = deflate(&s->strm, Z_NO_FLUSH);
        if (ret != Z_OK && ret != Z_BUF_ERROR) {
            free(buf);
            return mk_zlib_error("gzip deflate push", ret, s->strm.msg);
        }
        total = buf_size - s->strm.avail_out;
    }

    lean_obj_res result = mk_byte_array(buf, total);
    free(buf);
    return lean_io_result_mk_ok(result);
}

/*
 * Finish the deflate stream: flush remaining data with Z_FINISH and clean up.
 * Loops until Z_STREAM_END.
 *
 * lean_gzip_deflate_finish : @& DeflateState → IO ByteArray
 */
LEAN_EXPORT lean_obj_res lean_gzip_deflate_finish(b_lean_obj_arg state_obj, lean_obj_arg _w) {
    deflate_state *s = (deflate_state *)lean_get_external_data(state_obj);
    if (s->finished) {
        return lean_io_result_mk_ok(lean_alloc_sarray(1, 0, 0));
    }

    s->strm.next_in = NULL;
    s->strm.avail_in = 0;

    size_t buf_size = 65536;
    uint8_t *buf = (uint8_t *)malloc(buf_size);
    if (!buf) return mk_io_error("gzip deflate finish: out of memory");
    size_t total = 0;

    int ret;
    do {
        if (total >= buf_size) {
            buf = grow_buffer(buf, &buf_size);
            if (!buf) return mk_io_error("gzip deflate finish: out of memory");
        }
        s->strm.next_out = buf + total;
        s->strm.avail_out = buf_size - total;
        ret = deflate(&s->strm, Z_FINISH);
        if (ret != Z_OK && ret != Z_STREAM_END) {
            free(buf);
            return mk_zlib_error("gzip deflate finish", ret, s->strm.msg);
        }
        total = buf_size - s->strm.avail_out;
    } while (ret != Z_STREAM_END);

    deflateEnd(&s->strm);
    s->finished = 1;

    lean_obj_res result = mk_byte_array(buf, total);
    free(buf);
    return lean_io_result_mk_ok(result);
}

/*
 * Create a new gzip inflate (decompression) state.
 * Uses MAX_WBITS + 32 for auto-detect of gzip/zlib format.
 *
 * lean_gzip_inflate_new : IO InflateState
 */
LEAN_EXPORT lean_obj_res lean_gzip_inflate_new(lean_obj_arg _w) {
    ensure_classes();
    inflate_state *s = (inflate_state *)calloc(1, sizeof(inflate_state));
    if (!s) return mk_io_error("gzip inflate new: out of memory");

    int ret = inflateInit2(&s->strm, MAX_WBITS + 32);
    if (ret != Z_OK) {
        const char *msg = s->strm.msg;
        free(s);
        return mk_zlib_error("gzip inflate new", ret, msg);
    }

    return lean_io_result_mk_ok(lean_alloc_external(g_inflate_class, s));
}

/*
 * Push a chunk of compressed data through the inflate stream.
 * Handles concatenated gzip streams via inflateReset.
 * Returns decompressed output.
 *
 * lean_gzip_inflate_push : @& InflateState → @& ByteArray → IO ByteArray
 */
LEAN_EXPORT lean_obj_res lean_gzip_inflate_push(b_lean_obj_arg state_obj,
                                                 b_lean_obj_arg chunk,
                                                 lean_obj_arg _w) {
    inflate_state *s = (inflate_state *)lean_get_external_data(state_obj);
    if (s->finished) return mk_io_error("gzip inflate push: stream already finished");

    s->strm.next_in = (Bytef *)lean_sarray_cptr(chunk);
    s->strm.avail_in = lean_sarray_size(chunk);

    size_t buf_size = 65536;
    uint8_t *buf = (uint8_t *)malloc(buf_size);
    if (!buf) return mk_io_error("gzip inflate push: out of memory");
    size_t total = 0;

    while (s->strm.avail_in > 0) {
        size_t prev_avail_in = s->strm.avail_in;
        size_t prev_total = total;
        int ret;

        do {
            if (total >= buf_size) {
                buf = grow_buffer(buf, &buf_size);
                if (!buf) return mk_io_error("gzip inflate push: out of memory");
            }
            s->strm.next_out = buf + total;
            s->strm.avail_out = buf_size - total;
            ret = inflate(&s->strm, Z_NO_FLUSH);
            if (ret != Z_OK && ret != Z_STREAM_END && ret != Z_BUF_ERROR) {
                free(buf);
                return mk_zlib_error("gzip inflate push", ret, s->strm.msg);
            }
            total = buf_size - s->strm.avail_out;
        } while (ret != Z_STREAM_END && s->strm.avail_in > 0 && s->strm.avail_out == 0);

        if (ret == Z_STREAM_END) {
            if (s->strm.avail_in == 0) {
                /* Clean end of stream — mark finished */
                inflateEnd(&s->strm);
                s->finished = 1;
                break;
            }
            /* Concatenated gzip: reset for next member */
            ret = inflateReset(&s->strm);
            if (ret != Z_OK) {
                free(buf);
                return mk_zlib_error("gzip inflate push: inflateReset", ret, s->strm.msg);
            }
        } else {
            /* No progress guard: detect stalls to prevent infinite loops */
            if (s->strm.avail_in == prev_avail_in && total == prev_total) {
                break;  /* No progress made — need more input or output */
            }
            if (s->strm.avail_in > 0 && s->strm.avail_out > 0) {
                break;  /* inflate didn't consume input and has output space — needs more data */
            }
        }
    }

    lean_obj_res result = mk_byte_array(buf, total);
    free(buf);
    return lean_io_result_mk_ok(result);
}

/*
 * Finish the inflate stream. Cleans up the zlib state.
 *
 * lean_gzip_inflate_finish : @& InflateState → IO ByteArray
 */
LEAN_EXPORT lean_obj_res lean_gzip_inflate_finish(b_lean_obj_arg state_obj, lean_obj_arg _w) {
    inflate_state *s = (inflate_state *)lean_get_external_data(state_obj);
    if (s->finished) {
        return lean_io_result_mk_ok(lean_alloc_sarray(1, 0, 0));
    }

    inflateEnd(&s->strm);
    s->finished = 1;

    return lean_io_result_mk_ok(lean_alloc_sarray(1, 0, 0));
}

/* ========================================================================
 * Checksums
 * ======================================================================== */

/*
 * CRC32 checksum (incremental). Initial value should be 0.
 *
 * lean_zlib_crc32 : UInt32 → @& ByteArray → IO UInt32
 */
LEAN_EXPORT lean_obj_res lean_zlib_crc32(uint32_t init, b_lean_obj_arg data, lean_obj_arg _w) {
    const uint8_t *src = lean_sarray_cptr(data);
    size_t src_len = lean_sarray_size(data);
    uint32_t result = crc32(init, src, src_len);
    return lean_io_result_mk_ok(lean_box_uint32(result));
}

/*
 * Adler32 checksum (incremental). Initial value should be 1.
 *
 * lean_zlib_adler32 : UInt32 → @& ByteArray → IO UInt32
 */
LEAN_EXPORT lean_obj_res lean_zlib_adler32(uint32_t init, b_lean_obj_arg data, lean_obj_arg _w) {
    const uint8_t *src = lean_sarray_cptr(data);
    size_t src_len = lean_sarray_size(data);
    uint32_t result = adler32(init, src, src_len);
    return lean_io_result_mk_ok(lean_box_uint32(result));
}

/* ========================================================================
 * Raw deflate (no header/trailer, used by ZIP format)
 * ======================================================================== */

/*
 * Raw deflate compression.
 *
 * lean_raw_deflate_compress : @& ByteArray → UInt8 → IO ByteArray
 */
LEAN_EXPORT lean_obj_res lean_raw_deflate_compress(b_lean_obj_arg data, uint8_t level, lean_obj_arg _w) {
    const uint8_t *src = lean_sarray_cptr(data);
    size_t src_len = lean_sarray_size(data);

    z_stream strm;
    memset(&strm, 0, sizeof(strm));
    int ret = deflateInit2(&strm, (int)level, Z_DEFLATED, -MAX_WBITS, 8, Z_DEFAULT_STRATEGY);
    if (ret != Z_OK) {
        return mk_zlib_error("raw deflate compress: deflateInit2", ret, strm.msg);
    }

    size_t buf_size = deflateBound(&strm, src_len);
    uint8_t *buf = (uint8_t *)malloc(buf_size);
    if (!buf) {
        deflateEnd(&strm);
        return mk_io_error("raw deflate compress: out of memory");
    }

    strm.next_in = (Bytef *)src;
    strm.avail_in = src_len;
    strm.next_out = buf;
    strm.avail_out = buf_size;

    ret = deflate(&strm, Z_FINISH);
    if (ret != Z_STREAM_END) {
        free(buf);
        deflateEnd(&strm);
        return mk_zlib_error("raw deflate compress: deflate", ret, strm.msg);
    }

    size_t out_len = buf_size - strm.avail_out;
    deflateEnd(&strm);

    lean_obj_res result = mk_byte_array(buf, out_len);
    free(buf);
    return lean_io_result_mk_ok(result);
}

/*
 * Raw deflate decompression.
 *
 * lean_raw_deflate_decompress : @& ByteArray → IO ByteArray
 */
LEAN_EXPORT lean_obj_res lean_raw_deflate_decompress(b_lean_obj_arg data, lean_obj_arg _w) {
    const uint8_t *src = lean_sarray_cptr(data);
    size_t src_len = lean_sarray_size(data);

    z_stream strm;
    memset(&strm, 0, sizeof(strm));
    int ret = inflateInit2(&strm, -MAX_WBITS);
    if (ret != Z_OK) {
        return mk_zlib_error("raw deflate decompress: inflateInit2", ret, strm.msg);
    }

    strm.next_in = (Bytef *)src;
    strm.avail_in = src_len;

    size_t buf_size = initial_decompress_buf(src_len);
    uint8_t *buf = (uint8_t *)malloc(buf_size);
    if (!buf) {
        inflateEnd(&strm);
        return mk_io_error("raw deflate decompress: out of memory");
    }
    size_t total = 0;

    do {
        if (total >= buf_size) {
            buf = grow_buffer(buf, &buf_size);
            if (!buf) {
                inflateEnd(&strm);
                return mk_io_error("raw deflate decompress: out of memory");
            }
        }
        strm.next_out = buf + total;
        strm.avail_out = buf_size - total;
        ret = inflate(&strm, Z_NO_FLUSH);
        if (ret != Z_OK && ret != Z_STREAM_END) {
            free(buf);
            inflateEnd(&strm);
            return mk_zlib_error("raw deflate decompress", ret, strm.msg);
        }
        total = buf_size - strm.avail_out;
    } while (ret != Z_STREAM_END);

    inflateEnd(&strm);

    lean_obj_res result = mk_byte_array(buf, total);
    free(buf);
    return lean_io_result_mk_ok(result);
}

/*
 * Create a new raw deflate streaming compression state.
 * Uses -MAX_WBITS for raw deflate (no header/trailer).
 *
 * lean_raw_deflate_new : UInt8 → IO DeflateState
 */
LEAN_EXPORT lean_obj_res lean_raw_deflate_new(uint8_t level, lean_obj_arg _w) {
    ensure_classes();
    deflate_state *s = (deflate_state *)calloc(1, sizeof(deflate_state));
    if (!s) return mk_io_error("raw deflate new: out of memory");

    int ret = deflateInit2(&s->strm, (int)level, Z_DEFLATED, -MAX_WBITS, 8, Z_DEFAULT_STRATEGY);
    if (ret != Z_OK) {
        const char *msg = s->strm.msg;
        free(s);
        return mk_zlib_error("raw deflate new", ret, msg);
    }

    return lean_io_result_mk_ok(lean_alloc_external(g_deflate_class, s));
}

/*
 * Create a new raw inflate streaming decompression state.
 * Uses -MAX_WBITS for raw deflate (no header/trailer).
 *
 * lean_raw_inflate_new : IO InflateState
 */
LEAN_EXPORT lean_obj_res lean_raw_inflate_new(lean_obj_arg _w) {
    ensure_classes();
    inflate_state *s = (inflate_state *)calloc(1, sizeof(inflate_state));
    if (!s) return mk_io_error("raw inflate new: out of memory");

    int ret = inflateInit2(&s->strm, -MAX_WBITS);
    if (ret != Z_OK) {
        const char *msg = s->strm.msg;
        free(s);
        return mk_zlib_error("raw inflate new", ret, msg);
    }

    return lean_io_result_mk_ok(lean_alloc_external(g_inflate_class, s));
}
