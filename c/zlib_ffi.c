#include <lean/lean.h>
#include <zlib.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <stdint.h>
#include <limits.h>

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

/* ========================================================================
 * Shared compression/decompression helpers
 * ======================================================================== */

/*
 * Shared whole-buffer compression using deflateInit2/deflate/Z_FINISH.
 * Used by gzip and raw deflate; zlib uses the simpler compress2 API.
 */
static lean_obj_res compress_deflate(const char *label, int windowBits,
                                      const uint8_t *src, size_t src_len, int level) {
    char errbuf[256];

    /* Guard against silent truncation: zlib's avail_in is uInt (32-bit) */
    if (src_len > UINT_MAX) {
        snprintf(errbuf, sizeof(errbuf),
                 "%s: input too large for whole-buffer API (%zu bytes > 4GB); use streaming instead",
                 label, src_len);
        return mk_io_error(errbuf);
    }

    z_stream strm;
    memset(&strm, 0, sizeof(strm));
    int ret = deflateInit2(&strm, level, Z_DEFLATED, windowBits, 8, Z_DEFAULT_STRATEGY);
    if (ret != Z_OK) {
        snprintf(errbuf, sizeof(errbuf), "%s: deflateInit2", label);
        return mk_zlib_error(errbuf, ret, strm.msg);
    }

    size_t buf_size = deflateBound(&strm, src_len);
    /* Allocate Lean ByteArray directly — no intermediate copy */
    lean_obj_res arr = lean_alloc_sarray(1, 0, buf_size);
    uint8_t *buf = lean_sarray_cptr(arr);

    strm.next_in = (Bytef *)src;
    strm.avail_in = (uInt)src_len;
    strm.next_out = buf;
    strm.avail_out = (buf_size <= UINT_MAX) ? (uInt)buf_size : UINT_MAX;

    ret = deflate(&strm, Z_FINISH);
    if (ret != Z_STREAM_END) {
        lean_dec_ref(arr);
        deflateEnd(&strm);
        snprintf(errbuf, sizeof(errbuf), "%s: deflate", label);
        return mk_zlib_error(errbuf, ret, strm.msg);
    }

    size_t out_len = buf_size - strm.avail_out;
    deflateEnd(&strm);

    lean_sarray_set_size(arr, out_len);
    return lean_io_result_mk_ok(arr);
}

/*
 * Shared whole-buffer decompression using inflateInit2/inflate.
 * When handle_concat is true, handles concatenated streams (gzip members)
 * by resetting inflate after each Z_STREAM_END while input remains.
 */
static lean_obj_res decompress_inflate(const char *label, int windowBits,
                                        const uint8_t *src, size_t src_len,
                                        int handle_concat, uint64_t max_output) {
    char errbuf[256];

    /* Guard against silent truncation: zlib's avail_in is uInt (32-bit) */
    if (src_len > UINT_MAX) {
        snprintf(errbuf, sizeof(errbuf),
                 "%s: input too large for whole-buffer API (%zu bytes > 4GB); use streaming instead",
                 label, src_len);
        return mk_io_error(errbuf);
    }

    z_stream strm;
    memset(&strm, 0, sizeof(strm));
    int ret = inflateInit2(&strm, windowBits);
    if (ret != Z_OK) {
        snprintf(errbuf, sizeof(errbuf), "%s: inflateInit2", label);
        return mk_zlib_error(errbuf, ret, strm.msg);
    }

    strm.next_in = (Bytef *)src;
    strm.avail_in = (uInt)src_len;

    size_t buf_size = initial_decompress_buf(src_len);
    uint8_t *buf = (uint8_t *)malloc(buf_size);
    if (!buf) {
        inflateEnd(&strm);
        snprintf(errbuf, sizeof(errbuf), "%s: out of memory", label);
        return mk_io_error(errbuf);
    }
    size_t total = 0;

    for (;;) {
        do {
            if (total >= buf_size) {
                buf = grow_buffer(buf, &buf_size);
                if (!buf) {
                    inflateEnd(&strm);
                    snprintf(errbuf, sizeof(errbuf), "%s: out of memory", label);
                    return mk_io_error(errbuf);
                }
            }
            strm.next_out = buf + total;
            size_t avail = buf_size - total;
            uInt avail_out_initial = (avail <= UINT_MAX) ? (uInt)avail : UINT_MAX;
            strm.avail_out = avail_out_initial;
            ret = inflate(&strm, Z_NO_FLUSH);
            if (ret != Z_OK && ret != Z_STREAM_END) {
                free(buf);
                inflateEnd(&strm);
                return mk_zlib_error(label, ret, strm.msg);
            }
            total += (avail_out_initial - strm.avail_out);
            if (max_output > 0 && total > max_output) {
                free(buf);
                inflateEnd(&strm);
                snprintf(errbuf, sizeof(errbuf),
                         "%s: decompressed size exceeds limit (%llu bytes)",
                         label, (unsigned long long)max_output);
                return mk_io_error(errbuf);
            }
        } while (ret != Z_STREAM_END);

        if (!handle_concat || strm.avail_in == 0) break;

        ret = inflateReset(&strm);
        if (ret != Z_OK) {
            free(buf);
            inflateEnd(&strm);
            snprintf(errbuf, sizeof(errbuf), "%s: inflateReset", label);
            return mk_zlib_error(errbuf, ret, strm.msg);
        }
    }

    inflateEnd(&strm);

    lean_obj_res result = mk_byte_array(buf, total);
    free(buf);
    return lean_io_result_mk_ok(result);
}

/* ========================================================================
 * Whole-buffer compression/decompression
 * ======================================================================== */

/*
 * Zlib compression (uses the simpler compress2 API).
 *
 * lean_zlib_compress : @& ByteArray → UInt8 → IO ByteArray
 */
LEAN_EXPORT lean_obj_res lean_zlib_compress(b_lean_obj_arg data, uint8_t level, lean_obj_arg _w) {
    const uint8_t *src = lean_sarray_cptr(data);
    size_t src_len = lean_sarray_size(data);

    /* Guard: compress2 internally uses uInt for avail_in */
    if (src_len > UINT_MAX) {
        return mk_io_error("zlib compress: input too large for whole-buffer API (> 4GB); use streaming instead");
    }

    uLongf dest_len = compressBound(src_len);
    /* Allocate Lean ByteArray directly — no intermediate copy */
    lean_obj_res arr = lean_alloc_sarray(1, 0, dest_len);
    uint8_t *dest = lean_sarray_cptr(arr);

    int ret = compress2(dest, &dest_len, src, src_len, (int)level);
    if (ret != Z_OK) {
        lean_dec_ref(arr);
        return mk_zlib_error("zlib compress", ret, NULL);
    }

    lean_sarray_set_size(arr, dest_len);
    return lean_io_result_mk_ok(arr);
}

/* lean_zlib_decompress : @& ByteArray → UInt64 → IO ByteArray */
LEAN_EXPORT lean_obj_res lean_zlib_decompress(b_lean_obj_arg data, uint64_t max_output, lean_obj_arg _w) {
    return decompress_inflate("zlib decompress", MAX_WBITS,
                               lean_sarray_cptr(data), lean_sarray_size(data), 0, max_output);
}

/* lean_gzip_compress : @& ByteArray → UInt8 → IO ByteArray */
LEAN_EXPORT lean_obj_res lean_gzip_compress(b_lean_obj_arg data, uint8_t level, lean_obj_arg _w) {
    return compress_deflate("gzip compress", MAX_WBITS + 16,
                             lean_sarray_cptr(data), lean_sarray_size(data), (int)level);
}

/* lean_gzip_decompress : @& ByteArray → UInt64 → IO ByteArray (handles concatenated members) */
LEAN_EXPORT lean_obj_res lean_gzip_decompress(b_lean_obj_arg data, uint64_t max_output, lean_obj_arg _w) {
    return decompress_inflate("gzip decompress", MAX_WBITS + 32,
                               lean_sarray_cptr(data), lean_sarray_size(data), 1, max_output);
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

    size_t chunk_len = lean_sarray_size(chunk);
    if (chunk_len > UINT_MAX)
        return mk_io_error("gzip deflate push: chunk too large (> 4GB)");
    s->strm.next_in = (Bytef *)lean_sarray_cptr(chunk);
    s->strm.avail_in = (uInt)chunk_len;

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
        size_t avail = buf_size - total;
        uInt avail_out_initial = (avail <= UINT_MAX) ? (uInt)avail : UINT_MAX;
        s->strm.avail_out = avail_out_initial;
        ret = deflate(&s->strm, Z_NO_FLUSH);
        if (ret != Z_OK && ret != Z_BUF_ERROR) {
            free(buf);
            return mk_zlib_error("gzip deflate push", ret, s->strm.msg);
        }
        total += (avail_out_initial - s->strm.avail_out);
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
        size_t avail = buf_size - total;
        uInt avail_out_initial = (avail <= UINT_MAX) ? (uInt)avail : UINT_MAX;
        s->strm.avail_out = avail_out_initial;
        ret = deflate(&s->strm, Z_FINISH);
        if (ret != Z_OK && ret != Z_STREAM_END) {
            free(buf);
            return mk_zlib_error("gzip deflate finish", ret, s->strm.msg);
        }
        total += (avail_out_initial - s->strm.avail_out);
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

    size_t chunk_len = lean_sarray_size(chunk);
    if (chunk_len > UINT_MAX)
        return mk_io_error("gzip inflate push: chunk too large (> 4GB)");
    s->strm.next_in = (Bytef *)lean_sarray_cptr(chunk);
    s->strm.avail_in = (uInt)chunk_len;

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
            size_t avail = buf_size - total;
            uInt avail_out_initial = (avail <= UINT_MAX) ? (uInt)avail : UINT_MAX;
            s->strm.avail_out = avail_out_initial;
            ret = inflate(&s->strm, Z_NO_FLUSH);
            if (ret != Z_OK && ret != Z_STREAM_END && ret != Z_BUF_ERROR) {
                free(buf);
                return mk_zlib_error("gzip inflate push", ret, s->strm.msg);
            }
            total += (avail_out_initial - s->strm.avail_out);
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
 * Pure function — no IO.
 *
 * lean_zlib_crc32 : UInt32 → @& ByteArray → UInt32
 */
LEAN_EXPORT uint32_t lean_zlib_crc32(uint32_t init, b_lean_obj_arg data) {
    const uint8_t *src = lean_sarray_cptr(data);
    size_t remaining = lean_sarray_size(data);
    uint32_t crc = init;
    /* Loop over UINT_MAX-sized chunks: zlib's crc32 takes uInt length */
    while (remaining > 0) {
        uInt chunk = (remaining > UINT_MAX) ? UINT_MAX : (uInt)remaining;
        crc = crc32(crc, src, chunk);
        src += chunk;
        remaining -= chunk;
    }
    return crc;
}

/*
 * Adler32 checksum (incremental). Initial value should be 1.
 * Pure function — no IO.
 *
 * lean_zlib_adler32 : UInt32 → @& ByteArray → UInt32
 */
LEAN_EXPORT uint32_t lean_zlib_adler32(uint32_t init, b_lean_obj_arg data) {
    const uint8_t *src = lean_sarray_cptr(data);
    size_t remaining = lean_sarray_size(data);
    uint32_t a = init;
    while (remaining > 0) {
        uInt chunk = (remaining > UINT_MAX) ? UINT_MAX : (uInt)remaining;
        a = adler32(a, src, chunk);
        src += chunk;
        remaining -= chunk;
    }
    return a;
}

/* ========================================================================
 * Raw deflate (no header/trailer, used by ZIP format)
 * ======================================================================== */

/* lean_raw_deflate_compress : @& ByteArray → UInt8 → IO ByteArray */
LEAN_EXPORT lean_obj_res lean_raw_deflate_compress(b_lean_obj_arg data, uint8_t level, lean_obj_arg _w) {
    return compress_deflate("raw deflate compress", -MAX_WBITS,
                             lean_sarray_cptr(data), lean_sarray_size(data), (int)level);
}

/* lean_raw_deflate_decompress : @& ByteArray → UInt64 → IO ByteArray */
LEAN_EXPORT lean_obj_res lean_raw_deflate_decompress(b_lean_obj_arg data, uint64_t max_output, lean_obj_arg _w) {
    return decompress_inflate("raw deflate decompress", -MAX_WBITS,
                               lean_sarray_cptr(data), lean_sarray_size(data), 0, max_output);
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
