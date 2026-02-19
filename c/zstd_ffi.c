#include <lean/lean.h>
#include <zstd.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <pthread.h>

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
 * Helper: create an IO error with zstd error detail.
 */
static lean_obj_res mk_zstd_error(const char *prefix, size_t code) {
    char buf[256];
    snprintf(buf, sizeof(buf), "%s: %s", prefix, ZSTD_getErrorName(code));
    return mk_io_error(buf);
}

/*
 * Whole-buffer Zstd compression.
 *
 * lean_zstd_compress : @& ByteArray → UInt8 → IO ByteArray
 */
LEAN_EXPORT lean_obj_res lean_zstd_compress(b_lean_obj_arg data, uint8_t level, lean_obj_arg _w) {
    const uint8_t *src = lean_sarray_cptr(data);
    size_t src_len = lean_sarray_size(data);

    size_t dest_cap = ZSTD_compressBound(src_len);
    /* Allocate Lean ByteArray directly — no intermediate copy */
    lean_obj_res arr = lean_alloc_sarray(1, 0, dest_cap);
    uint8_t *dest = lean_sarray_cptr(arr);

    size_t result = ZSTD_compress(dest, dest_cap, src, src_len, (int)level);
    if (ZSTD_isError(result)) {
        lean_obj_res err = mk_zstd_error("zstd compress", result);
        lean_dec_ref(arr);
        return err;
    }

    lean_sarray_set_size(arr, result);
    return lean_io_result_mk_ok(arr);
}

/*
 * Whole-buffer Zstd decompression.
 *
 * lean_zstd_decompress : @& ByteArray → IO ByteArray
 */
LEAN_EXPORT lean_obj_res lean_zstd_decompress(b_lean_obj_arg data, uint64_t max_output, lean_obj_arg _w) {
    const uint8_t *src = lean_sarray_cptr(data);
    size_t src_len = lean_sarray_size(data);
    char errbuf[256];

    /* Try to get frame content size for optimal allocation */
    unsigned long long frame_size = ZSTD_getFrameContentSize(src, src_len);

    if (frame_size == ZSTD_CONTENTSIZE_ERROR) {
        return mk_io_error("zstd decompress: not a valid zstd frame");
    }

    /* Early reject if known size exceeds limit */
    if (max_output > 0 && frame_size != ZSTD_CONTENTSIZE_UNKNOWN && frame_size > max_output) {
        snprintf(errbuf, sizeof(errbuf),
                 "zstd decompress: decompressed size exceeds limit (%llu bytes)",
                 (unsigned long long)max_output);
        return mk_io_error(errbuf);
    }

    if (frame_size != ZSTD_CONTENTSIZE_UNKNOWN && frame_size <= (1ULL << 31)) {
        /* Known size: single-shot decompress */
        size_t dest_cap = (size_t)frame_size;
        uint8_t *dest = (uint8_t *)malloc(dest_cap);
        if (!dest) return mk_io_error("zstd decompress: out of memory");

        size_t result = ZSTD_decompress(dest, dest_cap, src, src_len);
        if (ZSTD_isError(result)) {
            lean_obj_res err = mk_zstd_error("zstd decompress", result);
            free(dest);
            return err;
        }

        lean_obj_res arr = mk_byte_array(dest, result);
        free(dest);
        return lean_io_result_mk_ok(arr);
    }

    /* Unknown or very large size: streaming decompress with growable buffer */
    ZSTD_DStream *dstream = ZSTD_createDStream();
    if (!dstream) return mk_io_error("zstd decompress: failed to create DStream");

    size_t init_result = ZSTD_initDStream(dstream);
    if (ZSTD_isError(init_result)) {
        lean_obj_res err = mk_zstd_error("zstd decompress init", init_result);
        ZSTD_freeDStream(dstream);
        return err;
    }

    size_t buf_size;
    if (src_len <= SIZE_MAX / 4) {
        buf_size = src_len * 4;
        if (buf_size < 65536) buf_size = 65536;
    } else {
        buf_size = src_len;  /* already huge, don't multiply */
    }
    uint8_t *buf = (uint8_t *)malloc(buf_size);
    if (!buf) {
        ZSTD_freeDStream(dstream);
        return mk_io_error("zstd decompress: out of memory");
    }
    size_t total = 0;

    ZSTD_inBuffer input = { src, src_len, 0 };
    while (input.pos < input.size) {
        ZSTD_outBuffer output = { buf + total, buf_size - total, 0 };
        size_t ret = ZSTD_decompressStream(dstream, &output, &input);
        if (ZSTD_isError(ret)) {
            lean_obj_res err = mk_zstd_error("zstd decompress stream", ret);
            free(buf);
            ZSTD_freeDStream(dstream);
            return err;
        }
        total += output.pos;
        if (max_output > 0 && total > max_output) {
            free(buf);
            ZSTD_freeDStream(dstream);
            snprintf(errbuf, sizeof(errbuf),
                     "zstd decompress: decompressed size exceeds limit (%llu bytes)",
                     (unsigned long long)max_output);
            return mk_io_error(errbuf);
        }
        if (total >= buf_size) {
            if (buf_size > SIZE_MAX / 2) {
                free(buf);
                ZSTD_freeDStream(dstream);
                return mk_io_error("zstd decompress: output too large");
            }
            buf_size *= 2;
            uint8_t *newbuf = (uint8_t *)realloc(buf, buf_size);
            if (!newbuf) {
                free(buf);
                ZSTD_freeDStream(dstream);
                return mk_io_error("zstd decompress: out of memory");
            }
            buf = newbuf;
        }
    }

    ZSTD_freeDStream(dstream);
    lean_obj_res arr = mk_byte_array(buf, total);
    free(buf);
    return lean_io_result_mk_ok(arr);
}

/* ======== Streaming state types ======== */

typedef struct {
    ZSTD_CStream *cstream;
    int finished;
} zstd_compress_state;

typedef struct {
    ZSTD_DStream *dstream;
    int finished;
} zstd_decompress_state;

static lean_external_class *g_zstd_compress_class = NULL;
static lean_external_class *g_zstd_decompress_class = NULL;
static pthread_once_t g_zstd_classes_once = PTHREAD_ONCE_INIT;

static void noop_foreach(void *mod, b_lean_obj_arg fn) {
    (void)mod; (void)fn;
}

static void zstd_compress_finalizer(void *p) {
    zstd_compress_state *s = (zstd_compress_state *)p;
    if (s->cstream) ZSTD_freeCStream(s->cstream);
    free(s);
}

static void zstd_decompress_finalizer(void *p) {
    zstd_decompress_state *s = (zstd_decompress_state *)p;
    if (s->dstream) ZSTD_freeDStream(s->dstream);
    free(s);
}

static void register_zstd_classes(void) {
    g_zstd_compress_class = lean_register_external_class(zstd_compress_finalizer, noop_foreach);
    g_zstd_decompress_class = lean_register_external_class(zstd_decompress_finalizer, noop_foreach);
}

static void ensure_zstd_classes(void) {
    pthread_once(&g_zstd_classes_once, register_zstd_classes);
}

/* ======== Streaming compression ======== */

/*
 * Create a new Zstd compression stream.
 *
 * lean_zstd_compress_new : UInt8 → IO ZstdCompressState
 */
LEAN_EXPORT lean_obj_res lean_zstd_compress_new(uint8_t level, lean_obj_arg _w) {
    ensure_zstd_classes();
    zstd_compress_state *s = (zstd_compress_state *)calloc(1, sizeof(zstd_compress_state));
    if (!s) return mk_io_error("zstd compress new: out of memory");

    s->cstream = ZSTD_createCStream();
    if (!s->cstream) {
        free(s);
        return mk_io_error("zstd compress new: failed to create CStream");
    }

    size_t ret = ZSTD_initCStream(s->cstream, (int)level);
    if (ZSTD_isError(ret)) {
        lean_obj_res err = mk_zstd_error("zstd compress new", ret);
        ZSTD_freeCStream(s->cstream);
        free(s);
        return err;
    }

    return lean_io_result_mk_ok(lean_alloc_external(g_zstd_compress_class, s));
}

/*
 * Push data through the compression stream.
 *
 * lean_zstd_compress_push : @& ZstdCompressState → @& ByteArray → IO ByteArray
 */
LEAN_EXPORT lean_obj_res lean_zstd_compress_push(b_lean_obj_arg state_obj,
                                                   b_lean_obj_arg chunk,
                                                   lean_obj_arg _w) {
    zstd_compress_state *s = (zstd_compress_state *)lean_get_external_data(state_obj);
    if (s->finished) return mk_io_error("zstd compress push: stream already finished");

    ZSTD_inBuffer input = { lean_sarray_cptr(chunk), lean_sarray_size(chunk), 0 };

    size_t buf_size = ZSTD_CStreamOutSize();
    if (buf_size < 65536) buf_size = 65536;
    uint8_t *buf = (uint8_t *)malloc(buf_size);
    if (!buf) return mk_io_error("zstd compress push: out of memory");
    size_t total = 0;

    while (input.pos < input.size) {
        if (total >= buf_size) {
            if (buf_size > SIZE_MAX / 2) {
                free(buf);
                return mk_io_error("zstd compress push: output too large");
            }
            buf_size *= 2;
            uint8_t *newbuf = (uint8_t *)realloc(buf, buf_size);
            if (!newbuf) {
                free(buf);
                return mk_io_error("zstd compress push: out of memory");
            }
            buf = newbuf;
        }
        ZSTD_outBuffer output = { buf + total, buf_size - total, 0 };
        size_t ret = ZSTD_compressStream(s->cstream, &output, &input);
        if (ZSTD_isError(ret)) {
            lean_obj_res err = mk_zstd_error("zstd compress push", ret);
            free(buf);
            return err;
        }
        total += output.pos;
    }

    lean_obj_res arr = mk_byte_array(buf, total);
    free(buf);
    return lean_io_result_mk_ok(arr);
}

/*
 * Finish the compression stream: flush all remaining data.
 *
 * lean_zstd_compress_finish : @& ZstdCompressState → IO ByteArray
 */
LEAN_EXPORT lean_obj_res lean_zstd_compress_finish(b_lean_obj_arg state_obj, lean_obj_arg _w) {
    zstd_compress_state *s = (zstd_compress_state *)lean_get_external_data(state_obj);
    if (s->finished) {
        return lean_io_result_mk_ok(lean_alloc_sarray(1, 0, 0));
    }

    size_t buf_size = ZSTD_CStreamOutSize();
    if (buf_size < 65536) buf_size = 65536;
    uint8_t *buf = (uint8_t *)malloc(buf_size);
    if (!buf) return mk_io_error("zstd compress finish: out of memory");
    size_t total = 0;

    size_t remaining;
    do {
        if (total >= buf_size) {
            if (buf_size > SIZE_MAX / 2) {
                free(buf);
                return mk_io_error("zstd compress finish: output too large");
            }
            buf_size *= 2;
            uint8_t *newbuf = (uint8_t *)realloc(buf, buf_size);
            if (!newbuf) {
                free(buf);
                return mk_io_error("zstd compress finish: out of memory");
            }
            buf = newbuf;
        }
        ZSTD_outBuffer output = { buf + total, buf_size - total, 0 };
        remaining = ZSTD_endStream(s->cstream, &output);
        if (ZSTD_isError(remaining)) {
            lean_obj_res err = mk_zstd_error("zstd compress finish", remaining);
            free(buf);
            return err;
        }
        total += output.pos;
    } while (remaining > 0);

    ZSTD_freeCStream(s->cstream);
    s->cstream = NULL;
    s->finished = 1;

    lean_obj_res arr = mk_byte_array(buf, total);
    free(buf);
    return lean_io_result_mk_ok(arr);
}

/* ======== Streaming decompression ======== */

/*
 * Create a new Zstd decompression stream.
 *
 * lean_zstd_decompress_new : IO ZstdDecompressState
 */
LEAN_EXPORT lean_obj_res lean_zstd_decompress_new(lean_obj_arg _w) {
    ensure_zstd_classes();
    zstd_decompress_state *s = (zstd_decompress_state *)calloc(1, sizeof(zstd_decompress_state));
    if (!s) return mk_io_error("zstd decompress new: out of memory");

    s->dstream = ZSTD_createDStream();
    if (!s->dstream) {
        free(s);
        return mk_io_error("zstd decompress new: failed to create DStream");
    }

    size_t ret = ZSTD_initDStream(s->dstream);
    if (ZSTD_isError(ret)) {
        lean_obj_res err = mk_zstd_error("zstd decompress new", ret);
        ZSTD_freeDStream(s->dstream);
        free(s);
        return err;
    }

    return lean_io_result_mk_ok(lean_alloc_external(g_zstd_decompress_class, s));
}

/*
 * Push data through the decompression stream.
 *
 * lean_zstd_decompress_push : @& ZstdDecompressState → @& ByteArray → IO ByteArray
 */
LEAN_EXPORT lean_obj_res lean_zstd_decompress_push(b_lean_obj_arg state_obj,
                                                     b_lean_obj_arg chunk,
                                                     lean_obj_arg _w) {
    zstd_decompress_state *s = (zstd_decompress_state *)lean_get_external_data(state_obj);
    if (s->finished) return mk_io_error("zstd decompress push: stream already finished");

    ZSTD_inBuffer input = { lean_sarray_cptr(chunk), lean_sarray_size(chunk), 0 };

    size_t buf_size = ZSTD_DStreamOutSize();
    if (buf_size < 65536) buf_size = 65536;
    uint8_t *buf = (uint8_t *)malloc(buf_size);
    if (!buf) return mk_io_error("zstd decompress push: out of memory");
    size_t total = 0;

    while (input.pos < input.size) {
        if (total >= buf_size) {
            if (buf_size > SIZE_MAX / 2) {
                free(buf);
                return mk_io_error("zstd decompress push: output too large");
            }
            buf_size *= 2;
            uint8_t *newbuf = (uint8_t *)realloc(buf, buf_size);
            if (!newbuf) {
                free(buf);
                return mk_io_error("zstd decompress push: out of memory");
            }
            buf = newbuf;
        }
        ZSTD_outBuffer output = { buf + total, buf_size - total, 0 };
        size_t ret = ZSTD_decompressStream(s->dstream, &output, &input);
        if (ZSTD_isError(ret)) {
            lean_obj_res err = mk_zstd_error("zstd decompress push", ret);
            free(buf);
            return err;
        }
        total += output.pos;
        /* ret == 0 means frame is complete */
        if (ret == 0) {
            ZSTD_freeDStream(s->dstream);
            s->dstream = NULL;
            s->finished = 1;
            break;
        }
    }

    lean_obj_res arr = mk_byte_array(buf, total);
    free(buf);
    return lean_io_result_mk_ok(arr);
}

/*
 * Finish the decompression stream: clean up.
 *
 * lean_zstd_decompress_finish : @& ZstdDecompressState → IO ByteArray
 */
LEAN_EXPORT lean_obj_res lean_zstd_decompress_finish(b_lean_obj_arg state_obj, lean_obj_arg _w) {
    zstd_decompress_state *s = (zstd_decompress_state *)lean_get_external_data(state_obj);
    if (s->finished) {
        return lean_io_result_mk_ok(lean_alloc_sarray(1, 0, 0));
    }

    ZSTD_freeDStream(s->dstream);
    s->dstream = NULL;
    s->finished = 1;
    return lean_io_result_mk_ok(lean_alloc_sarray(1, 0, 0));
}
