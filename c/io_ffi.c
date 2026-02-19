/*
 * FFI shims for IO.FS.Handle operations missing from Lean 4 stdlib.
 *
 * Provides seek (fseeko) and file size (fstat) on Lean's Handle type,
 * which wraps a FILE* internally.
 *
 * Upstream PR to add these to Lean 4 stdlib:
 *   https://github.com/leanprover/lean4/pull/11442
 *
 * Remove this file when seek/tell land in the stdlib.
 */

#include <lean/lean.h>
#include <stdio.h>
#include <stdint.h>
#include <limits.h>
#include <sys/stat.h>
#include <unistd.h>
#include <errno.h>
#include <string.h>

/*
 * Seek to an absolute position in a file handle.
 * Uses fseeko for 64-bit offset support (required for ZIP64).
 *
 * lean_handle_seek : @& IO.FS.Handle → UInt64 → IO Unit
 */
LEAN_EXPORT lean_obj_res lean_handle_seek(b_lean_obj_arg h, uint64_t pos, lean_obj_arg _w) {
    /* off_t is signed; reject values that would overflow or go negative */
    if (pos > (uint64_t)LLONG_MAX) {
        return lean_io_result_mk_error(
            lean_mk_io_user_error(lean_mk_string("handle seek: offset exceeds off_t range")));
    }
    FILE *fp = (FILE *)lean_get_external_data(h);
    if (fseeko(fp, (off_t)pos, SEEK_SET) != 0) {
        return lean_io_result_mk_error(
            lean_mk_io_user_error(lean_mk_string("handle seek: fseeko failed")));
    }
    return lean_io_result_mk_ok(lean_box(0));
}

/*
 * Get the size of the file underlying a handle.
 * Uses fstat on the file descriptor — does not move the file cursor.
 *
 * lean_handle_file_size : @& IO.FS.Handle → IO UInt64
 */
LEAN_EXPORT lean_obj_res lean_handle_file_size(b_lean_obj_arg h, lean_obj_arg _w) {
    FILE *fp = (FILE *)lean_get_external_data(h);
    int fd = fileno(fp);
    if (fd < 0) {
        return lean_io_result_mk_error(
            lean_mk_io_user_error(lean_mk_string("handle file size: invalid file descriptor")));
    }
    struct stat st;
    if (fstat(fd, &st) != 0) {
        return lean_io_result_mk_error(
            lean_mk_io_user_error(lean_mk_string("handle file size: fstat failed")));
    }
    if (st.st_size < 0) {
        return lean_io_result_mk_error(
            lean_mk_io_user_error(lean_mk_string("handle file size: negative file size")));
    }
    return lean_io_result_mk_ok(lean_box_uint64((uint64_t)st.st_size));
}

/*
 * Create a symbolic link.
 *
 * lean_create_symlink : @& String → @& String → IO Unit
 */
LEAN_EXPORT lean_obj_res lean_create_symlink(b_lean_obj_arg target, b_lean_obj_arg link_path, lean_obj_arg _w) {
    const char *t = lean_string_cstr(target);
    const char *l = lean_string_cstr(link_path);
    if (symlink(t, l) != 0) {
        char buf[512];
        snprintf(buf, sizeof(buf), "symlink: %s -> %s: %s", l, t, strerror(errno));
        return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(buf)));
    }
    return lean_io_result_mk_ok(lean_box(0));
}
