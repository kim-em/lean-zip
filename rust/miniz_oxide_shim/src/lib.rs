//! C-ABI shim for `miniz_oxide` so the lean-zip Track D bench can call into
//! the Rust DEFLATE comparator from C. We expose three functions:
//!
//!   * `lean_miniz_oxide_compress`   — raw DEFLATE encode (no zlib header),
//!   * `lean_miniz_oxide_decompress` — raw DEFLATE decode,
//!   * `lean_miniz_oxide_free`       — release a buffer the shim allocated.
//!
//! Status codes (returned by compress/decompress):
//!
//!   * `0` — success; `*out_ptr` and `*out_len` describe a heap buffer the
//!           caller MUST release with `lean_miniz_oxide_free`,
//!   * `1` — bad parameters (NULL pointers etc.),
//!   * `2` — decompression failure other than output-limit overrun,
//!   * `3` — decompression output exceeds the requested limit.
//!
//! The crate is `panic = "abort"` so we don't try to unwind across the FFI
//! boundary.

#![deny(unsafe_op_in_unsafe_fn)]

use std::os::raw::c_int;
use std::slice;

use miniz_oxide::deflate::compress_to_vec;
use miniz_oxide::inflate::{decompress_to_vec_with_limit, TINFLStatus};

/// Compress `input` with raw DEFLATE (no zlib header), allocating the
/// output as a `Box<[u8]>` whose pointer + length are written through
/// `out_ptr` and `out_len`. Returns `0` on success.
///
/// # Safety
/// `input` must be a valid `[u8]` of length `input_len` (or NULL when
/// `input_len == 0`). `out_ptr` and `out_len` must be valid writable
/// pointers. The caller MUST release the returned buffer with
/// `lean_miniz_oxide_free(*out_ptr, *out_len)`.
#[no_mangle]
pub unsafe extern "C" fn lean_miniz_oxide_compress(
    input: *const u8,
    input_len: usize,
    level: u8,
    out_ptr: *mut *mut u8,
    out_len: *mut usize,
) -> c_int {
    if out_ptr.is_null() || out_len.is_null() {
        return 1;
    }
    if input.is_null() && input_len != 0 {
        return 1;
    }
    let slice: &[u8] = if input_len == 0 {
        &[]
    } else {
        // SAFETY: caller guarantees `input` is a valid buffer of
        // `input_len` bytes.
        unsafe { slice::from_raw_parts(input, input_len) }
    };
    let vec = compress_to_vec(slice, level);
    let len = vec.len();
    let boxed: Box<[u8]> = vec.into_boxed_slice();
    let raw = Box::into_raw(boxed) as *mut u8;
    // SAFETY: caller guarantees `out_ptr` / `out_len` are writable.
    unsafe {
        *out_ptr = raw;
        *out_len = len;
    }
    0
}

/// Decompress raw DEFLATE data into a freshly allocated `Box<[u8]>`.
/// `max_output` caps the output size; pass `0` for unlimited.
///
/// # Safety
/// Same contract as `lean_miniz_oxide_compress`; on success the caller
/// MUST release the returned buffer with `lean_miniz_oxide_free`.
#[no_mangle]
pub unsafe extern "C" fn lean_miniz_oxide_decompress(
    input: *const u8,
    input_len: usize,
    max_output: u64,
    out_ptr: *mut *mut u8,
    out_len: *mut usize,
) -> c_int {
    if out_ptr.is_null() || out_len.is_null() {
        return 1;
    }
    if input.is_null() && input_len != 0 {
        return 1;
    }
    let slice: &[u8] = if input_len == 0 {
        &[]
    } else {
        // SAFETY: caller guarantees `input` is a valid buffer.
        unsafe { slice::from_raw_parts(input, input_len) }
    };
    let cap: usize = if max_output == 0 {
        usize::MAX
    } else {
        usize::try_from(max_output).unwrap_or(usize::MAX)
    };
    match decompress_to_vec_with_limit(slice, cap) {
        Ok(vec) => {
            let len = vec.len();
            let boxed: Box<[u8]> = vec.into_boxed_slice();
            let raw = Box::into_raw(boxed) as *mut u8;
            // SAFETY: caller guarantees `out_ptr` / `out_len` are writable.
            unsafe {
                *out_ptr = raw;
                *out_len = len;
            }
            0
        }
        Err(e) => match e.status {
            TINFLStatus::HasMoreOutput => 3,
            _ => 2,
        },
    }
}

/// Release a buffer returned by `lean_miniz_oxide_compress` or
/// `lean_miniz_oxide_decompress`.
///
/// # Safety
/// `ptr` / `len` must come from a previous successful call to one of the
/// allocator functions in this module, and must be released exactly once.
#[no_mangle]
pub unsafe extern "C" fn lean_miniz_oxide_free(ptr: *mut u8, len: usize) {
    if ptr.is_null() {
        return;
    }
    // SAFETY: caller guarantees `ptr` was returned by `Box::into_raw`
    // for a `Box<[u8]>` of length `len`.
    unsafe {
        let slice = slice::from_raw_parts_mut(ptr, len);
        let _ = Box::from_raw(slice as *mut [u8]);
    }
}
