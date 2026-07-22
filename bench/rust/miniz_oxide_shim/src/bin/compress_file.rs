//! `miniz-compress-file` — the honest rust side of the end-to-end CLI comparison.
//!
//! A minimal real compression tool: read a file with `std::fs::read` (Rust's
//! pre-sized `read_to_end`), raw-DEFLATE compress it with
//! `miniz_oxide::deflate::compress_to_vec(&data, 6)`, and print the compressed
//! length. Same codec and level mapping as the Track D shim's
//! `lean_miniz_oxide_compress` (which calls `compress_to_vec(slice, level)`
//! with the level passed straight through), so on silesia.tar it produces the
//! identical 68,112,444-byte output.
//!
//! This is the fair rust counterpart to the lean `compress-file` exe. Both are
//! fresh processes doing read-file → compress → report, so timing them
//! head-to-head measures the real end-to-end `zip silesia.tar` wall — including
//! each language's file-read/alloc path, which the codec-only ratio in
//! bench/whole_tar_l6.sh's `codec` section deliberately cancels out.
//!
//! Usage:  miniz-compress-file <path> [level=6]

use std::process::ExitCode;

use miniz_oxide::deflate::compress_to_vec;

fn main() -> ExitCode {
    let mut args = std::env::args().skip(1);
    let path = match args.next() {
        Some(p) => p,
        None => {
            eprintln!("usage: miniz-compress-file <path> [level=6]");
            return ExitCode::FAILURE;
        }
    };
    let level: u8 = args
        .next()
        .and_then(|s| s.parse().ok())
        .unwrap_or(6);
    let data = match std::fs::read(&path) {
        Ok(d) => d,
        Err(e) => {
            eprintln!("miniz-compress-file: cannot read {path}: {e}");
            return ExitCode::FAILURE;
        }
    };
    let out = compress_to_vec(&data, level);
    println!("{}", out.len());
    ExitCode::SUCCESS
}
