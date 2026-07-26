//! zlib-rs / zlib-ng comparator for the lean-zip Track D dashboard.
//!
//! `build_all.sh` compiles this source twice with `flate2` default features
//! disabled: once with only `zlib-rs`, and once with only `zlib-ng`. Both
//! curves therefore share all file I/O, allocation, timing, and raw-DEFLATE
//! adapter code; the selected codec backend is the only difference.

#[cfg(all(feature = "zlib-rs-backend", feature = "zlib-ng-backend"))]
compile_error!("select exactly one compression backend");
#[cfg(not(any(feature = "zlib-rs-backend", feature = "zlib-ng-backend")))]
compile_error!("select either zlib-rs-backend or zlib-ng-backend");

use std::env;
use std::fs;
use std::hint::black_box;
use std::io::{self, Read, Write};
use std::process::ExitCode;
use std::time::Instant;

use flate2::read::DeflateDecoder;
use flate2::write::DeflateEncoder;
use flate2::Compression;

#[cfg(feature = "zlib-rs-backend")]
const BACKEND: &str = "zlib-rs";
#[cfg(feature = "zlib-ng-backend")]
const BACKEND: &str = "zlib-ng";

const TIMING_AGGREGATION: &str = "median";
const TIMING_REPS: usize = 5;

fn iters_for(size: usize) -> usize {
    if size <= 16_384 {
        50
    } else if size <= 262_144 {
        10
    } else if size <= 1_048_576 {
        3
    } else {
        1
    }
}

fn deflate(data: &[u8], level: u32) -> io::Result<Vec<u8>> {
    let mut encoder = DeflateEncoder::new(Vec::new(), Compression::new(level));
    encoder.write_all(data)?;
    encoder.finish()
}

fn inflate(compressed: &[u8]) -> io::Result<Vec<u8>> {
    let mut decoder = DeflateDecoder::new(compressed);
    let mut output = Vec::new();
    decoder.read_to_end(&mut output)?;
    Ok(output)
}

fn median_ns_per_op(
    iters: usize,
    mut operation: impl FnMut() -> io::Result<usize>,
) -> io::Result<u128> {
    let mut samples = [0_u128; TIMING_REPS];
    let mut sink = 0_usize;
    for sample in &mut samples {
        let start = Instant::now();
        for _ in 0..iters {
            sink = sink.wrapping_add(black_box(operation()?));
        }
        *sample = start.elapsed().as_nanos() / iters.max(1) as u128;
    }
    black_box(sink);
    samples.sort_unstable();
    Ok(samples[samples.len() / 2])
}

fn mbps(size: usize, ns_per_op: u128) -> f64 {
    if ns_per_op == 0 {
        return 0.0;
    }
    (size as f64 / (1024.0 * 1024.0)) / (ns_per_op as f64 / 1.0e9)
}

fn run_decode(path: &str) -> io::Result<()> {
    let compressed = fs::read(path)?;
    let decoded = inflate(&compressed)?;
    let size = decoded.len();
    let ns = median_ns_per_op(iters_for(size), || Ok(inflate(&compressed)?.len()))?;
    println!(
        "{{\"decompress_mbps\":{:.2},\"decoded_size\":{},\
         \"timing_aggregation\":\"{}\",\"timing_reps\":{}}}",
        mbps(size, ns),
        size,
        TIMING_AGGREGATION,
        TIMING_REPS
    );
    Ok(())
}

fn run_roundtrip(path: &str, level: u32) -> io::Result<()> {
    let data = fs::read(path)?;
    let size = data.len();
    let iters = iters_for(size);
    let compressed = deflate(&data, level)?;
    if inflate(&compressed)? != data {
        return Err(io::Error::other(format!(
            "{BACKEND} roundtrip mismatch: inflate(deflate(data)) != data"
        )));
    }

    let compress_ns = median_ns_per_op(iters, || Ok(deflate(&data, level)?.len()))?;
    let decompress_ns = median_ns_per_op(iters, || Ok(inflate(&compressed)?.len()))?;
    println!(
        "{{\"out_size\":{},\"compress_mbps\":{:.2},\"decompress_mbps\":{:.2},\
         \"timing_aggregation\":\"{}\",\"timing_reps\":{}}}",
        compressed.len(),
        mbps(size, compress_ns),
        mbps(size, decompress_ns),
        TIMING_AGGREGATION,
        TIMING_REPS
    );
    Ok(())
}

fn main() -> ExitCode {
    let args: Vec<String> = env::args().collect();
    let result = match args.as_slice() {
        [_, mode, path] if mode == "decode" => run_decode(path),
        [_, path, level] => match level.parse::<u32>() {
            Ok(level @ 0..=9) => run_roundtrip(path, level),
            Ok(_) => Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "compression level must be in 0..=9",
            )),
            Err(error) => Err(io::Error::new(io::ErrorKind::InvalidInput, error)),
        },
        _ => {
            eprintln!(
                "usage: bench-{BACKEND} <payload.bin> <level>  |  \
                 bench-{BACKEND} decode <stream.deflate>"
            );
            return ExitCode::from(2);
        }
    };

    match result {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("bench-{BACKEND}: {error}");
            ExitCode::FAILURE
        }
    }
}
