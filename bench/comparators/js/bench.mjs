// JS DEFLATE comparator for the lean-zip Track D dashboard.
//
// Uses fflate — a pure-JavaScript DEFLATE codec (no native zlib binding; node's
// built-in zlib would just be another C-zlib data point, so we deliberately
// avoid it). Honours the shared comparator contract:
//
//   node bench.mjs <payload.bin> <level>  ->  stdout JSON
//   {"out_size":N,"compress_mbps":X,"decompress_mbps":Y}
//
// Timing mirrors ZipBenchReport.lean: median-of-5 reps, itersFor(size) iters per
// rep, throughput against the uncompressed byte count. Self-verifies its
// roundtrip before timing.
import { readFileSync } from "node:fs";
import { deflateSync, inflateSync } from "fflate";

function itersFor(size) {
  if (size <= 16384) return 50;
  if (size <= 262144) return 10;
  if (size <= 1048576) return 3;
  return 1;
}

let sink = 0; // defeat dead-code elimination

function medianNsPerOp(iters, op) {
  const reps = [];
  for (let r = 0; r < 5; r++) {
    const t0 = process.hrtime.bigint();
    for (let i = 0; i < iters; i++) sink += op();
    const ns = Number(process.hrtime.bigint() - t0) / Math.max(iters, 1);
    reps.push(ns);
  }
  reps.sort((a, b) => a - b);
  return reps[Math.floor(reps.length / 2)];
}

function mbps(size, nsPerOp) {
  if (nsPerOp === 0) return 0;
  return Math.round(((size / (1024 * 1024)) / (nsPerOp / 1e9)) * 100) / 100;
}

// Decode-only throughput on a provided raw-DEFLATE stream (fixed external
// encoder), so every decoder is measured on byte-identical input. Throughput is
// against the decoded (uncompressed) byte count.
function runDecode(path) {
  const comp = new Uint8Array(readFileSync(path));
  const size = inflateSync(comp).length;
  const iters = itersFor(size);
  const dNs = medianNsPerOp(iters, () => inflateSync(comp).length);
  if (sink === 0) console.error("unreachable");
  process.stdout.write(JSON.stringify({
    decompress_mbps: mbps(size, dNs),
    decoded_size: size,
  }) + "\n");
}

function main() {
  const argv = process.argv.slice(2);
  if (argv.length === 2 && argv[0] === "decode") {
    runDecode(argv[1]);
    return;
  }
  const [path, levelStr] = argv;
  if (!path || levelStr === undefined) {
    console.error("usage: node bench.mjs <payload.bin> <level>  |  node bench.mjs decode <stream.bin>");
    process.exit(2);
  }
  const data = new Uint8Array(readFileSync(path));
  const level = parseInt(levelStr, 10);
  const size = data.length;
  const iters = itersFor(size);

  const comp = deflateSync(data, { level });
  const back = inflateSync(comp);
  if (back.length !== size || !back.every((b, i) => b === data[i])) {
    throw new Error("roundtrip mismatch: inflate(deflate(data)) != data");
  }

  const cNs = medianNsPerOp(iters, () => deflateSync(data, { level }).length);
  const dNs = medianNsPerOp(iters, () => inflateSync(comp).length);

  if (sink === 0) console.error("unreachable");
  process.stdout.write(JSON.stringify({
    out_size: comp.length,
    compress_mbps: mbps(size, cNs),
    decompress_mbps: mbps(size, dNs),
  }) + "\n");
}

main();
