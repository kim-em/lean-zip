# Progress: compress→FFI fuzz + native-vs-FFI strictness census

- **Date**: 2026-06-11 UTC
- **Session**: b6fadf47 (feature, one-shot)
- **Issue**: #2535

## Accomplished

Added two encoder-side fuzz entries to `ZipTest/FuzzInflate.lean`, both
deterministic (fixed-seed) and reproducible:

1. **compress→FFI-decompress round-trip** (`runCompressFuzz`, 256 iters):
   native `Deflate.deflateRaw` at a sampled level (`#[0,1,4,6,7,8,9]`,
   including the optimal-parse level 9) over PRNG payloads spanning four
   compressibility classes (`genPayloadCls`: random, small-alphabet,
   long-runs, repeated-motif), decompressed through the zlib FFI
   (`RawDeflate.decompress`) with a byte-equality assertion. This is the
   cross-implementation net the native-only round-trips lack.

2. **differential strictness census** (`runDiffFuzz`, 256 iters): build a
   valid dynamic block from a compressible payload via `deflateRaw … 9`
   (filtering on BTYPE==2 so we only mutate real dynamic blocks), flip
   one bit in the header region (BFINAL/BTYPE bits 0–2 left intact, so
   the flip lands in HLIT/HDIST/HCLEN/CL-lengths/lit-len-length region),
   then decode the mutation with both native inflate and the FFI and
   tally the verdicts into a `Census`. Silent corruption (both accept but
   produce different bytes) fails; native-accepts/FFI-rejects is the
   known strictness gap and is **recorded, not failed**.

## Census result (seed 0xfeedface, 256 iters)

223 mutated (33 skipped non-dynamic):
- both-reject: 220
- **native-accept / FFI-reject: 3** ← the strictness gap
- native-reject / FFI-accept: 0
- both-accept-but-disagree (corruption): 0

The 3 native-accept/FFI-reject cases confirm native inflate is more
lenient than zlib on malformed dynamic headers (the `repairBl` bug
class). Low but nonzero — enough to justify a follow-up issue to tighten
native inflate strictness, but not an active corruption signal.

## Decisions

- Deliverable 3 ("register in ZipTest.lean") is satisfied transitively:
  both drivers are invoked from `FuzzInflate.tests`, which is already
  wired into `ZipTest.main`. Adding separate top-level calls would only
  double the run, so I kept the existing one-module-one-entry shape.
- Used `deflateRaw … 9` + BTYPE filter (rather than `deflateDynamicBlock`
  directly) for the base stream so it is always the verified encoder's
  output and can never false-fail the base round-trip assertion; the
  trade-off is skipping iterations whose payload compresses to a
  non-dynamic block, mitigated by biasing payload sizes upward
  (`#[300,800,2000,4096,9000]`) and to compressible classes 1–3.

## Quality metrics

- `lake build && lake exe test` green; full suite ~15 s.
- No `sorry` introduced (test-only change).
