# Progress: BitWriter wide-store flush (#2631)

**Date**: 2026-07-03 UTC
**Session type**: Feature
**Issue**: #2631

## Step 0: kernel microbenchmark (the required check) — cleared

`lake exe wide-store-bench` (new): four bit-emission kernels over the same
synthetic L1-like field trace (LCG-generated 7-9 bit "literals" + occasional
3-13 bit extras, no memory traffic), outputs verified byte-identical:

| variant | ns/field | vs A |
|---|---|---|
| A production push/byte | 7.9 | — |
| B grow-by-push + wide append (`pushUInt64LE`) | 5.5 | **1.44×** |
| C pre-sized buffer + `usetUInt64LE` cursor | 5.6 | 1.42× |
| D pre-sized + deferred 64-bit accumulator (flush ≥ 33 bits) | 3.2 | 2.46× |

Two decisions fell out of B ≈ C:

- **The issue's step 2 (pre-sized buffer + proven output bound, "the hard
  part") is unnecessary.** The append-form wide store captures the whole
  per-call win with the existing grow-by-push model — confirming #2739's
  branch-sample finding that push-doubling reallocs are already amortized
  to ~nothing. No BitWriter representation change, no proof restructure.
- **D is the real follow-up ceiling** (another ~1.7× over B at the kernel):
  defer flushing in a 64-bit accumulator (`bitBuf : UInt64`, flush every
  ~4 fields). That *does* change the BitWriter representation and its `wf`
  invariant (`bitCount < 8` → `< 64`), touching `BitWriterCorrect` and the
  field-level uses in `BlockSizeModel`/`DeflateFixedCorrect`/
  `DeflateDynamicCorrect`. Left for a follow-up issue.

Benchmark pitfalls hit (both worth remembering):
- The optimizer CSE'd/sank pure timed calls out of the timing window —
  fixed by per-rep runtime seeds and an IO action depending on the result
  inside the window.
- `c/bytearray_wide_ffi.c` was compiled with **no `-O` flag at all**, so
  every `lean.h` static-inline helper (`lean_sarray_cptr`,
  `lean_is_exclusive`, ...) was an outlined -O0 call. The wide ops lost to
  the runtime's own -O2 `push` until the lakefile target got
  `-O2 -DNDEBUG`. This also speeds the already-landed #2707 readers.

## Step 1: primitives + conformance

- `ByteArray.usetUInt64LE a off v h` — 8-byte LE store at `off`, reference
  body = chain of eight proven `a.set` writes; C does one wide store, in
  place when exclusive (issue's literal step-1 ask; used by bench C/D and
  the future deferred-accumulator work).
- `ByteArray.pushUInt64LE a v k h` (`k ≤ 8`) — append the low `k` bytes,
  reference body `pushLEBytes` = exactly `flushBytes`'s recursion; C hot
  path = one unconditional 8-byte store into capacity slack + size bump,
  cold path = the model's byte pushes (COW/growth via
  `lean_byte_array_push`).
- `ZipTest/Wide.lean`: sweeps vs the reference bodies, shared-input
  copy-on-write checks against independent snapshots (an alias compares
  equal even after a wrongful in-place mutation — snapshot first),
  exclusive-chain checks covering both C paths, LE spot-checks.
  `(3 : USize).toNat` is not kernel-decidable (platform-dependent size), so
  side conditions go through `toUSize_toNat_of_le_8` instead of `decide`.

## Step 3 (step 2 skipped): wiring, zero proof churn

`flushBytesWide data acc k = pushUInt64LE … when k ≤ 8` (always: `k =
total/8 ≤ (7+25)/8 = 4`), fallback `flushBytes`. `flushBytesWide_eq` +
`pushLEBytes_eq_flushBytes` re-derive `writeBits_def`/`writeHuffCode_def`
unchanged, so `BitWriterCorrect` and everything above it compile untouched.

## Measured (Silesia, pinned core, median-of-5, tokens held constant)

`l1-attrib` before (d7cd9688) → after, MB/s:
- fixed-only emit (col 4): +17–28% on all 12 files
- full L1 base candidate (col 5): +12–21% on all 12 files

Full test suite green (incl. new conformance tests + fuzz).
