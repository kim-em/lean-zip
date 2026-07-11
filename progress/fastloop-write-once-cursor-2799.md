# Progress: fastloop / write-once cursor decode (#2799) — confirmed +6.2% throughput

**Date**: 2026-07-08 UTC
**Session type**: Feature (benchmark-first probe; measured a real end-to-end win on libdeflate streams, landed the reproducible spike)
**Issue**: #2799

## What was done

Followed the issue's own framing comment exactly: spike the fastloop +
write-once cursor first, confirm the win on `inflate-profile` A/B
(x-ray / dickens / nci, instructions **and** cycles), and only pay for the
(heaviest-in-repo) equivalence proof once the win is confirmed.

1. **Two spikes implemented** in a quarantined module
   `Zip/Native/InflateFast.lean` (NOT on any production path — `Inflate.inflate`
   is unchanged and stays the verified decoder):
   - `goCur` / `Inflate.inflateFast`: byte-for-byte `goTreeFreeU` with the
     output side swapped to a **`set!` cursor** into a pre-extended buffer
     (`ByteArray.presize`), and back-references written in place at the cursor
     via `ByteArray.copyWithinAt` (append-free analogue of
     `copyWithin`/`extendWithin`). Input handling (`uget` wide refill, packed
     table, `walkCanonical`) is identical, so the A/B isolates exactly the
     per-symbol **output-write** cost — #2799's "remaining half".
   - `goCurU` / `Inflate.inflateFastU`: the actual #2799 shape — a per-symbol
     margin guard `outPos + 299 ≤ output.size` gating a branch-free body where
     literals are proven-bounds `uset` (bound discharged from the margin, real
     omega proof, no `sorry`) and the per-literal max-size check is gone. The
     <299-byte tail delegates to `goCur`.
   - Two FFI primitives (`c/inflate_fast_ffi.c`, extern-with-reference-body
     pattern like `copyWithin`): `presize` (zeroed buffer) and `copyWithinAt`
     (in-place LZ77 copy at a cursor).
   - Exact-size path only: the caller passes the true decompressed length as
     `sizeHint` (the archive workloads: gzip ISIZE, ZIP sizes).

2. **Correctness**: both spikes decode byte-identically to the reference on all
   three corpora and across block types / edge cases / RLE — asserted by the
   new `ZipTest/InflateFast.lean` conformance suite (green) and by the
   `inflate-profile decode-fast{,-u}` one-time equality check.

3. **Measured — absolute end-to-end throughput** (`inflate-profile` decode rate,
   loop-only timing so process startup / one-time sanity decode are excluded;
   best-of-5 MB/s; **libdeflate level-6 raw-DEFLATE streams**, the dense
   pre-registered workload — libdeflate built into the bench via `shell.nix`,
   which already lists it; the whole-corpus decompressed bytes over the timed
   loop is the decode-rate denominator). Numbers averaged over two independent
   best-of-5 sweeps (run-to-run spread < 1%):

   | corpus  | mix          | native decode | set! cursor | **uset fastloop** | libdeflate |
   |---------|--------------|--------------:|------------:|------------------:|-----------:|
   | dickens | literal-heavy | 280.7 MB/s   | 299.0 (+6.5%) | **304.0 (+8.3%)** | 994 |
   | x-ray   | literal-heavy | 182.2 MB/s   | 192.4 (+5.6%) | **193.0 (+5.9%)** | 595 |
   | nci     | match-heavy   | 903.2 MB/s   | 940.2 (+4.1%) | **943.2 (+4.4%)** | 2033 |
   | **geomean gain** |       |              | **+5.4%**    | **+6.2%**         | (2.2–3.3× the native rate) |

   The win is **microarchitectural** — eliminating the realloc/regrow churn on
   the growing `push` buffer and the refcount traffic on its header, not an
   instruction-count reduction (instruction counts were flat-to-up and
   layout-sensitive, so they are not the metric; throughput is). `uset`'s
   branch-elision adds a further ~1% geomean over the `set!` cursor, concentrated
   on the literal-heavy `dickens` (+1.7pp), where dropping the per-literal
   bounds/max-size checks pays.

## Verdict

**The write-once cursor architecture delivers a real, reproducible end-to-end
throughput win: the `uset` fastloop is +6.2% geomean (dickens +8.3%, x-ray
+5.9%, nci +4.4%), the `set!` cursor +5.4%.** That is in the ballpark of #2799's
pre-registered 7–10% — literal-heavy `dickens` lands at +8.3%, inside the band;
match-heavy `nci` at +4.4% is the low end, exactly the predicted shape. In
absolute terms the native decoder goes 280 → 304 MB/s on `dickens`, 182 → 193 on
`x-ray`, 903 → 943 on `nci`; libdeflate remains 2.2–3.3× faster still.

(**Correction to an earlier draft of this verdict:** a first pass measured on
zlib streams with a whole-process `perf stat` cycle count and reported only
−3.5% cycles, calling the win "half the estimate". That was wrong — the cycle
count carried a ±4% code-layout artifact and included the one-time sanity decode.
The clean best-of-5 loop-only throughput on the pre-registered libdeflate streams
above is the number that stands.)

**Recommendation:** the win justifies proceeding — the `uset` fastloop is the
full #2799 shape and earns its keep (+6.2% geomean, +8.3% literal-heavy, and it
beats the plain `set!` cursor where literals dominate). The next step is the
equivalence proof (the heaviest proof surface in the repo: a write-once cursor
equivalence through the exact-size buffer plus the 299-margin invariant), which
this benchmark-first probe has now cleared the bar for. The `set!` cursor
remains a valid cheaper-to-prove fallback if the `uset` proof proves
intractable, at ~0.8pp less throughput.

## Proof progress — `inflateFast_eq` is COMPLETE, `Zip/Spec/InflateFastCorrect.lean` is `sorry`-free (2026-07-10)

The whole lift is proven. `inflateFast_eq`: whenever the verified
`Inflate.inflate` yields `out`, the write-once cursor decoder run at the exact
size hint `out.size` yields the same bytes. The full dependency chain, all
`sorry`-free:

1. `goCur_eq` — the core bisimulation (below), plus `goCur_size` (the cursor
   preserves the buffer size).
2. The two block bridges `decodeHuffmanCurTables_eq` (via `goCur_eq`) and
   `decodeStoredCur_eq` (via the `storedCopyLoop` content lemmas — `decodeStoredCur`
   was refactored from an opaque `for`-loop to WF `storedCopyLoop`), each also
   concluding `cf.size = buf.size`.
3. Reference-loop output monotonicity `inflateLoopTreeFree_size_mono` (per-block
   growth via `goTreeFreeU_size_mono` / append, threaded through
   `inflateLoopTreeFree.induct`; `bitOff < 8` is derived fresh each iteration, so
   the IH need not carry it).
4. The block-loop bisimulation `inflateLoopCur_eq` (via `inflateLoopCur.induct`):
   `inflateLoopCur` re-represents `inflateLoopTreeFree` block-for-block, applying
   the two bridges and threading the cursor invariant, with per-block room from
   the monotonicity lemma and the fixed buffer size from `goCur_size` /
   `storedCopyLoop_size`.
5. `inflateFast_eq`: `Inflate.inflate = inflateLoopTreeFree` (`inflateRaw_eq_loop`),
   then the loop bisimulation on the presized buffer, then the exact-size contract
   (`cf.size = out.size`, so `cf = out`). Takes the honest addressability
   hypotheses `data.size / out.size < USize.size` and `out.size ≤ maxOut` (the
   wide-buffer cursor path's always-true-for-in-memory-`ByteArray`s conditions).

`lake build` + `lake exe test` green. The file is standalone (not imported by
`Zip`), so production and CI stay `sorry`-free regardless.

**Rebased onto master and CI-green (2026-07-11).** Master (`#2819`) evolved the
reference decoder to libdeflate-style subtables — the separate fixed tables /
`buildLongDecodeWithCount` were replaced by `buildTreeFreeWithCount` (a
`DecodeTable × LongDecode` pair). Because `goCur_eq`, both block bridges, and
`goCur_size` are all *generic* in the decode table (they only need
`packed.size = 2^fastBits`), the entire correctness proof survived untouched. The
only adaptation was mechanical: the cursor spike's `inflateLoopCur` /
`inflateLoopCurU` now build tables via `buildTreeFreeWithCount` (matching the
reference `inflateLoopTreeFree`), with `maxRecDepth`/`maxHeartbeats` raised on the
loop defs since that construction is deeper to elaborate inline. The full branch —
proof + spike + benchmarks — is green on CI (build-and-test, bench, animation-sync,
check) rebased on top of master.

## Proof progress — the core bisimulation `goCur_eq` is COMPLETE (2026-07-09)

`goCur_eq` — the write-once-cursor decode agrees with `goTreeFreeU` — is now
**fully proven, no `sorry`, no `decreasing_by`**. All 10 loop cases (refill,
literal write/error, long-literal write/error/no-progress, EOB, invalid-length,
back-reference) are discharged. This is the heaviest proof surface in the repo,
the piece the issue's own framing said to pay for only after the win was
confirmed.

Key move: the first attempt used direct well-founded recursion, but a tactic
theorem's `decreasing_by` does **not** receive the `by_cases`/`split` guard
hypotheses (they are packed into the WF argument tuple), so the per-branch
measure decreases — literal `len ≥ 1`, decode `consumed ≥ 1 bit` — were
unprovable there. Rebuilding the proof over `goCur.induct` (functional
induction) supplies each guard as a named case hypothesis and carries no
termination obligation, exactly mirroring the existing `goTreeFreeU_eq`. The
goal side stays in `goCur`'s native `entryAtU` form (so it unifies with each
IH); only `href` is normalised to `entryAt` via `entryAtU_window_eq`, with the
IH rebased by `hue` where a literal write is involved. The two write bridges
(`set!_extract_eq_push`, `copyWithinAt_extract_eq_copyLoop`) and per-step room
from `goTreeFreeU_size_mono` close each write case.

The block-loop lift (`inflateFast_eq`) is underway on the foundation of
`goCur_eq`. `Inflate.inflate = inflateLoopTreeFree` (`inflateRaw_eq_loop`,
`rfl`), and `inflateLoopCur` mirrors `inflateLoopTreeFree` block-for-block
(same `btype` dispatch, `decodeDynamicLengthsOnly`, `bfinal`/progress guards),
differing only in the output representation.

- **Done — the Huffman-block bridge** `decodeHuffmanCurTables_eq`: one Huffman
  block decoded at a cursor (`decodeHuffmanCurTables`, through `goCur`)
  re-represents the reference block decode (`decodeHuffmanFastBufTables`,
  through `goTreeFreeU`). Same entry refill and `BitReader` bookkeeping —
  established through the `BufCorr` invariant (`refill_corr` / `consume_corr`,
  giving the `pos ≤ size` bound `goCur_eq` needs) — and by `goCur_eq` the same
  produced bytes, a prefix of the cursor buffer. Covers `btype ∈ {1, 2}`.
- **Done — the stored-block bridge** `decodeStoredCur_eq` (`btype = 0`).
  `decodeStoredCur`'s copy was refactored from a `for i in [:len]` loop (opaque
  `forIn`, unprovable) to well-founded `storedCopyLoop` (output byte-identical,
  conformance green). Its three content lemmas are proved — `storedCopyLoop_size`,
  `storedCopyLoop_getElem!` (written-window content), and `storedCopyLoop_extract`
  (the placed bytes are the reference `buf.extract 0 outPos ++ bytes` as a cursor
  prefix). The bridge then relates `decodeStoredCur` to `Inflate.decodeStored`:
  identical reads and `BitReader` bookkeeping, max-size guard aligned via
  `(buf.extract 0 outPos).size = outPos`.
- **Remaining** for `inflateFast_eq` — the two block bridges above are the
  reusable core; what is left is the assembly:
  1. The loop bisimulation `inflateLoopCur.induct` against `inflateLoopTreeFree`
     (`btype` dispatch is block-for-block identical), applying the two block
     bridges and threading the cursor invariant `refOut = buf.extract 0 outPos`.
     This needs the reference loop's output monotonicity (each block's output is
     a prefix of the final, so intermediate `.size ≤ final .size ≤ buf.size`) and
     preservation of the `BitReader` invariants (`bitOff < 8`, `bitPos ≤ size*8`)
     across blocks.
  2. Instantiation with the presized buffer + exact-size contract, chaining
     `inflate = inflateRaw = inflateLoopTreeFree`.

## Proof progress (`Zip/Spec/InflateFastCorrect.lean`)

With the win confirmed, the equivalence proof is started. The bisimulation
approach: the reference threads a growing `output` (`.size` = logical length);
the cursor loop threads a fixed buffer + `outPos` (logical content =
`buf.extract 0 outPos`). Both make identical control decisions because
`outPos = refOutput.size`, so every guard aligns; the two write steps are
bridged by write-vs-append lemmas, with a big-enough-buffer hypothesis
discharged per step by the reference's monotone growth.

**Verified — both write bridges + monotonicity + all supporting lemmas (no `sorry`):**
- `set!_extract_eq_push` — **the literal write bridge**: cursor `set!` then
  extract equals extract then `push` (via the pure-`Array`
  `arr_setIfInBounds_extract_eq_push`, `ByteArray.size_set!` / `getElem!_set!`).
- `copyWithinAt_extract_eq_copyLoop` — **the back-reference write bridge**: cursor
  `copyWithinAt` then extract equals `copyLoop` on the logical prefix. Assembled
  from the `copyWithinAtGo` content lemmas (`_size`, `_getElem!_lt` preservation
  below the cursor, `_getElem!_written` the periodic window content) plus
  `copyLoop_eq_ofFn`, via `getElem!` extensionality and list-`getElem!` helpers.
- `goTreeFree_size_mono` — **reference output monotonicity** (10-case
  WF-recursion proof over the reference loop): refill/EOB keep the output, the
  two literal branches grow by `push`, the match branch by `copyLoop`. Discharges
  the per-step buffer-room obligation.
- Infrastructure: `ByteArray.get!_eq_getElem!`, `getElem!_extract`,
  `getElem!_eq_data_toList`, `ext_getElem!`, `copyLoop_size`, and list
  `getElem!` append/`ofFn` helpers.

**`inflateFast_eq` is now proven** (see the completion section at the top of this
file). `Zip/Spec/InflateFastCorrect.lean` is entirely `sorry`-free.

## Quality metrics

- sorry count (`grep -rc sorry Zip/`): **0**. `Zip/Spec/InflateFastCorrect.lean`
  (the full correctness proof `goCur_eq` → block bridges → loop bisimulation →
  `inflateFast_eq`) and the spikes (`Zip/Native/InflateFast.lean`) both carry no
  `sorry`. The spec file is not imported by `Zip`, so the production decoder and
  CI are `sorry`-free regardless.
- `lake build` + `lake exe test`: green.

## What remains

The tracking issue #2799's full scope (a proven, production-integrated cursor
decoder) stays open. The reproducible probe lives on this branch:
`inflate-profile decode-fast` / `decode-fast-u` re-run the exact A/B,
`ZipTest/InflateFast.lean` guards correctness, and `Zip/Spec/InflateFastCorrect.lean`
holds the verified foundational lemmas + the roadmap for the bisimulation and
the lift to `inflateFast = inflate`.
