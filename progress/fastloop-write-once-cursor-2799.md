# Progress: fastloop / write-once cursor decode (#2799) — partial-confirm verdict

**Date**: 2026-07-08 UTC
**Session type**: Feature (benchmark-first probe; measured real-but-modest, recorded as verdict + landed spike)
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

3. **Measured** (same-binary A/B — the three modes `decode` / `decode-fast` /
   `decode-fast-u` in ONE `inflate-profile` binary, which is strictly more
   layout-comparable than the two-worktree rule; Python-zlib level-6 raw-DEFLATE
   payloads, libdeflate FFI unavailable in this env; `perf stat` cycles, 3
   trials; best-of-5 wall-clock cross-check):

   | corpus  | mix          | set! cursor (cyc) | uset fastloop (cyc) |
   |---------|--------------|-------------------|---------------------|
   | dickens | literal-heavy| −4.2%             | **−6.0%**           |
   | x-ray   | literal-heavy| −3.3%             | −3.6%               |
   | nci     | match-heavy  | −0.5%             | −0.9%               |
   | **geomean** |          | **−2.7%**         | **−3.5%**           |

   Wall-clock best-of-5 agrees (uset: dickens −6.4%, x-ray −3.5%, nci −2.7%).
   **Instructions did NOT drop** — they were flat-to-slightly-up and proved
   layout-sensitive across builds (the untouched baseline `decode` was
   bit-identical across rebuilds; `goCur` in the edited module shifted ±4%).
   The win is therefore **microarchitectural** (no realloc/regrow churn on the
   growing push buffer, no RC on its header), not an instruction-count
   reduction: the cursor index arithmetic replaces `push`'s internal
   bookkeeping roughly 1:1.

## Verdict

**The write-once cursor architecture is real and correct, but ~half to
two-thirds of the pre-registered 7–10% geomean: −3.5% cycles (uset) /
−2.7% (set!).** The shape matches the estimate (literal-heavy dickens −6.0%,
match-heavy nci −0.9%) at lower magnitude. Two decision-relevant findings:

- **The expensive part is not proven to pay.** The branch-free `uset` +
  299-margin machinery — the piece carrying the heaviest proof obligation in the
  repo (a write-once cursor equivalence through the exact-size buffer, plus the
  margin invariant) — separates from the far-simpler `set!` cursor by only
  ~0.8% cycles geomean, which is **inside the ±4% layout/codegen sensitivity**
  the instruction counts showed. Read it as "`uset` is **not proven materially
  better** than `set!`", not as a stable 0.8% edge.
- **The cheap part carries most of the win.** The `set!` cursor alone captures
  ~two-thirds (−2.7%), and it is a much more localized change to prove.

**Recommendation:** do not pay for the full `uset`+margin equivalence proof on
this evidence. If #2799 is pursued, target the `set!` cursor (better win/proof
ratio); the branch-free refinement is not justified by a delta within the
measurement noise. Under #2799's own "confirm the 7–10% before proving" rule,
the probe under-delivered vs pre-registration.

**Caveat (blocks any production/proof revival):** streams are Python-zlib
level-6 — this env lacks the libdeflate FFI, and #2799's pre-registration is on
libdeflate's denser (fewer-literal) streams. The literal-write component of the
win is likely smaller there; do not treat the magnitude as established. **A
libdeflate-stream rerun is required before reviving this for production or
proof.**

## Quality metrics

- sorry count (`grep -rc sorry Zip/`): unchanged from master — the spikes carry
  **no `sorry`** (they are total via `set!`/`copyWithinAt` and real `uset`
  proofs); they are simply not *proven equivalent* to the reference (no
  `Zip.Spec` obligation), guarded instead by the runtime conformance test.
- `lake build` + `lake exe test`: green.

## What remains

The tracking issue #2799's full scope (a proven, production-integrated cursor
decoder) is untouched and stays open for Kim's call. The reproducible probe
lives on this branch: `inflate-profile decode-fast` / `decode-fast-u` re-run the
exact A/B, `ZipTest/InflateFast.lean` guards correctness, and the FFI primitives
(`presize`, `copyWithinAt`) are the reusable substrate for whichever variant is
eventually proven.
