# Tree-free canonical decode: verified through the wide-buffer block decoder (issue #2678)

- **Date**: 2026-06-22 UTC
- **Session type**: feature (branch `issue-2678-treefree-proof`)
- **Issue**: #2678

## Achievement

The tree-free DEFLATE decoder is now **formally proven to accept exactly the
inputs the verified tree decoder does, with identical output, all the way up
through the wide-buffer block decoder** — the Huffman tree (`fromLengthsTree`) is
a proof-only object, never built at runtime. All in `Zip.Spec.InflateTreeFreeCorrect`
(registered in `Zip.lean`, so CI compile-checks it). No `sorry`. The decode
loops are well-founded (no longer `partial`); `treefree-decode-bench` stays
byte-identical to `Inflate.inflate` on all 23 corpus files with the ~13–15%
speedup preserved.

## What's proven (bottom-up)

**Canonical structures** (steps 1–3): `buildSymbols` counting-sort placement;
`codeFor_placed` (placed symbol's codeword); surjectivity + `codeFor_of_value`
(value→codeword); the full `walkCanonical` characterization both directions
(`walkCanonical_ok_spec` soundness, `walkCanonical_complete` completeness).

**Per-symbol correspondence** (UInt64-land, no BitReader):
`walkTree_ok_spec`/`walkTree_complete` mirror the `walkCanonical` lemmas, giving
`walkCanonical_ok_iff_walkTree` — the canonical long-code decode and the tree
walk over the same buffer succeed on exactly the same inputs with the same
result (error strings may differ; the loops still reject the same inputs). Hence
`decodeSymCanon_ok_iff_decodeSym`.

**Well-founded loops**: `goTreeFree`, `goTreeFreeU`, `inflateLoopTreeFree` made
non-`partial` (mirroring `goFusedP`/`goFusedPU`/`inflateLoop`); `goTreeFree`'s
body is now byte-identical to `goFusedP` except the decode call.

**Loop correspondence**: `goTreeFree_ok_iff_goFusedP` (well-founded induction;
the per-symbol iff threaded through refill / inline-literal / literal /
length+distance branches); `goTreeFreeU_eq` (USize loop projects to the boxed
one, mirror of `goFusedPU_eq`).

**Block decoder**: `decodeHuffmanFastBufTreeFree_ok_iff` — the tree-free
wide-buffer block decode equals the verified `decodeHuffmanFastBuf` on success:
tables coincide (`buildTableCanonicalFast_eq_buildTable`), both addressability
dispatches collapse to the boxed loop, and the loops agree (threaded through the
shared reconstruction via `bind_ok_iff`).

## Remaining: the `inflate` top-level wrapper (one more layer)

`decodeHuffmanFastBufTreeFree_ok_iff` is the substantive result. To lift it to
`Inflate.inflateTreeFree data = .ok out ↔ Inflate.inflate data = .ok out`:

1. **`decodeDynamicTrees` ↔ `decodeDynamicLengthsOnly`**: the two share their
   whole prefix; `decodeDynamicTrees` just appends two `fromLengths` builds. NOT
   `rfl` (needs bind-associativity over the ~6-bind prefix). Prove
   `decodeDynamicTrees br = (decodeDynamicLengthsOnly br >>= fun p =>
   fromLengths p.1 15 >>= fun lt => fromLengths p.2.1 15 >>= fun dt =>
   .ok (lt, dt, p.2.2))` via `simp [bind_assoc]` over the unfolded prefix (or a
   shared-prefix helper). Then `fromLengths_valid` (`DynamicTreesCorrect.lean`)
   gives `ValidLengths`, and `fromLengths_ok_of_valid` gives
   `lt = fromLengthsTree p.1 15`.

2. **Block-loop correspondence** `inflateLoopTreeFree ok-iff inflateLoop`
   (well-founded on `dataSize*8 - br.bitPos`, threading `br.bitOff < 8` and
   `br.bitPos ≤ data.size*8`). Per block: btype 0 (`decodeStored`) identical;
   btype 1 (fixed) uses `decodeHuffmanFastBufTreeFree_ok_iff` with the constant
   `fixedLitLengths`/`fixedDistLengths` (valid, size ≤ `UInt16.size`); btype 2
   (dynamic) uses (1) + `decodeHuffmanFastBufTreeFree_ok_iff`. `decodeHuffmanFast`
   = `decodeHuffmanFastBuf` (delegation), and `fixedLit`/`fixedDist` in `inflateRaw`
   are `fromLengthsTree fixedLitLengths 15` / `…distLengths…` (via
   `fromLengths_ok_of_valid`). Reader invariant: `bitOff<8` is maintained by
   `readBits`/the decoder reconstruction (`endbit % 8`); `bitPos` bound from the
   loop's out-of-range guard.

3. **`inflateTreeFree` ↔ `inflateRaw`**: `inflate = inflateRaw data 0 …`;
   `inflateRaw` builds the fixed trees then calls `inflateLoop`; `inflateTreeFree`
   calls `inflateLoopTreeFree`. Compose (2) with the fixed-tree identity.

All supporting lemmas exist (`fromLengths_valid`, `fromLengths_ok_of_valid`,
`decodeHuffmanFastBuf` delegation). This layer is ~150–200 lines of
verified-pattern mirroring with reader-invariant threading.
