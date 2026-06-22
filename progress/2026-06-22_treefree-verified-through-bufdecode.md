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

## Update: `decodeDynamicTrees_extract` done; target is the FORWARD direction

The full *iff* `inflateTreeFree ↔ inflate` is **false**: for invalid dynamic code
lengths the verified path rejects (`fromLengths` Kraft check fails) but the
tree-free path may accept (it builds canonical tables from the raw lengths). So
the right top-level theorem is the **forward** direction
`Inflate.inflate data = .ok out → Inflate.inflateTreeFree data = .ok out`
(tree-free is a correct drop-in for every *successful* decode).

`decodeDynamicTrees_extract` is now proven: a successful `decodeDynamicTrees`
yields the same code-length arrays and reader as `decodeDynamicLengthsOnly`, with
the trees being `fromLengths` of those arrays (peeling the shared prefix with a
`bindOk` helper, then reconstructing `decodeDynamicLengthsOnly`).

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

2. **Block-loop FORWARD correspondence** `inflateLoop ok → inflateLoopTreeFree ok`
   (recursive theorem, well-founded on `data.size*8 - br.bitPos`; only hyp is
   `br.data = data` — `readBits` re-establishes `bitOff<8` and the `bitPos` bound
   each iteration). Extract via the `bindOk` helper. Per block (`cases btype`):
   - btype 0 (`decodeStored`): the tree-free block call is *identical*; reuse
     `decodeStored_inv` / `decodeStored_invariants` (`BitReaderInvariant.lean` /
     `InflateCorrect.lean`) for `br'`'s invariants.
   - btype 1 (fixed): `decodeHuffmanFast = decodeHuffmanFastBuf` (delegation,
     `rfl`); the fixed trees are `fromLengthsTree fixedLitLengths 15` (from
     `inflateRaw`'s `fromLengths fixedLitLengths` success → `fromLengths_valid` +
     `fromLengths_ok_of_valid`); apply `decodeHuffmanFastBufTreeFree_ok_iff.mpr`
     (constant `fixedLitLengths`/`fixedDistLengths` valid, size ≤ `UInt16.size`).
   - btype 2 (dynamic): `decodeDynamicTrees_extract` + `fromLengths_valid` →
     `ll`/`dl` valid; `decodeDynamicTrees_inv` + `decodeDynamicTrees_bitOff_pres`
     for `br₃`'s invariants; apply `decodeHuffmanFastBufTreeFree_ok_iff.mpr`.
   - btype ≥3: `throw`, so `inflateLoop = .error` contradicts the `.ok` hyp.

   Block-reader hyps for `decodeHuffmanFastBufTreeFree_ok_iff` (`br₂`/`br₃`):
   `data` via `readBits_data_eq`/`decodeDynamicTrees_inv`; `bitOff<8` via
   `readBits_bitOff_lt_pos`/`decodeDynamicTrees_bitOff_pres`; `bitPos ≤ data.size*8`
   via `readBits_bitPos_le` (or `pos ≤ data.size` ∧ `hpos` from the `_inv` lemmas).
   **One new lemma needed**: `readBits n = .ok (v, _) → v.toNat < 2^n` (induction
   over `readBits.go`), to bound the dynamic `ll.size = hlit.toNat + 257 ≤ 288 <
   UInt16.size` (`Array.size_extract`, `decodeCLSymbols` size preservation).

3. **`inflateTreeFree` ↔ `inflateRaw`**: `inflate = inflateRaw data 0 …`;
   `inflateRaw` builds the fixed trees then calls `inflateLoop`; `inflateTreeFree`
   calls `inflateLoopTreeFree`. Compose (2) with the fixed-tree identity.

All supporting lemmas exist (`fromLengths_valid`, `fromLengths_ok_of_valid`,
`decodeHuffmanFastBuf` delegation). This layer is ~150–200 lines of
verified-pattern mirroring with reader-invariant threading.
