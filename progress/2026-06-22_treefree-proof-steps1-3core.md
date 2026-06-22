# Tree-free canonical decode: steps 1–3 core proven (issue #2678)

- **Date**: 2026-06-22 UTC
- **Session type**: feature (branch `issue-2678-treefree-proof`)
- **Issue**: #2678

## What landed (5 green commits, no sorry, full build + tests pass)

All in `Zip/Spec/InflateTreeFreeCorrect.lean`.

- `141d1194` **Step 1 — `buildSymbols` counting-sort placement.**
  `buildSymbols_placement`: every valid-length symbol `s` is written at
  `firstIndex[len] + numEarlier lsList len s`. Via the WF `go` invariant carrying
  offset-tracking (A) and placements-so-far (B); overwrite-safety reduces to
  `place_ne` (distinct length-blocks are disjoint, by `psumCount` monotonicity).
  `numEarlier` is defined to match `codeFor`'s offset exactly. Needs no validity.
- `9127b191` **Step 2 — `codeFor` correspondence.**
  `buildLongDecode_placement` (instantiates step 1; needs only `maxBits ≥ 1`),
  `codeFor_placed`: `codeFor lsList maxBits s = some (natToBits (firstCode[len] +
  numEarlier lsList len s) len)`. Plus `countLengthsFast_eq` bridge.
- `8a8a14ff` **Step 3 core — surjectivity / value→codeword (the `←` direction).**
  `numEarlier_surj` (+ `_arr`): `numEarlier` hits every value `< count[len]`.
  `codeFor_of_value`: any `c ∈ [firstCode[len], firstCode[len]+count[len])` is a
  real symbol's codeword, and `walkCanonical`'s lookup
  `symbols[firstIndex[len] + (c - firstCode[len])]` returns exactly that symbol
  with `codeFor s = natToBits c len`. This is the error-soundness fact (no value
  matches that isn't a genuine tree leaf).
- `8b581167` **Step 3 bit bridges.** `bitReverse_succ`, `natToBits_bitReverse`:
  `walkCanonical`'s LSB-first accumulated value `bitReverse bitBuf.toNat k 0` has
  `natToBits = cwOf bitBuf.toNat k` — the exact codeword the spec consumes.

## Key finding: `walkCanonical = walkTree` is NOT exactly true

A dead branch reached exactly when `cnt = 0`: `walkTree` checks `.empty` before
`cnt` and returns `"invalid Huffman code"`, while `walkCanonical` checks `cnt`
first and returns `"unexpected end of input"`. Different error strings, so the
two functions are not equal. **Integration must be an output-equality
correspondence on success, not function equality.** On *success* both agree
(same `sym, bb, c, used`); they error on the same inputs (strings may differ).

So the right target is `walkCanonical_ok_iff_walkTree` (success-equivalence) or
`walkCanonical_ok_spec` (forward characterization). With `decodeSymCanon` and
`decodeSym` identical except `walkCanonical` vs `walkTree`, and the table being
the same (`buildTableCanonicalFast_eq` ∘ `buildTableCanonical_eq`, already
merged), the loop integration reduces to that fallback correspondence.

## Update: `walkCanonical` fully characterized (both directions, UInt64-land)

Since the original note, the runtime `walkCanonical` semantics are now **proven
in full**, with no BitReader/BufCorr dependency:

- **`walkCanonical_ok_spec`** (forward / soundness): a successful run consumes
  `used` bits (`1 ≤ used ≤ maxBits`, `used ≤ cnt`), advances the buffer by `used`
  (`bb = buf >>> used`, `c = cnt - used`), and returns the symbol whose canonical
  codeword is exactly `cwOf buf.toNat used`. Fuel induction `walkCanonical_go_ok`
  over the accumulated value `code·2^(used+1-len) + bitReverse buf.toNat …`.
- **`walkCanonical_complete`** (backward / completeness): if `codeFor s =
  cwOf buf.toNat L` with `L ≤ cnt`, the run succeeds returning `s` after `L`
  bits. Fuel induction `walkCanonical_go_complete`; prefix-freeness
  (`canonical_prefix_free`) blocks any early match at `len < L`.

Supporting (all proven, no sorry): `accum_step`, `and_one_toNat`,
`shr_one_toNat`, `ushr_succ`, `natToBits_append` (local copy of the private
upstream lemma). This is the heart of step 3 — `walkCanonical` provably accepts
exactly the genuine canonical codewords.

## Remaining work (BufCorr bridge + rewiring)

0. **Bridge `cwOf buf.toNat L = br.toBits.take L`** under `BufCorr` (`L ≤ cnt`):
   `cwOf`'s `j`-th bit is `buf.toNat.testBit j`, and `BufCorr.bits` gives
   `buf.toNat.testBit j = streamBit data (bitpos+j)` for `j < cnt`. Generalizes
   `cwOf_peekFast_eq_take` (`Zip/Spec/InflateTable.lean`) past the 9-bit window.
   With this + the two `walkCanonical` lemmas, `decodeSymCanon` matches the spec
   `decode.go`/`decodeWithTable` on success (and rejects iff the spec rejects).
1. **`walkCanonical_ok_spec`** (forward, DONE — see above):
   `walkCanonical (buildLongDecode lengths maxBits) maxBits bitBuf cnt =
   .ok (sym, bb, c, used)` ⟹ `1 ≤ used ≤ maxBits`, `used ≤ cnt`,
   `bb = bitBuf >>> used`, `c = cnt - used`, and `∃ s, sym = s.toUInt16 ∧
   codeFor lsList maxBits s = some (cwOf bitBuf.toNat used)`.
   Proof: fuel induction on `walkCanonical.go` over `maxBits + 1 - len`, tracking
   the matched value `cval = code·2^(used+1-len) + bitReverse bitBuf.toNat
   (used+1-len) 0`; the step uses `bitReverse_succ`, `UInt64.toNat_and` +
   `Nat.and_one_is_mod` (`(bitBuf &&& 1).toNat = bitBuf.toNat % 2`), and
   `UInt64.toNat_shiftRight` + `Nat.shiftRight_eq_div_pow`
   (`(bitBuf >>> 1).toNat = bitBuf.toNat / 2`). At the top (`len=1, code=0`)
   `cval = bitReverse bitBuf.toNat used 0`; apply `codeFor_of_value` then
   `natToBits_bitReverse` to land `codeFor s = cwOf bitBuf.toNat used`.
   Friction: tracking `bb = bitBuf >>> used` needs single-shift composition
   `(x >>> 1) >>> m = x >>> (m+1)` for `m+1 < 64` — no toolchain lemma found;
   prove via `UInt64.eq_of_toNat_eq` + `UInt64.toNat_shiftRight`.

2. **Reverse / error-soundness** to get `walkCanonical_ok_iff_walkTree` (or to
   `decode.go` directly): when `walkCanonical` errors, the spec also rejects.
   Uses `codeFor_of_value` (already proven) for "no spurious accept" and the
   bit/`cwOf` bridge to connect `cwOf bitBuf.toNat used` to `br.toBits.take used`
   (`cwOf_peekFast_eq_take` / `peekFast` machinery in `Zip/Spec/InflateTable.lean`
   and `BufCorr` in `Zip/Spec/InflateBufCorrect.lean`, exactly as `walkTree_corr`
   /`decodeSym_corr` do for the tree path).

3. **`decodeSymCanon` ↔ `decodeWithTable`**: short codes via the merged
   `buildTableCanonical_eq` + `decodeWithTable_eq`; long codes via (1)+(2). Mirror
   `decodeSym_corr` (`Zip/Spec/InflateBufCorrect.lean:729`).

4. **Loop rewiring**: make `goTreeFree`/`goTreeFreeU` non-`partial` (WF
   termination, measure as in the verified `Inflate.go`), prove the tree-free
   buffer decode equals (on success) the verified `decodeHuffmanFastBuf`, and
   transfer the `InflateBuf`/`Inflate` correctness chain — the analogue of the
   `#2680` table-level rewiring. Re-run `treefree-decode-bench` after the loop is
   non-`partial` to reconfirm the ~13% win.

## Reusable lemmas now available (all in `Zip.Native.HuffTree`)

`psumCount_mono`, `psumCount_succ_pred`, `buildFirstIndex_size`,
`numEarlier` (+ `_succ`, `_succ_arr`, `_lt`, `_lt_arr`, `_size_eq`, `_surj`,
`_surj_arr`), `map_toNat_getElem`, `place_upper`, `place_ne`,
`buildSymbols_placement`, `buildLongDecode_placement`, `countLengthsFast_eq`,
`codeFor_placed`, `codeFor_of_value`, `bitReverse_succ`, `natToBits_bitReverse`.
