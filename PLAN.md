# Current Plan

<!-- Rewritten at the start of each work session. -->
<!-- If a session ends with unchecked items, the next session continues here. -->

## Status: Completed

## Session type: implementation

## Goal: Prove readBits_toBits, reduce sorry count from 4 to 3 (or fewer)

### Steps

- [x] Search for available UInt32/Nat/BitVec lemmas in Lean 4.29.0-rc1
- [x] Add `Nat.or_two_pow_eq_add` to ZipForStd/Nat.lean
- [x] Prove `readBits_go_spec` loop invariant (induction on k)
- [x] Derive `readBits_toBits` from `readBits_go_spec` with acc=0, shift=0
- [x] Decompose `huffTree_decode_correct` into two steps
- [x] Prove `decode_go_decodeBits` (BitReader→bits step)
- [x] Wire up `huffTree_decode_correct` using both helper lemmas

### Next session priorities

1. **Prove `decodeBits_eq_spec_decode`** — show that the pure tree decode
   agrees with the spec's linear-search decode. Approach:
   - Define "tree maps codeword to symbol" predicate
   - Prove `insert` maintains it
   - Prove `fromLengths` establishes it for all canonical codes
   - Connect to `Huffman.Spec.decode`'s linear search
2. Prove `inflate_correct'` from `inflate_correct`
3. Work on `inflate_correct` (the main theorem)

### Proof approach notes for decodeBits_eq_spec_decode

The challenge is connecting two implementations of RFC 1951 §3.2.2:
- `fromLengths` (native): imperative with mutable arrays, builds tree
- `allCodes` → `codeFor` (spec): functional, computes each code independently

Both compute `nextCode[len] = (nextCode[len-1] + count[len-1]) << 1`.
An intermediate representation (e.g., a mapping from codewords to symbols)
could bridge the gap. Alternatively, prove both produce the same code for
each symbol, then connect tree insertion to table membership.
