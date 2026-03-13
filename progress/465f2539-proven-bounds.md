# Progress: Proven-bounds data access in ZstdHuffman.lean

**Date**: 2026-03-13 UTC
**Session type**: Feature
**Issue**: #1408
**PR**: #1426 (partial)

## What was accomplished

Converted 13 `data[pos + i]!` runtime-bounds-checked array accesses to
`data[pos + i]'(by omega)` proven-bounds accesses in
`parseCompressedLiteralsHeader` (Zip/Native/ZstdHuffman.lean).

### Implementation pattern

The bounds guard was restructured from:
```lean
if data.size < pos + N then throw "..."
let b0 := data[pos]!.toNat
```
to:
```lean
if h : pos + N ≤ data.size then
  let b0 := data[pos]'(by omega) |>.toNat
  ...
else throw "..."
```

This captures the bound hypothesis `h` via `dite` so `omega` can prove
each array access is in bounds.

### Spec proof updates (Zip/Spec/ZstdHuffman.lean)

Updated 5 theorems whose proofs unfold `parseCompressedLiteralsHeader`:
- `parseCompressedLiteralsHeader_headerBytes_ge`
- `parseCompressedLiteralsHeader_headerSize`
- `parseCompressedLiteralsHeader_fourStreams`
- `parseCompressedLiteralsHeader_regen_bound`
- `parseCompressedLiteralsHeader_succeeds`

Changes: swapped `nomatch`/`simp` branch order (success is now the
`then` branch of `dite`, not the continuation after `ite`), replaced
`↓reduceIte` with `↓reduceDIte`, and removed unused `bind`/`Except.bind`
simp arguments.

### Patterns skipped

- **parseHuffmanWeightsDirect** (1 pattern): The `data[pos + i]!` is
  inside a `for` loop body. Converting to proven-bounds embeds proof
  terms in the forIn lambda, breaking `forIn_range_always_ok'`-based
  spec proofs that must match the exact unfolded body term. Reverted.

- **parseHuffmanTreeDescriptor** (5 patterns): Spec proofs in
  `Zip/Spec/ZstdHuffman.lean` unfold this function and reference
  `data[pos]!` directly via `array_get!Internal_eq`. Would need
  simultaneous proof updates.

## Key insight

When a function uses `data[i]'(proof)` inside a `for` loop, the proof
term gets embedded in the forIn lambda during unfolding. This makes it
impossible to pattern-match the body in `suffices` statements or
`forIn_range_always_ok'` calls, because the proof terms are opaque and
differ between the unfolded definition and the proof context. Functions
with `for` loops that have spec proofs unfolding them should keep `!`
access until the proof infrastructure is redesigned.

## Metrics

- Patterns converted: 13 of 19 data byte reads (68%)
- Sorry count: unchanged
- Build: all Lean files pass (FFI build requires nix-shell — pre-existing)
- Tests: cannot run due to pre-existing zstd_ffi.o build failure
