# Current Plan

<!-- Rewritten at the start of each work session. -->
<!-- If a session ends with unchecked items, the next session continues here. -->

## Status: Completed

## Session type: implementation

## Objective

Begin Phase 2 (DEFLATE decompressor) — implement the BitReader and core
DEFLATE infrastructure: stored blocks and fixed Huffman decoding.

## Deliverables

- [x] `Zip/Native/BitReader.lean` — bit-level reader (LSB-first) for ByteArray
- [x] `Zip/Native/Inflate.lean` — DEFLATE decompressor: block parsing,
      stored blocks, fixed Huffman tables, LZ77 back-references
- [x] `ZipTest/NativeInflate.lean` — conformance tests (FFI compress → native decompress)
- [x] Wire up in `Zip.lean`, `ZipTest.lean`, `lakefile.lean`

## Design Notes

DEFLATE (RFC 1951) operates on a bit stream (LSB-first within each byte).
Three block types:
- Type 0: Stored (uncompressed, byte-aligned)
- Type 1: Fixed Huffman codes
- Type 2: Dynamic Huffman codes

BitReader: mutable state tracking byte position + bit offset within byte.
Huffman tree: simple binary tree; decode by reading one bit at a time.

All three block types implemented and tested in this session.
