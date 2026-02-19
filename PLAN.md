# Current Plan

<!-- Rewritten at the start of each work session. -->
<!-- If a session ends with unchecked items, the next session continues here. -->

## Status: In progress

## Session type: implementation

## Objective

Implement native gzip (RFC 1952) and zlib (RFC 1950) framing layers on top
of the existing pure Lean DEFLATE decompressor. This enables integration
with existing ZIP/tar code paths and completes Phase 2 deliverables.

## Deliverables

- [ ] **Expose inflate ending position**: Add `Inflate.inflateRaw` that returns
      `(ByteArray × Nat)` where `Nat` is the byte position after the DEFLATE
      stream. Needed so the framing layer can read the trailer.
- [ ] **Gzip decompression** (`Zip/Native/Gzip.lean`): Parse gzip header
      (magic, method, flags, skip optional fields), inflate, parse trailer
      (CRC32 + ISIZE), verify checksums. Support concatenated gzip streams.
- [ ] **Zlib decompression** (`Zip/Native/Gzip.lean`): Parse zlib header
      (CMF + FLG, check bits), inflate, parse trailer (Adler32 big-endian),
      verify checksum.
- [ ] **Auto-detect function**: Detect gzip vs zlib vs raw deflate from
      the first bytes.
- [ ] **Conformance tests** (`ZipTest/NativeGzip.lean`): Compare native
      gzip/zlib decompress with FFI for various inputs.
- [ ] **Wire up**: Add imports to `Zip.lean` and `ZipTest.lean`.
