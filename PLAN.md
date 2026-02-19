# Current Plan

<!-- Rewritten at the start of each work session. -->
<!-- If a session ends with unchecked items, the next session continues here. -->

## Status: Complete

## Session type: implementation

## Objective

Integrate the native pure-Lean decompressor as an alternative backend for
ZIP and tar.gz code paths. This completes the last Phase 2 deliverable.

## Deliverables

- [x] **Archive.lean integration**: `useNative` parameter on `extract`,
      `extractFile`, `readEntryData`. Uses `Zip.Native.Inflate.inflate`
      and `Crc32.Native.crc32` when true.
- [x] **Tar.lean integration**: `extractTarGzNative` reads entire gzip
      file, decompresses with `Zip.Native.GzipDecode.decompress`, then
      parses tar from a ByteArray-backed stream. O(file_size) memory.
- [x] **Conformance tests**: `ZipTest/NativeIntegration.lean` — creates
      ZIP and tar.gz with FFI, extracts with native, verifies identical.
- [x] **Wire up imports**: Updated `Zip.lean` (already had imports) and
      `ZipTest.lean`.
