# Security Inventory

Living inventory of trusted components, boundary-facing subsystems, and
known gaps that sit outside the formally verified codec core.

## Status Labels

- `proved-in-repo`: covered by Lean proofs in this repository
- `guarded-locally`: not fully proved, but protected by explicit checks and limits
- `tested-only`: covered by tests/conformance but missing stronger assurance
- `upstream-risk`: trusted dependency with a known or suspected upstream issue

## Trusted Computing Base

### Lean Runtime: `ByteArray`, scalar-array allocation, `IO`

- Status: `upstream-risk`
- Why trusted: all Lean code ultimately relies on runtime allocation and
  `IO` primitives for `ByteArray`, `Handle.read`, and stream operations.
- Current local guardrails:
  - `Zip/Archive.lean` checks `n.toUSize.toNat == n` before `Handle.read`
  - `Zip/Archive.lean` checks file-bounds for central directory before reading it
  - native inflate APIs carry explicit `maxOutputSize` bounds
- Known concern:
  - crafted oversized reads can become runtime-allocation hazards if
    unchecked sizes reach `Handle.read`
- Upstream tracking:
  - Report: no upstream link yet — local tracking only. The April 2026
    report against Lean runtime allocation/read paths is recorded in
    this repository (see *"Current local guardrails"* above and
    *"Local guard inventory for `Handle.read` and `Stream.read`"*
    below) but has not yet been filed as a leanprover/lean4 issue.
  - Status: not yet reported upstream (as of 2026-04-22). An honest
    search of `progress/`, the lean-zip issue tracker, and
    leanprover/lean4 (`allocation`, `ByteArray`, `Handle.read`
    queries) did not find a matching upstream issue. Re-triage
    required once one is filed.
  - Local regression coverage (fixtures + assertion sites that guard
    this attack surface today):
    - `testdata/zip/malformed/oversized-compressed-size.zip` —
      oversized 32-bit `compressedSize`; asserted in
      `ZipTest/ZipFixtures.lean`.
    - `testdata/zip/malformed/oversized-zip64-compressed-size.zip` —
      oversized ZIP64 `compressedSize` (PR #1543); asserted in
      `ZipTest/ZipFixtures.lean`.
    - `testdata/zip/malformed/oversized-zip64-uncompressed-size.zip` —
      oversized ZIP64 `uncompressedSize` (PR #1544); asserted in
      `ZipTest/ZipFixtures.lean`.
    - `testdata/zip/malformed/cd-lh-method-mismatch.zip` and
      `cd-lh-size-mismatch.zip` — CD vs local-header mismatches
      (PR #1554); asserted in `ZipTest/ZipFixtures.lean`.
    - Bomb-limit regression tests for `Gzip.decompress`,
      `RawDeflate.decompress`, and `Zip.Native.GzipDecode.decompress`
      (PR #1560); coverage in `ZipTest/Gzip.lean`,
      `ZipTest/RawDeflate.lean`, and `ZipTest/NativeGzip.lean`.
    - Bomb-limit regression tests for `Archive.extract` /
      `Archive.extractFile` / `Tar.extract` / `Tar.extractTarGz`
      (PR #1561); coverage in `ZipTest/Archive.lean` and
      `ZipTest/Tar.lean`.
  - Local guardrails (cross-ref *"Current local guardrails"* above):
    `readExact`'s `Nat → USize` roundtrip before every `Handle.read`;
    `assertSpanInFile` for local-header / name+extra / compressed-data
    spans in `Zip/Archive.lean` (PR #1497); ZIP `maxCentralDirSize`
    (default 64 MiB) and `maxEntrySize` caps on `Archive.extract` /
    `Archive.extractFile`; tar `maxEntrySize` cap on `Tar.extract` /
    `Tar.extractTarGz` / `Tar.extractTarGzNative`; native inflate
    `maxOutputSize` caps (`Zip.Native.Inflate.inflate` default 1 GiB;
    `Zip.Native.GzipDecode.decompress`, `Zip.Native.ZlibDecode.decompress`,
    `Zip.Native.decompressAuto` default 256 MiB — see
    *"Decompression Limit Inventory"* below for the full table).
- Missing work:
  - prove or enforce stronger preconditions before every `Handle.read`
    and `Stream.read` driven by archive metadata
    - see *"Local guard inventory for `Handle.read` and `Stream.read`"*
      below for the per-site audit of what protections are currently in
      place
  - file or link the upstream Lean runtime issue so the *"Report"* and
    *"Status"* fields in *"Upstream tracking"* above can be updated
    with a concrete target
- Recent wins:
  - oversized ZIP64 compressed-size fixture — PR #1543
    (`testdata/zip/malformed/oversized-zip64-compressed-size.zip`)
  - oversized ZIP64 uncompressed-size fixture — PR #1544
    (`testdata/zip/malformed/oversized-zip64-uncompressed-size.zip`)
    — together these close the previous *"add regression fixtures for
    oversized ZIP64 size claims"* Missing-work bullet

### zlib via C FFI

- Components: [c/zlib_ffi.c](/home/kim/lean-zip/c/zlib_ffi.c:1)
- Status: `guarded-locally`
- Why trusted: whole-buffer and streaming compression/decompression are
  implemented in C and depend on zlib plus libc allocation behavior.
- Current local guardrails:
  - `UINT_MAX` guards on whole-buffer input sizes
  - overflow-aware buffer growth helpers
  - explicit `max_output` check in whole-buffer decompression
  - state finalizers for streaming objects
  - [`scripts/sanitize-ffi.sh`](/home/kim/lean-zip/scripts/sanitize-ffi.sh)
    rebuilds `c/zlib_ffi.c` under `-fsanitize=address,undefined` and
    runs the test suite so FFI-level memory and UB errors surface as
    runtime traps; the April 2026 tree is ASan + UBSan clean.
  - [`ZipTest/FuzzInflate.lean`](/home/kim/lean-zip/ZipTest/FuzzInflate.lean)
    + [`scripts/fuzz-inflate.sh`](/home/kim/lean-zip/scripts/fuzz-inflate.sh)
    land a deterministic xorshift-seeded fuzz driver that feeds every
    whole-buffer FFI decoder (`Zlib.decompress`, `Gzip.decompress`,
    `RawDeflate.decompress`) and the streaming `Gzip.InflateState`
    path with pseudo-random inputs at sizes {0, 1, 16, 512, 8192,
    65536} and chunk sizes {1, 7, 31, 127}. `lake exe test` runs a
    100-iteration fixed-seed smoke check (≈ 10 ms); the `fuzz_inflate`
    lake executable takes a wall-clock budget (default 30 s, override
    via CLI arg or `LEAN_ZIP_FUZZ_SECONDS`). For sanitizer coverage,
    reuse the `ZLIB_CFLAGS / ZLIB_LDFLAGS / LD_PRELOAD` recipe from
    `scripts/sanitize-ffi.sh` — the fuzz driver is linked into
    `.lake/build/bin/fuzz_inflate` which inherits the same sanitizer
    runtime when built under those flags. Any `IO.userError` is the
    handled case; an uncaught panic, segfault, or ASan/UBSan trap
    terminates with non-zero status.
- Missing work:
  - maintain sanitizer coverage for all FFI entry points
  - add dedicated malformed-input regression tests for streaming paths
  - any new `malloc`/`realloc`/`calloc`/`grow_buffer` call, or change
    to `grow_buffer` semantics, in `c/zlib_ffi.c` requires re-running
    the audit below and updating the snapshot table. The helper
    [`scripts/check-c-allocations.sh`](/home/kim/lean-zip/scripts/check-c-allocations.sh)
    prints a one-line warning at PR-review time if the count of
    `malloc`/`realloc`/`calloc` mentions drifts from the baseline.

#### Allocation site audit (`c/zlib_ffi.c`)

Snapshot of every `malloc`, `realloc`, `calloc`, and `grow_buffer`
call in [c/zlib_ffi.c](/home/kim/lean-zip/c/zlib_ffi.c) as of
2026-04-22. `grow_buffer` is the shared doubling helper at
[c/zlib_ffi.c:54](/home/kim/lean-zip/c/zlib_ffi.c:54); its
`*buf_size > SIZE_MAX/2` overflow check and `free(buf)`-on-failure
semantics are the linchpin for every decompression-side growth
site. Callers of `grow_buffer` must NOT free `buf` themselves on a
`NULL` return — it has already been freed.

| Site (line) | Function | Bound | Failure handling | Notes |
|---|---|---|---|---|
| [c/zlib_ffi.c:39](/home/kim/lean-zip/c/zlib_ffi.c:39) | `mk_zlib_error` (shared error-string formatter; reached by every FFI entry point on a non-OK zlib return) | `prefix_len + detail_len + 3`, with `prefix_len > SIZE_MAX - detail_len - 3` overflow guard at [c/zlib_ffi.c:34](/home/kim/lean-zip/c/zlib_ffi.c:34) | returns `mk_io_error("zlib error: out of memory while formatting error")` (no resource held at this point) | `buf` is `free`d immediately after `snprintf` + `mk_io_error`; the Lean string owns its own copy. Allocation is small (≤ 256 + message). |
| [c/zlib_ffi.c:60](/home/kim/lean-zip/c/zlib_ffi.c:60) | `grow_buffer` (shared helper; caller-dependent) | `*buf_size *= 2`, pre-checked by `if (*buf_size > SIZE_MAX / 2)` at [c/zlib_ffi.c:55](/home/kim/lean-zip/c/zlib_ffi.c:55); on overflow, frees old `buf` and returns `NULL` | returns `NULL`; **frees the old `buf` on `realloc` failure** ([c/zlib_ffi.c:62](/home/kim/lean-zip/c/zlib_ffi.c:62)) | Every caller treats `NULL` as "buffer already freed" — no `free(buf)` on the caller's error path. |
| [c/zlib_ffi.c:162](/home/kim/lean-zip/c/zlib_ffi.c:162) | `decompress_inflate` — reached by `lean_zlib_decompress`, `lean_gzip_decompress`, `lean_raw_deflate_decompress` | `initial_decompress_buf(src_len)` at [c/zlib_ffi.c:71](/home/kim/lean-zip/c/zlib_ffi.c:71): `src_len * 4` with a `SIZE_MAX/4` overflow guard, floored at 1024. `src_len ≤ UINT_MAX` already enforced by the caller at [c/zlib_ffi.c:143](/home/kim/lean-zip/c/zlib_ffi.c:143) | `inflateEnd(&strm); return mk_io_error("<label>: out of memory")` | Initial whole-buffer decompression buffer. |
| [c/zlib_ffi.c:173](/home/kim/lean-zip/c/zlib_ffi.c:173) | `decompress_inflate` (same callers) | `grow_buffer` doubling, capped at `SIZE_MAX/2` | on `NULL`: `inflateEnd(&strm); return mk_io_error("<label>: out of memory")` — does **not** re-free `buf` (`grow_buffer` already did) | The `max_output` cap (when non-zero) is checked **after** `inflate` writes into the grown buffer ([c/zlib_ffi.c:191](/home/kim/lean-zip/c/zlib_ffi.c:191)), not before `grow_buffer` — see the summary below. |
| [c/zlib_ffi.c:320](/home/kim/lean-zip/c/zlib_ffi.c:320) | `lean_gzip_deflate_new` (streaming compression state constructor) | fixed `sizeof(deflate_state)` (small struct; zlib's internal `deflateInit2` buffers are allocated separately inside zlib) | `return mk_io_error("gzip deflate new: out of memory")` (no zlib stream yet) | `calloc` zero-initialises `finished` so the finalizer always makes a well-defined `deflateEnd` decision. |
| [c/zlib_ffi.c:353](/home/kim/lean-zip/c/zlib_ffi.c:353) | `lean_gzip_deflate_push` (streaming compression, per-chunk output buffer) | fixed 65 536 bytes initial | `return mk_io_error("gzip deflate push: out of memory")`. **Does not** call `deflateEnd` — the `deflate_state` remains live and the finalizer will clean it up | Grown by `grow_buffer` in the loop. |
| [c/zlib_ffi.c:361](/home/kim/lean-zip/c/zlib_ffi.c:361) | `lean_gzip_deflate_push` | `grow_buffer` doubling, capped at `SIZE_MAX/2` | on `NULL`: `return mk_io_error("gzip deflate push: out of memory")` (no `free`, no `deflateEnd` — finalizer cleans the state) | No per-call output cap; bounded only by `grow_buffer`'s `SIZE_MAX/2` guard. |
| [c/zlib_ffi.c:397](/home/kim/lean-zip/c/zlib_ffi.c:397) | `lean_gzip_deflate_finish` (streaming compression, `Z_FINISH` flush buffer) | fixed 65 536 bytes initial | `return mk_io_error("gzip deflate finish: out of memory")`. State stays live; finalizer calls `deflateEnd` | Used by both gzip and raw-deflate streaming paths (they share the same `deflate_state`). |
| [c/zlib_ffi.c:404](/home/kim/lean-zip/c/zlib_ffi.c:404) | `lean_gzip_deflate_finish` | `grow_buffer` doubling, capped at `SIZE_MAX/2` | on `NULL`: `return mk_io_error("gzip deflate finish: out of memory")` (no re-free, no `deflateEnd` — finalizer cleans) | No per-call output cap. |
| [c/zlib_ffi.c:435](/home/kim/lean-zip/c/zlib_ffi.c:435) | `lean_gzip_inflate_new` (streaming decompression state constructor; `MAX_WBITS + 32` auto-detect) | fixed `sizeof(inflate_state)` | `return mk_io_error("gzip inflate new: out of memory")` | `calloc` zero-initialises `finished`. |
| [c/zlib_ffi.c:468](/home/kim/lean-zip/c/zlib_ffi.c:468) | `lean_gzip_inflate_push` (streaming decompression, per-chunk output buffer; shared with raw inflate) | fixed 65 536 bytes initial | `return mk_io_error("gzip inflate push: out of memory")`. State stays live | No `max_output` parameter on this path — caller is responsible for whole-archive bounding. |
| [c/zlib_ffi.c:479](/home/kim/lean-zip/c/zlib_ffi.c:479) | `lean_gzip_inflate_push` | `grow_buffer` doubling, capped at `SIZE_MAX/2` | on `NULL`: `return mk_io_error("gzip inflate push: out of memory")` (no re-free, no `inflateEnd` — finalizer cleans) | No per-call output cap. |
| [c/zlib_ffi.c:607](/home/kim/lean-zip/c/zlib_ffi.c:607) | `lean_raw_deflate_new` (streaming raw-deflate compression state) | fixed `sizeof(deflate_state)` | `return mk_io_error("raw deflate new: out of memory")` | Reuses the shared `lean_gzip_deflate_push` / `_finish` helpers via `g_deflate_class`. |
| [c/zlib_ffi.c:628](/home/kim/lean-zip/c/zlib_ffi.c:628) | `lean_raw_inflate_new` (streaming raw-deflate decompression state; `-MAX_WBITS`) | fixed `sizeof(inflate_state)` | `return mk_io_error("raw inflate new: out of memory")` | Reuses the shared `lean_gzip_inflate_push` helper via `g_inflate_class`. |

Summary — what this pattern catches and what it does not:

- **Catches**: `size_t` overflow in the doubling step (`SIZE_MAX/2` guard in `grow_buffer`); individual `malloc`/`realloc`/`calloc` failure (every site has a `NULL`-check and returns an `IO` error); double-free after `grow_buffer` failure (callers never re-`free(buf)` on a `NULL` return because `grow_buffer` already did); and over-4 GiB whole-buffer inputs (guarded at the caller before any allocation, via `src_len > UINT_MAX` checks).
- **Does NOT catch**:
  1. A decompression bomb passed to a whole-buffer decoder with `max_output == 0` (the "no limit" sentinel) can still walk the buffer up to `SIZE_MAX/2` before `grow_buffer` refuses: the `max_output` check at [c/zlib_ffi.c:191](/home/kim/lean-zip/c/zlib_ffi.c:191) fires only **after** `inflate` has written into the already-grown buffer. The guard is therefore a "refuses to keep going" limit, not a "refuses to allocate" limit — see the *Decompression Limit Inventory* below for the caller-level mitigation.
  2. The streaming entry points (`lean_gzip_deflate_push`, `lean_gzip_deflate_finish`, `lean_gzip_inflate_push`) accept no output-size parameter at all. Their per-call output buffer is bounded only by `grow_buffer`'s `SIZE_MAX/2` guard; whole-archive bounding is the caller's problem.
  3. zlib's own internal allocations (`inflateInit2` / `deflateInit2` stream state, Huffman tables, sliding window) are made via zlib's `zalloc` (default `malloc`). They are not enumerated here — they live inside zlib itself and sit under the "upstream-risk" portion of this entry's trust status.

### `Zip.Native.Inflate` and verified DEFLATE core

- Status: `proved-in-repo`
- Components:
  - [Zip/Native/Inflate.lean](/home/kim/lean-zip/Zip/Native/Inflate.lean:1)
  - [Zip/Spec/InflateCorrect.lean](/home/kim/lean-zip/Zip/Spec/InflateCorrect.lean:1)
  - [Zip/Spec/DeflateRoundtrip.lean](/home/kim/lean-zip/Zip/Spec/DeflateRoundtrip.lean:1)
- Notes:
  - this is the strongest-assurance part of the repo
  - remaining risk comes from framing, parser boundaries, runtime, and limits

## Boundary-Facing Subsystems

### ZIP Archive Reader/Extractor

- Components: [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean:1)
- Status: `guarded-locally`
- Trust boundary:
  - parses EOCD, central directory, ZIP64 metadata, local headers, names,
    offsets, compressed sizes, and extraction paths from untrusted files
- Current guardrails:
  - central directory must fit within file size
  - configurable `maxCentralDirSize`
  - local `readExact` checks `Nat -> USize` roundtrip before `Handle.read`
  - `assertSpanInFile` validates local-header, name+extra, and compressed-data
    spans against actual file size before each attacker-controlled `Handle.read`
    in `readEntryData`
  - regression fixture `testdata/zip/malformed/oversized-compressed-size.zip`
    exercises the oversized-compressedSize rejection path
  - path traversal blocked via `Binary.isPathSafe`
  - CRC and final size checked after extraction
- Missing work:
  - Executed — bounded-read helpers for `Handle`/`Stream` landed in
    PR #1608 (Track E P5.1); `SpanInFile` predicate + IO reduction
    lemmas in PR #1636 (Track E P5.2); `Archive`/`Tar` callers
    migrated to the helpers in PR #1626 (Track E P5.3). No residual
    sites currently identified at this layer.
  - CD-vs-EOCD comment-length consistency not yet checked — PR #1733
    landed the `totalEntries` dimension of this category, PR #1742
    the disk-number dimension, and PR #1752 the sibling
    `numEntriesThisDisk`; the trailing comment-length field remains
    silently accepted. Trailing bytes past `EOCD.commentLen` are not
    cross-checked against the file tail, which is one of the classic
    ZIP-smuggling vectors.
- Recent wins:
  - central-directory vs. local-header mismatch checks — PR #1554
    (`testdata/zip/malformed/cd-lh-method-mismatch.zip`,
    `cd-lh-size-mismatch.zip`)
  - CD-vs-LH flags (bit-3-masked) consistency check — PR #1715
    (`testdata/zip/malformed/cd-lh-flags-mismatch.zip`) rejects the
    bit-11 UTF-8-name smuggling vector before the payload read
  - CD-vs-EOCD `totalEntries` consistency check — PR #1733
    (`testdata/zip/malformed/eocd-numentries-mismatch.zip`) rejects
    EOCD-declared count ≠ parsed CD entry count
  - EOCD disk-number consistency check — PR #1742
    (`testdata/zip/malformed/eocd-disknum-mismatch.zip`) rejects
    any archive with nonzero `numberOfThisDisk` or `diskWhereCDStarts`
    (post-ZIP64-override); lean-zip supports single-disk archives only
    and the writer already hard-codes both fields to `0`
  - CD per-entry `diskNumberStart` consistency check — PR #1759
    (`testdata/zip/malformed/cd-entry-disknum-mismatch.zip`) rejects
    archives where any CD entry carries a nonzero APPNOTE §4.4.11
    `diskNumberStart` field at CD offset +34; per-entry sibling of
    PR #1742, together closing the full disk-number smuggling
    dimension on single-disk archives (writer-side at the
    `Binary.zeros`-initialised CD header — see *"disk number start
    (34)"* comment around
    [Zip/Archive.lean:131](/home/kim/lean-zip/Zip/Archive.lean:131))
  - EOCD `numEntriesThisDisk` vs. `totalEntries` consistency check —
    PR #1752 (`testdata/zip/malformed/eocd-numentries-thisdisk-mismatch.zip`)
    rejects archives where the sibling EOCD entry-count fields disagree
    (single-disk archives must have them equal; writer-side at
    [Zip/Archive.lean:156-157](/home/kim/lean-zip/Zip/Archive.lean:156)
    and :170-171)
  - ZIP64/standard-EOCD override sentinel check — PR #1745
    (`testdata/zip/malformed/eocd-zip64-override-nosentinel.zip` —
    `cdOffset` slot at [Zip/Archive.lean:399](/home/kim/lean-zip/Zip/Archive.lean:399)),
    PR #1905
    (`testdata/zip/malformed/eocd-zip64-override-cdsize-mismatch.zip` —
    `cdSize` slot at [Zip/Archive.lean:396](/home/kim/lean-zip/Zip/Archive.lean:396)),
    PR #1908
    (`testdata/zip/malformed/eocd-zip64-override-totalentries-mismatch.zip` —
    `totalEntries` slot at [Zip/Archive.lean:402](/home/kim/lean-zip/Zip/Archive.lean:402)),
    PR #1911
    (`testdata/zip/malformed/eocd-zip64-override-diskcd-mismatch.zip` —
    `diskWhereCDStarts` slot at [Zip/Archive.lean:408](/home/kim/lean-zip/Zip/Archive.lean:408)),
    and PR #1922
    (`testdata/zip/malformed/eocd-zip64-override-entriesthisdisk-mismatch.zip` —
    `numEntriesThisDisk` slot at [Zip/Archive.lean:411](/home/kim/lean-zip/Zip/Archive.lean:411))
    reject archives where the standard EOCD carries a real value
    instead of the APPNOTE §4.3.16 sentinel (`0xFFFFFFFF` / `0xFFFF`)
    in any of `cdSize`/`cdOffset`/`totalEntries`/`numberOfThisDisk`/
    `diskWhereCDStarts`/`numEntriesThisDisk` that the ZIP64 record
    overrides with a numerically different value. The check is relaxed
    to "sentinel or numeric match" to accommodate real-world producers
    such as Go's `archive/zip` that emit real zeros in the standard
    EOCD's disk-number fields when ZIP64 is used (see
    `testdata/zip/interop/go-zip64.zip`). Closes the
    parser-differential smuggling vector where one reader trusts the
    standard EOCD and another trusts the ZIP64 override. Per-slot
    regression coverage now pins the `cdOffset`, `cdSize`,
    `totalEntries`, `diskWhereCDStarts`, and `numEntriesThisDisk`
    slots; the remaining `numberOfThisDisk` slot (line 405) shares
    the same throw shape and is covered by symmetric code review
    pending its dedicated per-slot fixture (sibling issue #1902 in
    flight as PR #1909)
  - ZIP64 EOCD64 self-declared record-size check — PR #1761
    (`testdata/zip/malformed/zip64-eocd64-bad-recsize.zip`) rejects
    archives whose EOCD64 `size of this record` field (APPNOTE §4.3.14,
    at `bufPos + 4`) is not exactly `44` — the v1 EOCD64 shape lean-zip
    produces and consumes. lean-zip reads the EOCD64 at fixed per-field
    offsets from a hard-coded 56-byte layout; a stricter parser that
    trusts the self-declared length would read past or short of that,
    yielding a parser-differential smuggling vector (writer-side at
    [Zip/Archive.lean:142](/home/kim/lean-zip/Zip/Archive.lean:142)
    hard-codes `44`). Additional regression coverage from PR #1889
    (`testdata/zip/malformed/zip64-eocd64-v2-record.zip`) pins the
    rejection behaviour against the APPNOTE §4.3.14.2 v2 shape: an
    internally-consistent 72-byte record with `recSize=60` and a
    16-byte "zip64 extensible data sector" in the strong-encryption
    shape. lean-zip does not implement strong encryption (SES), so v2
    records remain rejected by policy; the fixture closes the
    documentation gap flagged by the post-#1843 summarize
    ([progress/20260424T203421Z_90d1e22c-summarize-post-1843.md](/home/kim/lean-zip/progress/20260424T203421Z_90d1e22c-summarize-post-1843.md))
    between the generic `recSize=0` boundary (existing fixture) and
    the v2-specific shape
  - ZIP64 EOCD64 `versionMadeBy` spec-version upper-bound check — PR #1826
    (`testdata/zip/malformed/zip64-eocd64-versionmadeby-too-high.zip`)
    rejects archives whose EOCD64 `versionMadeBy` field (APPNOTE
    §4.4.2.1 / §4.4.2.2, at `bufPos + 12`) carries a lower byte greater
    than `63` (spec version 6.3) at `findEndOfCentralDir` time
    ([Zip/Archive.lean:337](/home/kim/lean-zip/Zip/Archive.lean:337)).
    The low byte of `versionMadeBy` is the "version of the ZIP
    specification" in decimal-coded form (APPNOTE-defined values 1.0
    through 6.3, encoded `10`..`63`); any higher value is either a
    forward-looking extension lean-zip does not support or a crafted
    smuggle targeting readers that don't validate the field.
    Writer-side at
    [Zip/Archive.lean:153](/home/kim/lean-zip/Zip/Archive.lean:153)
    emits `3 * 256 + 45 = 0x032D`, so the writer always satisfies the
    bound (`45 ≤ 63`). Only the lower byte is checked — real archives
    vary widely in host-OS code (upper byte: Info-ZIP emits `3`,
    Windows producers `11` NTFS, etc.); the lower byte is a pure
    spec-version field with a well-defined APPNOTE maximum. Placed
    immediately after the record-size check so the version-field guard
    runs before any attacker-controlled size or offset is consumed.
    Archive-level counterpart to the per-entry CD+4 `versionMadeBy`
    upper-bound fixture (issue #1812 / PR #1820,
    `cd-entry-versionmadeby-too-high.zip`); together the two close the
    `versionMadeBy` upper-bound dimension across both ZIP layers
    (EOCD64 record and per-entry CD). Interop sweep:
    `testdata/zip/interop/go-zip64.zip` — the only interop fixture
    with an EOCD64 — has `versionMadeBy=0x002d` (low byte `45`),
    comfortably below the bound
  - ZIP64 EOCD64 `versionNeededToExtract` upper-bound check — PR #1852
    (`testdata/zip/malformed/zip64-eocd64-versionneeded-too-high.zip`)
    rejects archives whose EOCD64 `versionNeededToExtract` field
    (APPNOTE §4.4.3.2, at `bufPos + 14`) exceeds `63` (spec version
    6.3, the APPNOTE-defined maximum) at `findEndOfCentralDir` time.
    The field declares the minimum ZIP specification version needed
    to interpret the EOCD64 record; any higher value is either a
    forward-looking extension lean-zip does not support or a crafted
    smuggle against strict readers. Writer-side at
    [Zip/Archive.lean:150](/home/kim/lean-zip/Zip/Archive.lean:150)
    hard-codes `45` (EOCD64 requires ZIP64 support, §4.4.3.2), so the
    bound `45 ≤ 63` holds trivially for every lean-zip-produced
    archive. Upper-bound sibling of the lower-bound `≥ 45` check
    (issue #1758 / PR #1764); together the two bounds close the
    EOCD64 `versionNeededToExtract` two-sided-bound dimension.
    Archive-level analog of the per-entry CD +6 upper bound
    (PR #1807, `cd-version-needed-too-high.zip`), which caps the
    per-entry field at `45`; the archive-level EOCD64 cap is `63`
    because APPNOTE §4.4.3.2 documents the field as the version
    needed to *interpret the record* rather than to extract the
    largest entry. Interop sweep across
    `testdata/zip/{interop,malformed}/*.zip` reports every EOCD64
    `versionNeededToExtract` at `45`, comfortably below the bound
  - ZIP64 EOCD64 record archive-layout invariant — PR #1856
    (`testdata/zip/malformed/zip64-eocd64-overlap-locator.zip`)
    rejects archives whose Locator-declared `eocd64Offset` plus the
    56-byte v1 EOCD64 record reaches into or past the Locator at
    `findEndOfCentralDir` time
    ([Zip/Archive.lean:306](/home/kim/lean-zip/Zip/Archive.lean:306)).
    APPNOTE §4.3.6 pins the ZIP64 trailer layout as `[CD] [EOCD64]
    [Locator] [EOCD]`, so a legitimate archive satisfies
    `eocd64Offset + 56 ≤ locatorPos = eocdPos - 20` — the EOCD64
    record must end strictly before the Locator begins. Pre-PR
    reader silently let the claimed EOCD64 overlap the Locator (or
    claim to start anywhere inside it), reading Locator bytes as the
    tail of the EOCD64 record — classic parser-differential /
    layout-smuggling vector where a strict peer reader rejects and
    lean-zip accepts. Writer-side at
    [Zip/Archive.lean:148-164](/home/kim/lean-zip/Zip/Archive.lean:148)
    emits the three records contiguously in APPNOTE order, so the
    invariant holds trivially for every lean-zip-produced archive.
    Buffer-relative form `bufPos + 56 ≤ pos - 20` matches the
    surrounding `bufPos`/`pos` arithmetic and is well-defined under
    `Nat` subtraction via the outer `pos ≥ 20` guard. Placed
    immediately after the `sigEOCD64` match so the layout check
    runs before the record-size / versionMadeBy / versionNeeded
    guards — error attribution stays tightly scoped to
    layout-shape failures. The pre-existing `bufPos + 56 ≤
    data.size` buffer-readability check remains as defense-in-depth
    but is now strictly weaker than the layout invariant for any
    archive whose buffer extends past the Locator. Peer-parser
    confirmation: CPython's `zipfile._EndRecData64` enforces the
    same invariant (`if reloff > offset: raise BadZipFile("Corrupt
    zip64 end of central directory locator")`) — the new guard
    brings lean-zip into alignment with a strict reference
    implementation. Archive-level macro sibling: `cdOffset + cdSize
    ≤ eocdPos` (issue #1799 / in-flight PR #1809). Per-entry micro
    sibling: `localOffset + 30 ≤ cdOffset` (PR #1813). Together the
    three invariants close the ZIP archive-layout dimension across
    the standard-EOCD macro, the ZIP64-EOCD64 macro, and the
    per-entry micro granularities. Interop pre-flight swept
    `testdata/zip/interop/*.zip`: only `go-zip64.zip` carries an
    EOCD64 + Locator pair, and its `eocd64Offset + 56 = 200 =
    locatorPos` satisfies the invariant tightly (EOCD64 ends
    exactly at Locator start). Net-new dimension observed during
    the ZIP64-layer archive-layout coverage sweep
  - CD/LH extra-data sub-field structural check — PR #1788
    (`testdata/zip/malformed/cd-extra-overrun-datasize.zip`) rejects
    CD/LH entries whose extra-data contains a sub-field whose declared
    `dataSize` extends past the end of the extra-data blob (APPNOTE §4.5
    *"Extensible Data Fields"*). Pre-PR, the outer-sub-field iteration
    lived only inside `parseZip64Extra`, which `break`s silently on a
    malformed sub-field; the caller skips `parseZip64Extra` entirely
    when no ZIP64 sentinel is set, so the anomaly was invisible in the
    no-sentinel case and misattributed to "missing 0x0001" in the
    sentinel case.  `validateExtraFieldStructure` now runs
    unconditionally on the blob before the sentinel guard at both the
    CD site (`parseCentralDir`) and the LH site (`readEntryData`) —
    closing the outer sub-field iteration dimension of the ZIP64
    extra-data smuggling class (siblings of the inner-0x0001
    `zip64-extra-oversized-datasize.zip` `dataSize` exactness check).
    Writer side is well-formed by construction at
    [Zip/Archive.lean:66-71](/home/kim/lean-zip/Zip/Archive.lean:66)
    (LH) and :74-80 (CD): both paths emit either a single well-formed
    0x0001 block or zero extra-data
  - ZIP64 per-entry extra-field `dataSize` exactness check — PR #1785
    (`testdata/zip/malformed/zip64-extra-oversized-datasize.zip`)
    rejects CD entries whose ZIP64 (headerId `0x0001`) extra-field
    `dataSize` is strictly greater than the `8 * N` bytes consumed by
    the `N` sentinel-gated 32-bit standard fields (APPNOTE §4.5.3).
    Trailing slack past the consumed prefix is attacker-controllable
    and is a parser-differential smuggling vector — a lenient parser
    (the pre-PR lean-zip) silently discards the slack after the first
    `N * 8` bytes, while a strict parser rejects the archive.
    `parseZip64Extra` now asserts `fpos == fieldEnd` after the three
    conditional reads (Zip/Archive.lean:428). Sibling of the outer
    `zip64-eocd64-bad-recsize.zip` record-size check (same
    parser-differential attack class, different layer); writer-side at
    [Zip/Archive.lean:73-80](/home/kim/lean-zip/Zip/Archive.lean:73)
    (CD) and :65-71 (LH) both emit exactly `N * 8` bytes of data
  - duplicate ZIP64 (`headerId 0x0001`) extra-block rejection — PR #1793
    (`testdata/zip/malformed/cd-zip64-extra-duplicate.zip` and
    `testdata/zip/malformed/lh-zip64-extra-duplicate.zip`) rejects CD
    or LH extra-data containing two or more ZIP64 (`0x0001`) blocks.
    APPNOTE §4.5 forbids more than one instance of any registered
    header ID per entry's extra-data; for ZIP64 in particular the
    layout of each block depends on which standard 32-bit fields are
    at the `0xFFFFFFFF` sentinel, so two blocks with different
    payloads make the resolved sizes/offset ambiguous. lean-zip's
    pre-fix `parseZip64Extra` used a `break` after the first
    `headerId == 0x0001` match — a "first-wins" policy that lets a
    "last-wins" parser disagree on identical bytes. The new
    `hasDuplicateZip64Extra` helper at
    [Zip/Archive.lean:406](/home/kim/lean-zip/Zip/Archive.lean:406)
    walks the TLV structure once and is invoked by both the CD-side
    caller in `parseCentralDir`
    ([Zip/Archive.lean:693](/home/kim/lean-zip/Zip/Archive.lean:693))
    and the LH-side caller in `readEntryData`
    ([Zip/Archive.lean:983](/home/kim/lean-zip/Zip/Archive.lean:983))
    before `parseZip64Extra` is called. The two error wordings
    (`"duplicate ZIP64 extra field"` vs `"duplicate ZIP64 local extra
    field"`) keep attribution distinct between layers. Sibling of the
    sub-field `dataSize` exactness check (PR #1785) — together they
    close the ZIP64 extra-field layout-smuggling attack class at the
    CD/LH boundary; writer-side `writeZip64ExtraCentral`
    ([Zip/Archive.lean:73-80](/home/kim/lean-zip/Zip/Archive.lean:73))
    and `writeZip64ExtraLocal` (:66-71) emit at most one 0x0001 block
    per entry, so the new guard never fires on legitimate archives
  - CD-vs-LH `versionNeededToExtract` downgrade check — PR #1736
    (`testdata/zip/malformed/cd-lh-version-mismatch.zip`) rejects LH
    claiming a higher version than CD (CD > LH is legitimate per
    Go/Python ZIP64 producers and is allowed)
  - CD-vs-LH `lastModTime`/`lastModDate` consistency check — PR #1769
    (`testdata/zip/malformed/cd-lh-modtime-mismatch.zip`) rejects
    archives whose DOS-encoded last-modified `UInt16` time/date pair
    disagrees between CD offset +12/+14 and LH offset +10/+12 (APPNOTE
    §4.4.6). The check is ungated — unlike crc/compSize/uncompSize,
    the timestamp fields are not legitimately zeroed by the
    data-descriptor bit. Closes the last CD/LH header-metadata
    smuggling dimension; writer-side at
    [Zip/Archive.lean:93-94](/home/kim/lean-zip/Zip/Archive.lean:93)
    (LH) and :120-121 (CD) both emit `defaultDosTime` /
    `defaultDosDate` via the shared constants at
    [Zip/Archive.lean:62-63](/home/kim/lean-zip/Zip/Archive.lean:62).
    Net-new dimension observed during the CD/LH header-metadata
    coverage sweep — the *Missing work* block had not previously
    flagged the timestamp fields
  - CD-entry stored-method (`method=0`) size-invariant check — PR #1773
    (`testdata/zip/malformed/cd-stored-size-mismatch.zip`) rejects CD
    entries whose `method == 0` with `compressedSize != uncompressedSize`
    at `parseCentralDir` time (post-ZIP64-resolution), before any LH
    read. APPNOTE §4.4.5 defines method 0 as *"no compression"*, so the
    equality is a tautology — the writer emits equal values for stored
    entries and crafted archives with mismatched sizes are malformed.
    Complements the CD/LH `uncompressedSize` consistency check
    (`cd-lh-uncompsize-mismatch.zip`): that catches CD-vs-LH skew, this
    catches intra-CD invariant violation with no CD/LH divergence. Also
    makes the anomaly visible to `Archive.list`, which never reaches the
    late post-decode `"size mismatch"` guard at
    [Zip/Archive.lean:976](/home/kim/lean-zip/Zip/Archive.lean:976).
    Net-new dimension observed during the CD-parse guard coverage
    sweep — the *Missing work* block had not previously flagged the
    stored-method invariant
  - CD-entry compression-method allowlist check — PR #1801
    (`testdata/zip/malformed/cd-bad-method-early.zip`) rejects CD
    entries whose `method` field is outside lean-zip's `{0, 8}`
    allowlist (`0` = stored, `8` = deflate) at `parseCentralDir` time
    ([Zip/Archive.lean:668](/home/kim/lean-zip/Zip/Archive.lean:668)),
    before the ZIP64 extra resolution. The check is safe to run
    pre-ZIP64-resolution because `method` is a plain `UInt16` field
    with no sentinel-gating (APPNOTE §4.4.5). Pre-PR, only
    `Archive.extract`'s late `"unsupported method"` dispatch in
    `readEntryData` (`"unsupported method"` throw at [Zip/Archive.lean:1083](/home/kim/lean-zip/Zip/Archive.lean:1083))
    caught crafted archives advertising method 6 (imploded), 12
    (bzip2), 14 (LZMA), 93 (Zstd), etc. — `Archive.list` was entirely
    blind to the anomaly, and a caller routing on `Entry.method` to
    pre-authorize before extracting would treat the crafted metadata
    as trustworthy. Writer-side at
    [Zip/Archive.lean:192](/home/kim/lean-zip/Zip/Archive.lean:192)
    (`let method : UInt16 := if useDeflate then 8 else 0`) is
    trivially compliant. The late `readEntryData` throw stays in
    place as defense-in-depth — unreachable for CD-parseable archives
    via the public API, but kept so the precedence-shift story is
    grep-discoverable. Precedence-shift sibling of PR #1773
    (stored-method size invariant): same early-rejection approach
    applied to the method-field dimension. Companion fixture
    `bad-method.zip` (CD/LH method=14, LZMA, 140 B) now also trips
    the same CD-parse guard; the new `cd-bad-method-early.zip`
    (CD/LH method=6, imploded, 122 B) provides paired-review-distinct
    attribution
  - CD-entry `localOffset + 30 ≤ cdOffset` archive-layout invariant —
    PR #1813
    (`testdata/zip/malformed/cd-entry-localoffset-past-cdstart.zip`)
    rejects CD entries whose resolved `localOffset` plus the 30-byte
    fixed LH header (APPNOTE §4.3.7) reaches into or past the CD
    region at `parseCentralDir` time
    ([Zip/Archive.lean:728](/home/kim/lean-zip/Zip/Archive.lean:728)).
    APPNOTE §4.3.6 pins the archive layout as `[LH+data]* [CD]
    [EOCD]`, so every entry's LH must be readable strictly before the
    CD start; writer-side at
    [Zip/Archive.lean:192](/home/kim/lean-zip/Zip/Archive.lean:192)
    emits all LH bytes before the CD block, so the invariant is
    universal for legitimate archives. Per-entry micro-shape sibling
    of the archive-level macro-shape `cdOffset + cdSize ≤ eocdPos`
    guard; together they characterize the legitimate layout at both
    granularities. Pre-PR, `Archive.list` had no gate at all —
    crafted archives with `localOffset ≥ cdOffset` listed
    successfully and `Entry`-routing callers treated the metadata as
    trustworthy; only the extract path's late LH-signature check
    (`"bad local header signature"` at
    [Zip/Archive.lean:970](/home/kim/lean-zip/Zip/Archive.lean:970))
    caught a subset of the construction (and could be defeated by a
    carefully chosen overlap where the CD bytes happened to match
    `sigLocal`). Uses the asymmetric `SpanInFile`-shaped subtraction
    to avoid `UInt64` wrap on crafted very-large `localOff`. Placed
    after ZIP64 resolution so the resolved `UInt64` `localOff` is
    checked, not the `0xFFFFFFFF` sentinel. Net-new dimension
    observed during the CD-parse archive-layout-invariant coverage
    sweep
  - Late LH-signature guard regression coverage — PR #1903
    (`testdata/zip/malformed/cd-bad-lh-signature.zip`) pins the
    `Archive.extract` defense-in-depth catch at
    [Zip/Archive.lean:1081](/home/kim/lean-zip/Zip/Archive.lean:1081)
    — *"bad local header signature for {label}"* — for archives whose
    CD parses cleanly but whose LH magic at `entry.localOffset` is not
    `0x04034b50` (`sigLocal`, APPNOTE §4.3.7). 122-byte single-entry
    stored `hello.txt` fixture (LH at file offset 0, CD at offset 45,
    EOCD at offset 100) where the LH's first 4 bytes are overwritten
    with `0xCAFEBABE` (LE: `BE BA FE CA`) — the CD itself is
    byte-identical to the stock baseline so every CD-parse guard passes
    (`localOffset = 0`, `localOffset + 30 ≤ cdOffset = 45`,
    `entryEnd = 45 ≤ cdEnd = 100`, method ∈ {0, 8}, stored-method
    `compSize == uncompSize`, etc.) and `assertSpanInFile` /
    `readBoundedSpanFromHandle` clear the LH span (30 B at offset 0 ≤
    fileSize 122). `Archive.list` never reads the LH and lists the
    fixture cleanly; only `Archive.extract` throws — confirming the
    precedence story. Fixture-only regression coverage (no new guard
    code, no new error wording, no caller / signature change) — pattern
    matches PRs #1761 / #1889 (`zip64-eocd64-bad-recsize.zip` /
    `zip64-eocd64-v2-record.zip` at the EOCD64 record-size guard) and
    in-flight #1885 (`cd-entry-past-cdend.zip` at the `entryEnd > cdEnd`
    guard). Sibling of `cd-entry-localoffset-past-cdstart.zip` (PR #1813,
    fires the per-entry `localOffset + 30 ≤ cdOffset` CD-parse guard
    before the LH read) and `cd-entry-past-cdend.zip` (issue #1885,
    fires the `entryEnd > cdEnd` CD-parse guard before the LH read):
    together the trio pins all three precedence levels of the
    local-offset → local-header validation chain at CD-parse +
    late-extract — the late LH-signature guard is the defense-in-depth
    catch for archives that slip past every earlier CD-parse check, and
    this fixture pins that catch behaviour so future refactors of
    `Archive.extract` cannot silently lose the guard. Choice of
    `0xCAFEBABE` is canonical "obviously crafted" UInt32 — any 4-byte
    sequence ≠ `50 4b 03 04` fires the same guard
  - Per-entry `entryEnd > cdEnd` footprint guard regression coverage —
    PR #1921
    (`testdata/zip/malformed/cd-entry-past-cdend.zip`) pins the existing
    `parseCentralDir` per-entry footprint check at
    [Zip/Archive.lean:615](/home/kim/lean-zip/Zip/Archive.lean:615)
    — *"central directory entry extends past end of central directory"*
    — for archives whose declared field-length triple
    `(nameLen, extraLen, commentLen)` makes the CD entry's claimed
    footprint `46 + nameLen + extraLen + commentLen` exceed the
    EOCD-declared `cdEnd = cdOffset + cdSize`. 122-byte single-entry
    stored `hello.txt` fixture (LH at file offset 0, CD at offset 45,
    EOCD at offset 100) where the sole CD entry's `commentLen` field at
    CD +32 (UInt16) is `16` while no comment payload is physically
    present — `cdSize = 55` (header + name only). At parse time
    `entryEnd = 45 + 46 + 9 + 0 + 16 = 116 > cdEnd = 100`, firing the
    :615 guard before any name decode. All earlier CD-parse guards pass
    (loop entry `pos + 46 ≤ cdEnd` (91 ≤ 100), CD signature match,
    `nameLen = 9 > 0`, `diskNumberStart = 0`, `internalAttrs = 0`) so
    attribution pins to the footprint guard rather than a sibling
    early-reject. Fixture-only regression coverage (no new guard code,
    no new error wording, no caller / signature change) — pattern
    matches PRs #1761 / #1889 (`zip64-eocd64-bad-recsize.zip` /
    `zip64-eocd64-v2-record.zip` at the EOCD64 record-size guard) and
    #1903 (`cd-bad-lh-signature.zip` at the late LH-signature guard).
    Companion to in-flight `cd-trailing-garbage.zip` (issue #1775,
    trailing bytes AFTER the last entry inside `[lastEntryEnd, cdEnd)`)
    and `cd-extends-past-eocd.zip` (issue #1799, archive-level
    `cdOffset + cdSize ≤ eocdPos`) — the trio closes the three
    CD-region overrun shapes: per-entry footprint past `cdEnd`
    (this fixture), trailing garbage inside the declared region
    (#1775), and macro `cdSize` past EOCD (#1799). Pins the
    paired-review precedence chain alongside
    `cd-entry-localoffset-past-cdstart.zip` (PR #1813, per-entry
    `localOffset + 30 ≤ cdOffset`) and `cd-bad-lh-signature.zip`
    (PR #1903, late LH-signature guard) — together the trio fixes all
    three precedence levels of the local-offset → local-header
    validation chain at CD-parse + late-extract so future refactors
    of `parseCentralDir` cannot silently regress the per-entry
    footprint fence. Sentinel `commentLen = 16` is canonical
    "obviously crafted" overrun — any positive value satisfying
    `46 + nameLen + extraLen + commentLen > cdSize` fires the same
    guard. Interop pre-flight over
    `testdata/zip/{interop,malformed}/*.zip` returned zero hits before
    landing
  - CD-entry `internalFileAttributes` reserved-bits check — PR #1819
    (`testdata/zip/malformed/cd-entry-internal-attrs-reserved.zip`)
    rejects CD entries whose APPNOTE §4.4.10 `internalFileAttributes`
    field at CD offset +36 (UInt16) has any bit other than bit 0
    set. APPNOTE §4.4.10 defines only bit 0 ("apparent ASCII/text
    data"); bits 1 and 2 are "reserved for use by PKWARE"; remaining
    bits are "unused in version 1.0". The guard is
    `internalAttrs &&& 0xFFFE == 0` (preserve bit 0, reject bits
    1-15) — preserves Info-ZIP interop (spot-check of
    `testdata/zip/interop/`: `go-unix.zip`, `go-test.zip`,
    `go-crc32-not-streamed.zip` set bit 0 on apparent-text files
    as `0x0001`; `go-zip64.zip`, `latin1-name.zip`, `utf8-flag.zip`
    use `0x0000`; no interop fixture sets any reserved bit).
    `parseCentralDir` fires the guard at
    [Zip/Archive.lean:567](/home/kim/lean-zip/Zip/Archive.lean:567),
    immediately after the `diskNumberStart` check and before the
    `entryEnd > cdEnd` span check. Writer-side at
    [Zip/Archive.lean:131](/home/kim/lean-zip/Zip/Archive.lean:131)
    (`Binary.zeros`-initialised 46-byte CD header — `pos + 36` never
    overwritten) is trivially compliant. Writer-zero single-`UInt16`
    sibling of PR #1759 (CD +34 `diskNumberStart` per-entry
    writer-invariant) and PR #1752 (EOCD `numEntriesThisDisk`
    archive-level writer-invariant); the three PRs together close
    the contiguous `CD+34 → CD+36 → EOCD` writer-zero-field
    early-reject column. Pre-PR, `Archive.list` and `Archive.extract`
    both silently accepted any `UInt16` here — a caller routing on
    `Entry` metadata would treat the smuggled reserved bits as
    trustworthy, and a strict peer reader would disagree on parse
    success. Net-new dimension observed during the CD+offset
    writer-zero coverage sweep — the *Missing work* block had not
    previously flagged the internal-attrs field
  - CD-entry general-purpose flag bit-5 (compressed patched data)
    rejection — PR #1824
    (`testdata/zip/malformed/cd-patched-data-flag.zip`) rejects CD
    entries whose flag-word has APPNOTE §4.4.4 bit 5 set at
    `parseCentralDir` time
    ([Zip/Archive.lean:682](/home/kim/lean-zip/Zip/Archive.lean:682)),
    pre-ZIP64-resolution. lean-zip implements neither creation nor
    extraction of PKWARE's proprietary compressed-patched-data
    format (§4.6); the writer emits `flags = 0x0800` (bit 11 UTF-8
    names) only at `writeLocalHeader`
    ([Zip/Archive.lean:91](/home/kim/lean-zip/Zip/Archive.lean:91))
    and `writeCentralHeader` (:118), so the guard never fires on
    legitimate archives. Pre-PR, crafted archives with bit 5 set
    were silently extracted as if the payload were plain Deflate /
    stored data — a parser-differential smuggling vector where a
    strict APPNOTE-aware reader would reject while lean-zip
    mis-extracts. Mask-equality form (`flags &&& 0x0020 == 0`)
    matches the `0xFFF7` bit-3-masking convention in `readEntryData`.
    Sibling of in-flight PR #1771 (issue #1762, bits 0/6/13
    encryption-related) at the same CD+8 `flags` field — distinct
    bit, distinct semantic justification, distinct error substring
    (`"patched-data flag bit 5 set"`). Interop safety: spot-checked
    pre-planning that all six `testdata/zip/interop/` fixtures
    carry `flag_bits ∈ {0x0000, 0x0800}` (no bit 5). Net-new
    dimension observed during the CD-parse flag-field coverage
    sweep
  - CD-entry name NUL-byte rejection — PR #1831
    (`testdata/zip/malformed/cd-nul-in-name.zip`) rejects CD entries
    whose raw name bytes contain a NUL (`0x00`) byte at
    `parseCentralDir` time
    ([Zip/Archive.lean:589](/home/kim/lean-zip/Zip/Archive.lean:589)),
    before the UTF-8 decode at
    [Zip/Archive.lean:633-643](/home/kim/lean-zip/Zip/Archive.lean:633).
    A NUL byte in the filename is a classic parser-differential /
    filesystem-truncation smuggling vector: POSIX `open`/`stat` and
    many runtime layers treat `evil.txt\x00.zip` as `evil.txt`, while
    `Archive.list` callers and strict peer readers see the full
    NUL-embedded string. Pre-PR, `Archive.list` returned the
    NUL-containing `path` verbatim (both `String.fromUTF8?` and
    `Binary.fromLatin1` preserve U+0000), and `Archive.extract` with
    the default `Binary.isPathSafe` passed the NUL-containing path
    into `IO.FS.writeBinFile` where the POSIX `open` layer truncates
    at NUL — depositing the extracted file at the short-form prefix,
    not the smuggled full form. Guarding on the raw `ByteArray` before
    UTF-8 decode keeps the error message NUL-free (no re-injection
    into logs) and closes both the UTF-8 and Latin-1 decode branches
    uniformly. Closes both `Archive.list` (silent NUL-path surfacing)
    and `Archive.extract` (silent truncated-filename drop) dimensions
    simultaneously — extract-time `Binary.isPathSafe` in
    [zipCommon / `ZipCommon/Binary.lean`](https://github.com/kim-em/lean-zip-common/blob/main/ZipCommon/Binary.lean)
    does not reject NUL and is shared with Tar, so CD-parse rejection
    is strictly local to the ZIP layer. Writer-side at
    [Zip/Archive.lean:84](/home/kim/lean-zip/Zip/Archive.lean:84) and
    :110 inherits the invariant from caller-supplied `entry.path` (no
    emit-time enforcement). Interop pre-flight swept
    `testdata/zip/interop/*.zip` and `testdata/zip/malformed/*.zip`
    for pre-existing NUL-in-name fixtures: zero hits, so no
    pre-existing regression is disturbed. Net-new dimension observed
    during the CD-parse filename-validation coverage sweep
  - CD-entry path-safety rejection — PR #1840
    (`testdata/zip/malformed/cd-path-unsafe.zip`) rejects CD entries
    whose decoded `name` is path-unsafe per `Binary.isPathSafe` at
    `parseCentralDir` time
    ([Zip/Archive.lean:631](/home/kim/lean-zip/Zip/Archive.lean:631)),
    immediately after the UTF-8 / Latin-1 decode block at
    [Zip/Archive.lean:633-643](/home/kim/lean-zip/Zip/Archive.lean:633)
    and before the `versionNeeded` upper-bound at
    [Zip/Archive.lean:651](/home/kim/lean-zip/Zip/Archive.lean:651).
    `Binary.isPathSafe` (canonical lean-zip-common path-safety filter,
    shared with the Tar extract path) rejects absolute paths (`/`
    prefix), `\` anywhere, `..`/`.` components, empty components (from
    `//`), and Windows drive-letter components. Closes the
    path-traversal / archive-slip smuggling dimension on the
    `Archive.list` path, which pre-PR returned the `Entry` with the
    unsafe `path` verbatim — exposing the full smuggled form to
    callers who route on `entry.path` before any filesystem I/O. The
    extract-time `Binary.isPathSafe` calls at
    [Zip/Archive.lean:1133](/home/kim/lean-zip/Zip/Archive.lean:1133)
    and :1107 remain in place as defense-in-depth but are now
    unreachable for CD-parseable archives via the public API. Mirrors
    the trailing-slash carve-out at
    [Zip/Archive.lean:1131](/home/kim/lean-zip/Zip/Archive.lean:1131)
    (directory entries end with `"/"`, checked on the slash-stripped
    form) so legitimate directory entries are not tripped. Quotes the
    name via `String.quote` so control bytes from the smuggled name
    never reach logs unescaped. Writer-side at
    [Zip/Archive.lean:84](/home/kim/lean-zip/Zip/Archive.lean:84) and
    :110 inherits the invariant from caller-supplied `entry.path` (no
    emit-time enforcement); the CD-parse guard is read-side only.
    Interop pre-flight swept `testdata/zip/interop/*.zip` and
    `testdata/zip/malformed/*.zip` for pre-existing path-unsafe
    fixtures: zero hits, so no pre-existing regression is disturbed
    (the `testdata/zip/security/` directory contains three `zip-slip`
    / `absolute-path` / `backslash-slip` counter-fixtures whose
    existing `"unsafe path"` assertion substring is a substring of
    the new `"CD entry has unsafe path"` wording, so their tests
    continue to pass). Sibling of PR #1831 (CD-entry name NUL-byte
    rejection) on the same filename-validation layer — the pair
    together closes the "smuggled name" attack class (NUL byte + path
    shape). Net-new dimension observed during the CD-parse
    filename-validation coverage sweep
  - CD-entry empty-filename rejection — PR #1848
    (`testdata/zip/malformed/cd-empty-name.zip`) rejects CD entries
    whose `nameLen` field at CD +28 (APPNOTE §4.4.10) is `0` at
    `parseCentralDir` time
    ([Zip/Archive.lean:535](/home/kim/lean-zip/Zip/Archive.lean:535)),
    immediately after the `nameLen` read and before the
    `entryEnd > cdEnd` overrun check at
    [Zip/Archive.lean:570](/home/kim/lean-zip/Zip/Archive.lean:570)
    and the sibling NUL-byte / path-safety filename guards. Every
    legitimate ZIP entry — file or directory — has at least one byte
    of name, so `nameLen == 0` is structurally pathological and a
    parser-differential smuggling vector: lenient readers emit
    `entry.path = ""` (an `Entry` with no useful identity), while
    `Archive.extract` would resolve `outDir / ""` to either `outDir`
    itself or a path with a trailing separator — neither of which
    the downstream `IO.FS.writeBinFile` / `createDir` calls reject
    with a message that attributes the fault to the empty-name
    structural anomaly. Guarding on the 16-bit `nameLen` field alone,
    before any later field-read or decode step, pins the failure
    attribution cleanly: the sibling CD-parse path-safety guard
    (PR #1840) would otherwise also catch `""` via `Binary.isPathSafe`'s
    empty-component rejection, but only if the decode succeeds — and
    the attribution then reads *"CD entry has unsafe path"* rather
    than the more direct *"CD entry has empty filename"*. Closes both
    `Archive.list` (pre-PR returned the `Entry` with `path = ""` —
    exposing an identity-less value to callers that route on
    `entry.path`) and `Archive.extract` (pre-PR surfaced as an
    `IO.FS.writeBinFile` / `createDir` error against `outDir / ""`,
    not the empty-name anomaly) dimensions simultaneously. Writer-side
    at [Zip/Archive.lean:84](/home/kim/lean-zip/Zip/Archive.lean:84)
    and :110 inherits the invariant from caller-supplied `entry.path`
    (no emit-time enforcement); the CD-parse guard is read-side only.
    Interop pre-flight swept `testdata/zip/interop/*.zip` and
    `testdata/zip/malformed/*.zip` for pre-existing CD entries with
    `nameLen == 0`: zero hits, so no pre-existing regression is
    disturbed. Sibling of PR #1831 (CD-entry name NUL-byte rejection,
    byte-content dimension) and PR #1840 (CD-entry path-safety
    rejection, path-shape dimension) on the same filename-validation
    layer — the trio together closes the "smuggled name" attack class
    at CD parse: zero-length, NUL-embedded, and path-traversal forms
    are all rejected pre-decode. Net-new dimension observed during
    the CD-parse filename-validation coverage sweep
  - CD-entry empty-entry CRC invariant rejection — PR #1857
    (`testdata/zip/malformed/cd-empty-entry-crc-nonzero.zip`) rejects
    CD entries whose `uncompressedSize == 0` with any nonzero `crc32`
    at `parseCentralDir` time
    ([Zip/Archive.lean:794](/home/kim/lean-zip/Zip/Archive.lean:794)),
    post-ZIP64-resolution, after the stored-method size invariant.
    APPNOTE §4.4.7 defines the CRC32 field as the ANSI-CRC-32 of the
    uncompressed payload; the empty byte string has CRC32 `0x00000000`
    (start state `0xFFFFFFFF`; no data to process; final complement
    returns `0x00000000`), so `uncompSize == 0 → crc == 0` is a
    universal mathematical invariant. Every correct writer — Info-ZIP,
    Go `archive/zip`, CPython `zipfile`, 7-Zip, and lean-zip's own
    `create` at
    [Zip/Archive.lean:195](/home/kim/lean-zip/Zip/Archive.lean:195)
    (which emits `Checksum.crc32 0 fileData` and hence `0` on an empty
    payload) — obeys it. Crafted archives carrying `uncompSize = 0`
    alongside any nonzero CRC are structurally malformed and a
    parser-differential smuggle vector: pre-PR, `parseCentralDir`
    propagated the crafted CRC into `Entry.crc32` verbatim, so
    `Archive.list` callers that routed on `entry.crc32` (logging,
    deduplication, downstream CRC cross-checks) saw the smuggled value
    while strict peer parsers or CRC-cross-checking callers rejected.
    Pre-PR, `Archive.extract` caught the mismatch only post-extraction
    via the `"CRC32 mismatch"` guard at
    [Zip/Archive.lean:1088](/home/kim/lean-zip/Zip/Archive.lean:1088),
    after the I/O work had been performed; `Archive.list` had no gate
    at all. Placed after the stored-method size invariant so the
    resolved `uncompSize : UInt64` is the value checked (rather than
    the `0xFFFFFFFF` sentinel) and so attribution pins on the empty-
    file premise rather than a generic CRC check. The `uncompSize == 0`
    probe runs first so the CRC field is inspected only when the
    empty-file premise holds; method 0 (stored) and method 8 (deflate)
    share the same invariant — a deflate-encoded empty stream has
    `compSize = 2` (the `03 00` empty-block encoding) but `uncompSize
    = 0`, so the check applies regardless of method. Writer-side at
    [Zip/Archive.lean:195](/home/kim/lean-zip/Zip/Archive.lean:195) is
    trivially compliant (`Checksum.crc32 0 ByteArray.empty == 0` by
    the CRC-32 init⊕complement identity); the CD-parse guard is
    read-side only. Sibling of PR #1773 (stored-method size invariant)
    at the CD-parse mathematical-invariant family: #1773 closes the
    `compSize == uncompSize` dimension (tautological for stored
    entries); the present bullet closes the `uncompSize == 0 → crc == 0`
    dimension (tautological for every empty entry, regardless of
    method). Net-new dimension observed during the CD-parse
    mathematical-invariant coverage sweep — the *Missing work* block
    had not previously flagged the empty-entry CRC invariant
  - CD-entry `compressedSize > 0` rejection when `uncompressedSize > 0`
    — PR #1886
    (`testdata/zip/malformed/cd-deflate-zero-compsize.zip`) rejects CD
    entries whose `compressedSize == 0` alongside any positive
    `uncompressedSize` at `parseCentralDir` time, post-ZIP64-resolution,
    after the stored-method size invariant and the empty-entry CRC
    invariant. APPNOTE §4.4.8 / §4.4.9 define the `compressedSize` and
    `uncompressedSize` fields; every ZIP compression method produces
    at least one compressed byte from non-empty uncompressed input —
    method 0 (stored, APPNOTE §4.4.5) has `compSize == uncompSize`;
    method 8 (deflate, RFC 1951) has a 2-byte minimum block-header
    encoding (`03 00` empty-stored-block), so any non-empty inflate
    output requires at minimum a block header plus encoded data.
    Therefore `compSize == 0 ∧ uncompSize > 0` is structurally
    impossible regardless of method — a universal mathematical
    invariant every correct writer (Info-ZIP, Go `archive/zip`, CPython
    `zipfile`, 7-Zip, lean-zip's own `create` at
    [Zip/Archive.lean:195](/home/kim/lean-zip/Zip/Archive.lean:195))
    obeys. Pre-PR, the sibling stored-method guard (PR #1773) caught
    this shape only when `method == 0` (via the `compSize == uncompSize`
    equality mismatch), leaving `method == 8` entries with this shape
    unguarded at CD parse — they fell through to the downstream
    `readEntryData` + inflate path, which only runs on `Archive.extract`
    and whose error attribution is scattered among the decompression
    backends (`Zlib.decompress` / `Gzip.decompress` /
    `Zip.Native.Inflate.inflate` all fail with some variant of
    *"unexpected end of deflate stream"* or *"invalid block type"*)
    rather than pinned on the CD-parse structural anomaly. Pre-PR,
    `Archive.list` returned the `Entry` with `{method = 8, compSize = 0,
    uncompSize = 42, ...}` verbatim — callers routing on
    `entry.compressedSize == 0` as a short-circuit (cache lookups, ACL
    checks, downstream CRC verification) saw the smuggled values. The
    sibling empty-entry CRC guard (PR #1857) fires only on
    `uncompSize == 0`; the new invariant fires only on `uncompSize > 0`,
    so the two are ordering-disjoint. The third column of the per-entry
    mathematical-invariant family at CD parse: PR #1773 closes the
    `compSize == uncompSize` dimension (tautological for stored entries,
    method=0 only); PR #1857 closes the `uncompSize == 0 → crc == 0`
    dimension (tautological for empty entries, method-agnostic); PR #1886
    closes the `uncompSize > 0 → compSize > 0` dimension (structurally
    required under any compression method — method-agnostic). Together
    the three columns form a contiguous block of math invariants at
    `parseCentralDir`
  - oversized ZIP64 compressed-size fixture — PR #1543
    (`testdata/zip/malformed/oversized-zip64-compressed-size.zip`)
  - oversized ZIP64 uncompressed-size fixture — PR #1544
    (`testdata/zip/malformed/oversized-zip64-uncompressed-size.zip`)
  - bounded-read helpers for `Handle`/`Stream` — PR #1608
    (Track E P5.1)
  - `SpanInFile` predicate + IO reduction lemmas — PR #1636
    (Track E P5.2)
  - `Archive`/`Tar` callers migrated to bounded-read helpers — PR #1626
    (Track E P5.3)

### Tar Parser/Extractor

- Components: [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean:1)
- Status: `guarded-locally`
- Trust boundary:
  - parses tar headers, GNU long-name records, PAX metadata, symlinks,
    and streamed entry contents
- Current guardrails:
  - explicit `maxEntrySize` in extraction paths
  - path safety checks for extracted files
  - short-read detection in entry and padding reads
  - invalid PAX UTF-8 is skipped instead of panicking in `parsePaxRecords`
- Missing work:
  - none open at this layer; the policy and fixture work below are done
- Recent wins:
  - `String.fromUTF8!` callsite audit — PR #1550
    (`Tar.truncateUTF8`; regression coverage in
    `ZipTest/TarPathTruncation.lean`)
  - malformed PAX fixtures — PR #1545
    (`testdata/tar/malformed/pax-*.tar`)
  - malformed GNU long-name/long-link fixtures — PR #1546
    (`testdata/tar/malformed/gnu-longname-*.tar`,
    `gnu-longlink-truncated.tar`)
  - symlink/hardlink extraction policy + archive-slip tests — PR #1555
    (see subsection below; `testdata/tar/security/`)
  - UStar `name` / `linkname` / `prefix` / `uname` / `gname` interior-NUL
    rejection in `parseHeader` — PR #1880 (`name` slot,
    `testdata/tar/malformed/ustar-name-nul-in-name.tar`) + per-slot
    `linkname` follow-up
    (`testdata/tar/malformed/ustar-linkname-nul-in-name.tar`) +
    per-slot `prefix` follow-up
    (`testdata/tar/malformed/ustar-prefix-nul-in-name.tar`) + 4th-slot
    `uname` defense-in-depth follow-up
    (`testdata/tar/malformed/ustar-uname-nul-in-uname.tar`) +
    5th-and-final `gname` defense-in-depth follow-up
    (`testdata/tar/malformed/ustar-gname-nul-in-gname.tar`).
    `Tar.parseHeader` runs `hasInteriorNul` on the raw 512-byte block
    after the checksum + magic checks and before any
    `Binary.readString` call on the five UStar string fields. Five
    distinct error substrings keep attribution per-field —
    *"UStar name contains NUL byte"* (offset 0, 100 B),
    *"UStar linkname contains NUL byte"* (offset 157, 100 B),
    *"UStar prefix contains NUL byte"* (offset 345, 155 B),
    *"UStar uname contains NUL byte"* (offset 265, 32 B),
    *"UStar gname contains NUL byte"* (offset 297, 32 B). Closes
    the UStar layer of the smuggled-NUL attack class — sibling of
    PR #1831 (ZIP CD entry name, *"CD entry name contains NUL byte"*),
    PRs #1865 (long-name slot, `gnu-longname-nul-in-name.tar`) /
    #1953 (long-link slot, `gnu-longlink-nul-in-link.tar`) (GNU
    long-name / long-link, *"GNU long-name contains NUL byte"* /
    *"GNU long-link contains NUL byte"*), and PR #1866 (PAX
    `keyBytes` / `valueBytes` silent-skip in `parsePaxRecords`). The
    UStar interior-NUL family is **fully closed 5/5** — the 3-slot
    filesystem-reaching arm (`name` / `linkname` / `prefix`) plus the
    2-slot defense-in-depth arm (`uname` / `gname`). All five arms
    now each carry a dedicated per-slot regression fixture. The
    `uname` / `gname` fields do not reach the filesystem in
    `Tar.extract` — their guards are defense-in-depth against a
    `Tar.list` caller routing on `entry.uname` / `entry.gname` for a
    trust decision and seeing only the truncated prefix while peer
    parsers preserve the full bytes.
  - GNU long-name / long-link interior-NUL rejection in `forEntries`
    — PR #1865 (both guards in `forEntries`'s `typeGnuLongName` /
    `typeGnuLongLink` arms; long-name regression fixture
    `testdata/tar/malformed/gnu-longname-nul-in-name.tar`) +
    per-slot long-link follow-up
    (`testdata/tar/malformed/gnu-longlink-nul-in-link.tar`,
    PR #1953). Two error substrings keep per-slot attribution —
    *"GNU long-name contains NUL byte"* (typeflag `'L'` arm at
    [Zip/Tar.lean:667](/home/kim/lean-zip/Zip/Tar.lean:667)) and
    *"GNU long-link contains NUL byte"* (typeflag `'K'` arm at
    [Zip/Tar.lean:679](/home/kim/lean-zip/Zip/Tar.lean:679)).
    `forEntries` runs `findIdx? (· == 0)` on the raw `ByteArray`
    payload after `stripTrailingNuls` and before
    `String.fromUTF8?` / `Binary.fromLatin1`, so neither decode
    branch can re-introduce NUL into the error message. The
    GNU long-name / long-link interior-NUL family is
    **fully closed 2/2** — long-name slot (PR #1865,
    `gnu-longname-nul-in-name.tar`) + long-link slot (PR #1953,
    `gnu-longlink-nul-in-link.tar`). Sibling of PRs #1880 / #1934
    / #1937 / #1944 / #1957 (UStar interior-NUL family fully
    closed 5/5), PR #1831 (ZIP CD entry name NUL-byte rejection),
    and PR #1866 (PAX `keyBytes` / `valueBytes` silent-skip in
    `parsePaxRecords`). lean-zip's tar writer does not emit GNU
    long-name / long-link pseudo-entries (`Tar.create` always
    emits UStar-or-PAX-extended-header for paths exceeding the
    UStar 100/155-byte limits), so neither guard ever fires on
    legitimate archives produced by `Tar.create`. The guards
    exist to reject crafted malformed archives fed to `Tar.list`
    / `Tar.extract` — the fixtures are the only way to trigger
    them.
  - PAX extended-header duplicate-key rejection in `parsePaxRecords` —
    PR #1899
    (`testdata/tar/malformed/pax-duplicate-path.tar`).
    Ordering inside `parsePaxRecords`: UTF-8 decode → raw-byte NUL
    guard → duplicate-key check → push, so the duplicate-key branch
    at [Zip/Tar.lean:147](/home/kim/lean-zip/Zip/Tar.lean:147) only
    fires on records that already passed the UTF-8 and NUL filters.
    Unlike PR #1866 (PAX NUL-byte silent-skip, which drops the
    offending record and continues), PR #1899 hard-rejects — the
    `.error` return is rethrown unconditionally by `forEntries`'s
    `typePaxExtended` branch at
    [Zip/Tar.lean:669](/home/kim/lean-zip/Zip/Tar.lean:669) via
    `throw (IO.userError msg)`. Error wording *"tar: PAX extended
    header has duplicate {key.quote} record"* uses `String.quote`
    attribution on the duplicate key. Closes the parser-differential
    *duplicate-key* dimension on `parsePaxRecords` complementary to
    PR #1866's NUL-byte silent-skip; together the two close both
    parser-differential dimensions on the PAX-record decode pipeline.
  - PAX extended-header value-side NUL-byte silent-skip in
    `parsePaxRecords` — PR #1866 (`path` slot,
    `testdata/tar/malformed/pax-path-nul-in-value.tar`) +
    per-slot `linkpath` follow-up
    (`testdata/tar/malformed/pax-linkpath-nul-in-value.tar`,
    PR #1979). `parsePaxRecords` runs
    `findIdx? (· == 0)` on the raw `keyBytes` / `valueBytes`
    slices at
    [Zip/Tar.lean:145](/home/kim/lean-zip/Zip/Tar.lean:145)
    (`keyBytes`) and
    [Zip/Tar.lean:146](/home/kim/lean-zip/Zip/Tar.lean:146)
    (`valueBytes`) after `String.fromUTF8?` accepts the bytes
    (which permits U+0000 as valid UTF-8) and before the
    duplicate-key check pushes onto the records array. Records
    that fail this guard are dropped silently, matching the
    invalid-UTF-8 precedent on the same loop, *not* hard-rejected
    like PR #1899's duplicate-key guard at
    [Zip/Tar.lean:147](/home/kim/lean-zip/Zip/Tar.lean:147).
    Ordering inside `parsePaxRecords` is UTF-8 decode → raw-byte
    NUL guard → duplicate-key check → push; the silent-skip
    happens at the raw-byte NUL stage on `keyBytes` / `valueBytes`
    before `Binary.fromLatin1` would re-decode on the
    `applyPaxOverrides` side. The companion `applyPaxOverrides`
    case-arms at
    [Zip/Tar.lean:161](/home/kim/lean-zip/Zip/Tar.lean:161)
    (`"path"` → `entry.path`) and
    [Zip/Tar.lean:162](/home/kim/lean-zip/Zip/Tar.lean:162)
    (`"linkpath"` → `entry.linkname`) are the smuggle targets
    the silent-skip prevents from firing — pre-guard, an
    attacker-controlled record `path=a\x00b/c` would land as
    `entry.path = "a\x00b/c"` (POSIX `open` truncates at NUL on
    `Tar.extract` while `Tar.list` callers see the full embedded
    string), and `linkpath=a\x00b/c` would land as
    `entry.linkname = "a\x00b/c"` (POSIX `symlink` truncates
    similarly on the symlink path). The PAX value-side override
    family is **fully closed 2/2** — `path` slot (PR #1866,
    `pax-path-nul-in-value.tar`) + `linkpath` slot (PR #1979,
    `pax-linkpath-nul-in-value.tar`). Terminal closure of the
    third per-slot Tar interior-NUL family in the post-#1928
    wave (after the 5-slot UStar family closed at PR #1957 and
    the 2-slot GNU long-name / long-link family closed at
    PR #1953); together the three terminal closures complete the
    "smuggled NUL in any user-supplied string field" attack
    class across the entire Tar parsing surface (UStar + GNU +
    PAX). Sibling of PRs #1880 / #1934 / #1937 / #1944 / #1957
    (UStar interior-NUL family fully closed 5/5), PRs #1865 /
    #1953 (GNU long-name / long-link family fully closed 2/2),
    PR #1899 (PAX duplicate-key, complementary
    parser-differential dimension on the same `parsePaxRecords`
    loop), and PR #1831 (ZIP CD entry name NUL-byte rejection).
    lean-zip's tar writer does not emit PAX extended headers
    (`Tar.create` always emits UStar-or-PAX-extended-header for
    paths exceeding the UStar 100/155-byte limits, but never the
    value-side override records that this guard fires on), so
    neither slot of the guard ever fires on legitimate archives
    produced by `Tar.create` — the guards exist to reject crafted
    malformed archives fed to `Tar.list` / `Tar.extract`, and the
    fixtures are the only way to trigger them. The companion
    `keyBytes` arm at
    [Zip/Tar.lean:145](/home/kim/lean-zip/Zip/Tar.lean:145) is
    defense-in-depth (no known-key string in `applyPaxOverrides`'s
    case match contains `\x00`, so a NUL-bearing key would
    already be dropped at the case match) and is left for a
    future per-arm extension.

#### Symlink/hardlink extraction policy

`Tar.extract` (in [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean:748))
applies a fixed per-typeflag policy:

- `typeRegular` ('0') and `typeDirectory` ('5') — written under
  `outDir/path` after `Binary.isPathSafe` rejects unsafe paths
  (absolute, `..`, `.`, empty components, backslash, Windows drive
  letters).
- `typeSymlink` ('2') — `linkname` is rejected before any
  `Handle.createSymlink` call if it starts with `/`, contains `\`, or
  has any `..` component (path-component split). The payload is
  always discarded.
- `typeHardlink` ('1') — silently skipped. No filesystem entry is
  created, the payload is consumed and discarded, and no
  `Handle.createHardlink` call exists in the extractor. A crafted
  `linkname` therefore cannot escape `outDir`.
- All other typeflags (devices, FIFO, GNU sparse, etc.) — same silent
  skip as `typeHardlink`.

Regression fixtures live under `testdata/tar/security/`:

- `tar-slip.tar`, `tar-absolute.tar` — regular-file entries that must
  fail `"unsafe path"`.
- `backslash-slip.tar` — regular-file entry whose path contains `\`;
  also fails `"unsafe path"` (the backslash check fires before the
  `..` component check).
- `symlink-slip.tar` — symlink whose linkname contains `..`; must
  fail `"unsafe symlink"`.
- `symlink-absolute.tar` — symlink whose linkname is `/etc/passwd`;
  must fail `"unsafe symlink"`. Built deterministically by
  `scripts/build-symlink-hardlink-malformed-fixtures.lean`.
- `hardlink-outside.tar` — `typeHardlink` entry with linkname
  `../outside`; extraction must succeed with an empty extract dir.
  Built by the same script.

### Gzip/Zlib/Raw DEFLATE Public APIs

- Components:
  - [Zip/Gzip.lean](/home/kim/lean-zip/Zip/Gzip.lean:1)
  - [Zip/Basic.lean](/home/kim/lean-zip/Zip/Basic.lean:1)
  - [Zip/RawDeflate.lean](/home/kim/lean-zip/Zip/RawDeflate.lean:1)
- Status: `guarded-locally`
- Current guardrails:
  - decompression APIs expose `maxDecompressedSize` or native equivalents
  - malformed fixture coverage already exists for some gzip/zip/tar cases
- Missing work:
  - Executed — call-site inventory of `0 = no limit` is the
    *Decompression Limit Inventory* table below; this bullet is
    superseded by that table.
  - Executed — *Recommended policy* items 1–5 below all landed;
    extraction APIs now default to bounded mode (1 GiB per-entry,
    1 GiB FFI whole-buffer; opt-in `0` for unlimited).
  - Executed — sanitizer recipe in
    [`scripts/sanitize-ffi.sh`](/home/kim/lean-zip/scripts/sanitize-ffi.sh)
    covers FFI entry points; streaming paths additionally exercised
    by the fuzz harness (PR #1602) extended to streaming
    `decompressStream` APIs in PR #1653.

## Known Immediate Audit Targets

### 1. ZIP metadata to `Handle.read`

- File: [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean:491)
- Concern:
  - `readExact` itself guards `Nat -> USize`, but callers still need proof
    or validation that attacker-controlled sizes are file-bounded before reading
- Needed:
  - prove bounded-read lemmas for the guarded read paths (still open)
- Recent wins:
  - explicit pre-read span validation landed via `assertSpanInFile` in
    `Zip/Archive.lean` (wraps local-header, name+extra, and payload reads)
  - malformed ZIP64 size fixtures landed via PRs #1543 and #1544

### 2. Tar UTF-8 partial functions

- File: [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean:246)
- Concern:
  - `String.fromUTF8!` is partial and should not be reachable from
    attacker-controlled invalid bytes without prior validation
- Status: audit landed via PR #1550. The three panicking raw-byte
  truncations in `buildPaxEntry` and `create` now go through
  `Tar.truncateUTF8`; the two remaining `fromUTF8!` callsites in
  `splitPath` split at an ASCII `'/'` byte and are documented safe.
  Regression coverage in `ZipTest/TarPathTruncation.lean`.

### 3. Unlimited decompression knobs

- Files:
  - [Zip/Basic.lean](/home/kim/lean-zip/Zip/Basic.lean:9)
  - [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean:783)
- Concern:
  - `0 = no limit` is convenient but weak as a default for hostile inputs
- Needed:
  - policy decision on safer defaults for archive extraction APIs
  - tests for decompression-bomb limits
- See: *"Decompression Limit Inventory"* below for the full surface.

## Decompression Limit Inventory

Inventory of every public API that accepts untrusted compressed bytes
and drives decompression or extraction. This is the reference the
Priority 2 bomb-limit regression tests work against — it is
intentionally concrete (parameter, default, and semantics of `0`) so
callers and tests can reason about behaviour without re-reading the
source. The corresponding checklist item is Priority 2 items 1–2 in
[plans/track-e-current-audit-checklist.md](/home/kim/lean-zip/plans/track-e-current-audit-checklist.md:65).

### Public decompression / extraction APIs

| Entry point | Parameter | Default | Semantics of 0 | Notes |
|---|---|---|---|---|
| [Zlib.decompress](/home/kim/lean-zip/Zip/Basic.lean:15) (FFI) | `maxDecompressedSize : UInt64` | `1073741824` (1 GiB) | no limit (opt-in) | whole-buffer zlib (RFC 1950). Bomb-limit regression test at [ZipTest/Zlib.lean:17-22](/home/kim/lean-zip/ZipTest/Zlib.lean:17). <!-- drift-detector: quote `maxDecompressedSize : UInt64` is declaration-style and never appears in the test file; cite is correct, heuristic is limited. --> |
| [Gzip.decompress](/home/kim/lean-zip/Zip/Gzip.lean:16) (FFI) | `maxDecompressedSize : UInt64` | `1073741824` (1 GiB) | no limit (opt-in) | whole-buffer gzip (RFC 1952) + auto-zlib. Bomb-limit regression test at [ZipTest/Gzip.lean:18-23](/home/kim/lean-zip/ZipTest/Gzip.lean:18). <!-- drift-detector: quote `maxDecompressedSize : UInt64` is declaration-style and never appears in the test file; cite is correct, heuristic is limited. --> |
| [RawDeflate.decompress](/home/kim/lean-zip/Zip/RawDeflate.lean:20) (FFI) | `maxDecompressedSize : UInt64` | `1073741824` (1 GiB) | no limit (opt-in) | whole-buffer raw DEFLATE (ZIP method 8). Bomb-limit regression test at [ZipTest/RawDeflate.lean:17-22](/home/kim/lean-zip/ZipTest/RawDeflate.lean:17). <!-- drift-detector: quote `maxDecompressedSize : UInt64` is declaration-style and never appears in the test file; cite is correct, heuristic is limited. --> |
| [Gzip.decompressStream](/home/kim/lean-zip/Zip/Gzip.lean:83) (FFI) | `maxDecompressedSize : UInt64` | `1073741824` (1 GiB) | no limit (opt-in) | streaming via `IO.Ref UInt64` counter on pushed output; cap check fires before `output.write`, so the already-written prefix is ≤ `maxDecompressedSize` bytes. Parameter landed by PR #1610; default flipped to 1 GiB by PR #1631. |
| [Gzip.decompressFile](/home/kim/lean-zip/Zip/Gzip.lean:123) (FFI) | `maxDecompressedSize : UInt64` | `1073741824` (1 GiB) | no limit (opt-in) | thin wrapper forwarding to `decompressStream`. Parameter landed by PR #1610; default flipped to 1 GiB by PR #1631. |
| [RawDeflate.decompressStream](/home/kim/lean-zip/Zip/RawDeflate.lean:56) (FFI) | `maxDecompressedSize : UInt64` | `1073741824` (1 GiB) | no limit (opt-in) | streaming raw DEFLATE; same counter/check structure as `Gzip.decompressStream`. Parameter landed by PR #1610; default flipped to 1 GiB by PR #1631. |
| [Zip.Native.Inflate.inflate](/home/kim/lean-zip/Zip/Native/Inflate.lean:384) | `maxOutputSize : Nat` | `1 * 1024^3` (1 GiB) | hard cap at 0 bytes (explicit) | no unlimited mode; default is 1 GiB. |
| [Zip.Native.GzipDecode.decompress](/home/kim/lean-zip/Zip/Native/Gzip.lean:40) | `maxOutputSize : Nat` | `1 * 1024^3` (1 GiB) | hard cap at 0 bytes (explicit) | no unlimited mode; default is 1 GiB (unified with `Inflate.inflate` per Rec. 5). |
| [Zip.Native.ZlibDecode.decompress](/home/kim/lean-zip/Zip/Native/Gzip.lean:140) | `maxOutputSize : Nat` | `1 * 1024^3` (1 GiB) | hard cap at 0 bytes (explicit) | no unlimited mode; default is 1 GiB (unified with `Inflate.inflate` per Rec. 5). |
| [Zip.Native.decompressAuto](/home/kim/lean-zip/Zip/Native/Gzip.lean:240) | `maxOutputSize : Nat` | `1 * 1024^3` (1 GiB) | hard cap at 0 bytes (explicit) | format-auto dispatch over the three natives above. |
| [Archive.list](/home/kim/lean-zip/Zip/Archive.lean:1209) | `maxCentralDirSize : Nat` | `67108864` (64 MiB) | no limit | metadata-only; caps CD allocation, not decompressed payload. |
| [Archive.extract](/home/kim/lean-zip/Zip/Archive.lean:1233) | `maxCentralDirSize : Nat` | `67108864` (64 MiB) | no limit | CD allocation cap. |
| [Archive.extract](/home/kim/lean-zip/Zip/Archive.lean:1233) | `maxEntrySize : UInt64` | `1 * 1024^3` (1 GiB) | pass `0` for unlimited (FFI backend only; native inflate rejects `0`) | per-entry cap on the decompressed payload. |
| [Archive.extract](/home/kim/lean-zip/Zip/Archive.lean:1233) | `maxTotalSize : UInt64` | `0` | no whole-archive cap | running sum across all entries; intended as a second line of defence against many-small-entries bombs. |
| [Archive.extractFile](/home/kim/lean-zip/Zip/Archive.lean:1278) | `maxCentralDirSize : Nat` | `67108864` (64 MiB) | no limit | CD allocation cap. |
| [Archive.extractFile](/home/kim/lean-zip/Zip/Archive.lean:1278) | `maxEntrySize : UInt64` | `1 * 1024^3` (1 GiB) | pass `0` for unlimited (FFI backend only; native inflate rejects `0`) | per-entry cap. |
| [Tar.extract](/home/kim/lean-zip/Zip/Tar.lean:651) | `maxEntrySize : UInt64` | `1 * 1024^3` (1 GiB) | pass `0` for unlimited | per-entry byte cap, applied via header `e.size` before any I/O (see [Zip/Tar.lean:651](/home/kim/lean-zip/Zip/Tar.lean:651)). |
| [Tar.extract](/home/kim/lean-zip/Zip/Tar.lean:651) | `maxTotalSize : UInt64` | `0` | no whole-archive cap | running sum across all regular-file entries; directories and symlinks contribute zero. |
| [Tar.extractTarGz](/home/kim/lean-zip/Zip/Tar.lean:779) | `maxEntrySize : UInt64` | `1 * 1024^3` (1 GiB) | pass `0` for unlimited | per-entry cap. Outer gzip decode is streaming via `Gzip.InflateState`; no per-stream output cap. |
| [Tar.extractTarGz](/home/kim/lean-zip/Zip/Tar.lean:779) | `maxTotalSize : UInt64` | `0` | no whole-archive cap | forwarded to inner `Tar.extract`. |
| [Tar.extractTarGzNative](/home/kim/lean-zip/Zip/Tar.lean:945) | `maxEntrySize : UInt64` | `1 * 1024^3` (1 GiB) | pass `0` for unlimited | per-entry cap. |
| [Tar.extractTarGzNative](/home/kim/lean-zip/Zip/Tar.lean:945) | `maxTotalSize : UInt64` | `0` | no whole-archive cap | forwarded to inner `Tar.extract`. |
| [Tar.extractTarGzNative](/home/kim/lean-zip/Zip/Tar.lean:948) | `maxOutputSize : Nat` | `256 * 1024^2` (256 MiB) | hard cap at 0 bytes (explicit) | whole-archive tar-buffer cap for the outer native gzip decode. |

### Known inconsistencies

_None outstanding — prior inconsistencies resolved by the Track E
audit wave (see *Recommended policy* items flagged "Executed")._

### Recommended policy

This is a **proposal** for the safer-default direction; numbers are
placeholders to seed discussion, not final values. Treat each
recommendation as a starting point for the bomb-limit regression
issues and the follow-up docstring/default change.

1. **Low-level whole-buffer FFI decoders** — `Zlib.decompress`,
   `Gzip.decompress`, `RawDeflate.decompress`.
   Executed — the three FFI whole-buffer decoders now default to 1 GiB;
   `0` continues to mean unlimited on the opt-in path. See PR #1623.
2. **Streaming FFI decoders** — `Gzip.decompressStream`,
   `Gzip.decompressFile`, `RawDeflate.decompressStream`.
   Executed — the three streaming FFI decoders now default to 1 GiB;
   `0` continues to mean unlimited on the opt-in path. See PR #1631.
3. **Archive extraction — per-entry cap** — Executed. The per-entry
   default on `Archive.extract`, `Archive.extractFile`, `Tar.extract`,
   `Tar.extractTarGz`, and `Tar.extractTarGzNative` is now `1 GiB`
   (pass `0` to opt into unlimited mode on the FFI backend), and the
   silent `0 → 256 MiB` upgrade in `Archive.readEntryData` has been
   removed. See PR #1618.
4. **Archive extraction — whole-archive cap**. Executed —
   `Archive.extract`, `Tar.extract`, `Tar.extractTarGz`, and
   `Tar.extractTarGzNative` now accept an optional
   `maxTotalSize : UInt64 := 0` parameter; default `0` is unlimited
   and callers opt into a finite cap. See PR #1630.
5. **Native-side uniformity**. Executed (issue #1609) — all four
   native decoders (`Inflate.inflate`, `GzipDecode.decompress`,
   `ZlibDecode.decompress`, `decompressAuto`) now default to **1 GiB**,
   matching `Zip.Native.Inflate.inflate`. The factor-of-4 asymmetry
   between raw-DEFLATE and format-auto-dispatch is gone.
6. **Docstrings and error messages**. Executed — every public
   decompression / extraction API now states its default cap, the
   meaning of `0` (unlimited on the FFI path; rejects any non-empty
   output on the native path), and the exact `IO.userError` /
   `Except` substring thrown on cap overflow. The closing audit
   covered all twelve decompression / extraction surfaces plus the
   `Archive.list` central-directory cap; the only outstanding gap
   (the `maxOutputSize` paragraph on `Tar.extractTarGzNative`) was
   filled inline in PR #1710. See PR #1710.

Known caller impact if recommendations 1–5 land:

- `ZipTest/*.lean` mostly uses tiny inputs; switching FFI
  decompression defaults to 256 MiB is a no-op there.
- `ZipTest/NativeScale.lean` currently decompresses multi-MiB
  payloads — still well under 256 MiB.
- The public `README.md` example (`Tar.extractTarGz "..."`) works
  unchanged because its proposed default per-entry cap (1 GiB) is
  larger than any realistic test archive.
- No Lean-level caller passes `0` explicitly except the
  implicit default; after the change, callers who need unlimited
  mode must opt in — the migration is local and detectable via
  `grep`.

### Missing work

_All bomb-limit regression coverage proposed in the original block
has landed (Track E P3 + P5 + F-series, 2026-04-22)._ Per-API
coverage is documented in the audit table at
[`progress/20260422T115256Z_d2757984.md`](/home/kim/lean-zip/progress/20260422T115256Z_d2757984.md).
Notably absent surfaces (`Zlib.decompressStream`,
`Zlib.decompressFile`, `RawDeflate.decompressFile`) are absent
because the public API does not expose them, not because tests are
missing.

Residual gaps: none currently open at this layer.

### Local guard inventory for `Handle.read` and `Stream.read`

Per-callsite audit of every `Handle.read`, `Stream.read`, and
`inStream.read` invocation reachable from untrusted archive bytes in
`Zip/Archive.lean` and `Zip/Tar.lean`. This documents which guards
**already run before** each read, so a reader does not have to trace
back through the source to confirm that every metadata-driven read is
protected. The *"Failure mode"* column states the residual
upstream-runtime risk for each site — it is the behaviour that would
surface if the caller bypassed the guard.

The creator-side `h.read` in `Zip/Tar.lean` `create` at
[Zip/Tar.lean:466](/home/kim/lean-zip/Zip/Tar.lean:466) is **not**
listed: it reads local files chosen by the caller (the archive author),
not untrusted archive bytes, so it falls outside this inventory's
scope.

Trust-boundary callers reach the actual `.read` primitive via
`readExact` ([Zip/Archive.lean:869](/home/kim/lean-zip/Zip/Archive.lean:869),
[Zip/Tar.lean:189](/home/kim/lean-zip/Zip/Tar.lean:189)),
`readExactStream` ([Zip/Archive.lean:883](/home/kim/lean-zip/Zip/Archive.lean:883)),
`readEntryData` ([Zip/Tar.lean:220](/home/kim/lean-zip/Zip/Tar.lean:220)),
`skipEntryData` ([Zip/Tar.lean:539](/home/kim/lean-zip/Zip/Tar.lean:539)),
or open-coded read loops. Each row below names the call site that
drives an `n`-byte read; the `readExact`-family helpers themselves
perform a `Nat → USize` roundtrip check before every `Handle.read`.

| Callsite (file:line) | Reads driven by | Local guard | Failure mode if guard absent |
|---|---|---|---|
| [Zip/Archive.lean:883](/home/kim/lean-zip/Zip/Archive.lean:883) `readExactStream` helper (inner `s.read` at line 695) | caller-provided `n : Nat` | `Nat → USize` roundtrip at [Zip/Archive.lean:884](/home/kim/lean-zip/Zip/Archive.lean:884) | no production parser reaches this helper today — only `ZipTest/Archive.lean` exercises it. Any future stream-fed parser that wires into `readExactStream` must apply its own `n`-bound before calling; otherwise this row downgrades to caller-bounded |
| [Zip/Archive.lean:941](/home/kim/lean-zip/Zip/Archive.lean:941) `readExact h tailSize "EOCD tail"` | `tailSize = min fileSize 65558` at [Zip/Archive.lean:938](/home/kim/lean-zip/Zip/Archive.lean:938) | `min` clamp (≤ 65 558 bytes regardless of input); `Nat → USize` roundtrip in `readExact` | N/A — the read is structurally bounded to ≤ 65 558 bytes |
| [Zip/Archive.lean:923](/home/kim/lean-zip/Zip/Archive.lean:923) `readExact h cdSize "central directory"` | `cdSize` parsed from EOCD (attacker-controlled) | `cdOffset + cdSize ≤ fileSize` check at [Zip/Archive.lean:946](/home/kim/lean-zip/Zip/Archive.lean:946); `maxCentralDirSize` cap (default 64 MiB) at [Zip/Archive.lean:919](/home/kim/lean-zip/Zip/Archive.lean:919); `Nat → USize` roundtrip in `readExact` | would request a crafted multi-GB allocation; depends on runtime to reject or OOM |
| [Zip/Archive.lean:967](/home/kim/lean-zip/Zip/Archive.lean:967) `readBoundedSpanFromHandle h fileSize entry.localOffset 30 "local header for {label}"` | fixed `30` bytes | `assertSpanInFile fileSize entry.localOffset 30` internal to `readBoundedSpanFromHandle` at [Zip/Archive.lean:967](/home/kim/lean-zip/Zip/Archive.lean:967) | N/A — fixed 30-byte read |
| [Zip/Archive.lean:995](/home/kim/lean-zip/Zip/Archive.lean:995) `readBoundedSpanFromHandle h fileSize (entry.localOffset + 30) (nameLen + extraLen) "local name+extra for {label}"` | `nameLen + extraLen`, both `UInt16` read from the local header (≤ 2·`UInt16.max` ≈ 128 KiB) | `assertSpanInFile` at [Zip/Archive.lean:995](/home/kim/lean-zip/Zip/Archive.lean:995); `UInt16` type bound on each addend | N/A — `UInt16` type bounds each addend, total ≤ 128 KiB regardless of input |
| [Zip/Archive.lean:1039](/home/kim/lean-zip/Zip/Archive.lean:1039) `readExact h entry.compressedSize.toNat "compressed data for {label}"` | `entry.compressedSize` from CD / ZIP64 local extra (attacker-controlled `UInt64`) | `assertSpanInFile fileSize (entry.localOffset + headerAndNames) entry.compressedSize` at [Zip/Archive.lean:964](/home/kim/lean-zip/Zip/Archive.lean:964); CD-vs-LH `compressedSize` consistency check at [Zip/Archive.lean:1061](/home/kim/lean-zip/Zip/Archive.lean:1061) (only skipped when the LH data-descriptor flag bit 3 is set); CD-vs-LH flags-consistency check (bit-3-masked) at [Zip/Archive.lean:1036](/home/kim/lean-zip/Zip/Archive.lean:1036) — *"flags mismatch between CD and local header"* — rejects mismatched general-purpose flag words before the payload read; CD-vs-LH `versionNeededToExtract` one-sided downgrade check at [Zip/Archive.lean:1046](/home/kim/lean-zip/Zip/Archive.lean:1046) — *"LH versionNeededToExtract (…) exceeds CD versionNeededToExtract (…)"* — rejects LH claiming a higher version than CD (a capability-smuggle vector) before the payload read; `Nat → USize` roundtrip in `readExact`. Regression fixtures: `testdata/zip/malformed/oversized-compressed-size.zip`, `oversized-zip64-compressed-size.zip`, `cd-lh-flags-mismatch.zip`, `cd-lh-uncompsize-mismatch.zip`, `cd-lh-crc-mismatch.zip`, `cd-lh-version-mismatch.zip` | would request petabyte allocation on a crafted oversized `compressedSize`; relies on `assertSpanInFile` + CD/LH consistency to reject before `Handle.read` |
| [Zip/Tar.lean:565](/home/kim/lean-zip/Zip/Tar.lean:565) `readExact input 512` in `forEntries` | fixed `512` (one tar header block) | fixed constant | N/A — fixed 512-byte read |
| [Zip/Tar.lean:572](/home/kim/lean-zip/Zip/Tar.lean:572), [:582](/home/kim/lean-zip/Zip/Tar.lean:582), [:592](/home/kim/lean-zip/Zip/Tar.lean:592), [:598](/home/kim/lean-zip/Zip/Tar.lean:598) `readEntryData input entry.size.toNat maxHeaderSize` (GNU long-name, GNU long-link, PAX extended header, PAX global header) | `entry.size` from tar header (attacker-controlled `UInt64`) | `maxHeaderSize` cap inside `readEntryData` at [Zip/Tar.lean:222](/home/kim/lean-zip/Zip/Tar.lean:222) (default `defaultMaxHeaderSize = 8 MiB` at [Zip/Tar.lean:212](/home/kim/lean-zip/Zip/Tar.lean:212)) — rejects `entry.size > maxHeaderSize` before any allocation with `IO.userError` containing `"exceeds maximum header size"`. Per-chunk reads are also capped at 64 KiB ([Zip/Tar.lean:229](/home/kim/lean-zip/Zip/Tar.lean:229)) and padding at 512 bytes per chunk ([Zip/Tar.lean:238](/home/kim/lean-zip/Zip/Tar.lean:238)). The cap is independent of the caller's `maxEntrySize`, which only bounds payload-bearing entries. Regression fixtures: `testdata/tar/malformed/gnu-longname-oversized-size.tar`, `pax-extended-oversized-size.tar` | with the cap raised, `readEntryData` would accumulate `entry.size` bytes into memory on a crafted GNU long-name or PAX header claiming multi-GB size — depends on runtime allocation to reject |
| [Zip/Tar.lean:619](/home/kim/lean-zip/Zip/Tar.lean:619), [:650](/home/kim/lean-zip/Zip/Tar.lean:650), [:657](/home/kim/lean-zip/Zip/Tar.lean:657), [:671](/home/kim/lean-zip/Zip/Tar.lean:671) `skipEntryData input e.size` (directory-entry payload skip, symlink-entry payload skip, unsupported-typeflag payload skip, `Tar.list`) | `e.size + paddingFor e.size` (attacker-controlled `UInt64`) | 64 KiB per-chunk cap at [Zip/Tar.lean:539](/home/kim/lean-zip/Zip/Tar.lean:539); discarded bytes are not buffered (peak allocation = 64 KiB per iteration) | no memory amplification, but a malicious stream can force an unbounded number of 64 KiB reads. `Tar.extract` applies `maxEntrySize` at [Zip/Tar.lean:661](/home/kim/lean-zip/Zip/Tar.lean:661) for payload-bearing entries before the skip; `Tar.list` applies no cap |
| [Zip/Tar.lean:627](/home/kim/lean-zip/Zip/Tar.lean:627) `input.read toRead.toUSize` in `Tar.extract` regular-file loop | `min remaining 65536` where `remaining ≤ e.size.toNat` (attacker-controlled `UInt64` from tar header) | `maxEntrySize` check at [Zip/Tar.lean:661](/home/kim/lean-zip/Zip/Tar.lean:661) (effective only when `maxEntrySize > 0`); 64 KiB per-chunk cap; data is written through to disk, not buffered | with the default 1 GiB cap, `Tar.extract` writes up to 1 GiB to disk per regular-file entry; with `maxEntrySize = 0` (opt-in unlimited), the read is bounded only by `e.size` (attacker-controlled `UInt64`). The per-read allocation is bounded at 64 KiB regardless. Documented as the "per-entry cap" row in *Decompression Limit Inventory* |
| [Zip/Tar.lean:695](/home/kim/lean-zip/Zip/Tar.lean:695) `input.read (min padRemaining 512).toUSize` in `Tar.extract` padding loop | `min padRemaining 512`; `padRemaining ≤ 511` by tar framing (`paddingFor size < 512`) | fixed 512-byte per-chunk cap; `pad < 512` by tar block alignment | N/A — ≤ 512 bytes per read, bounded by tar block alignment |
| [Zip/Tar.lean:793](/home/kim/lean-zip/Zip/Tar.lean:793) `inStream.read 65536` in `extractTarGz` tarStream wrapper | fixed `65536` | fixed chunk constant regardless of input | N/A — fixed 64 KiB read |

Summary — what the inventory catches and what it does not:

- **Catches**: every metadata-driven read in ZIP extraction
  (`Archive.readEntryData`) is span-checked against the actual file
  size before `Handle.read` runs, and the CD-vs-LH consistency check
  rejects crafted size mismatches before the compressed-payload read.
  Padding and skip reads in `Tar.lean` are bounded per chunk (64 KiB
  or 512 bytes) and discarded, so they cannot amplify memory.
- **Does NOT catch** — one residual gap that would benefit from a
  follow-up issue:
  1. `Tar.extract` row 10 relies on a per-entry `maxEntrySize` cap
     of 1 GiB by default; an attacker who crafts many entries can
     still drive disk usage past this cap because the
     whole-archive `maxTotalSize` parameter on `Tar.extract` /
     `Tar.extractTarGz` / `Tar.extractTarGzNative` defaults to
     `0` (no limit) per Recommended Policy item 4. Callers
     concerned about multi-entry exhaustion must opt into a
     finite `maxTotalSize`.

  The previously-listed `Tar.readEntryData` gap at the four GNU
  long-name / long-link / PAX callsites is now closed by the
  `maxHeaderSize` cap (default `defaultMaxHeaderSize = 8 MiB`) that
  fires in `readEntryData` before any allocation; see row 8 above and
  the `gnu-longname-oversized-size.tar` /
  `pax-extended-oversized-size.tar` regression fixtures.

## Minimized Reproducer Corpus

Each row below is a minimised input that trips a specific defensive
guard in the parsers or extractors. Regression of a listed guard
surfaces as a test failure in
[`ZipTest/ZipFixtures.lean`](/home/kim/lean-zip/ZipTest/ZipFixtures.lean),
[`ZipTest/TarFixtures.lean`](/home/kim/lean-zip/ZipTest/TarFixtures.lean),
or (for the UTF-8 entry-name check)
[`ZipTest/Utf8Fixtures.lean`](/home/kim/lean-zip/ZipTest/Utf8Fixtures.lean).
The corpus realises the *"malformed regression corpus"* goal in
[`PLAN.md` lines 621-624](/home/kim/lean-zip/PLAN.md:621):
*"every discovered crash, panic, timeout, or upstream-runtime issue
gets a minimized reproducer and a permanent regression test when
feasible."*

<!-- convention: line anchors for CD/LH consistency checks (and any
     other `unless … throw` guard) point to the `s!"…"` throw-message
     line — the line a debugger lands on and the one a reader sees in
     the `IO.userError` stack trace — not the `unless` predicate
     above it. The ±2-line tolerance in
     scripts/check-inventory-links.sh accepts either form but readers
     expect the throw line; use it consistently across the corpus
     rows below and the cross-references in the *Local guard
     inventory* table above. -->

Columns:

- **Fixture** — relative-path link into `testdata/`.
- **Size** — on-disk byte size (as reported by `wc -c`).
- **Defence exercised** — the concrete guard that must continue to
  trip, linked to the source line that raises the error or applies
  the silent-skip policy.
- **First landed** — PR number if the fixture entered via a dedicated
  PR; commit `481e562` for the fixtures inherited from the initial
  `lean-zlib → lean-zip` import (no PR).
- **Related class** — one of {*oversized allocation*,
  *partial-decoder panic*, *archive-slip*, *decompression bomb*,
  *other*} so an auditor tracking regressions of a single class can
  filter.

Row order: by `testdata/` subdirectory, then alphabetically within
each subdirectory. Every row below has a live assertion in
`ZipTest/` (checked by `grep`-of-filename across `ZipTest/`); no
fixture is currently orphaned. `hardlink-outside.tar` is a
*positive* regression — the assertion is that extraction leaves the
output directory empty, confirming that `typeHardlink` continues
to be silently skipped.

| Fixture (testdata/…) | Size | Defence exercised | First landed | Related class |
|---|---|---|---|---|
| [testdata/tar/malformed/bad-checksum.tar](/home/kim/lean-zip/testdata/tar/malformed/bad-checksum.tar) | 2048 B | Tar header checksum verification at [Zip/Tar.lean:487](/home/kim/lean-zip/Zip/Tar.lean:487) — *"header checksum mismatch"* | `481e562` | other (integrity check) |
| [testdata/tar/malformed/gnu-longlink-nul-in-link.tar](/home/kim/lean-zip/testdata/tar/malformed/gnu-longlink-nul-in-link.tar) | 1536 B | GNU long-link NUL-byte rejection at [Zip/Tar.lean:679](/home/kim/lean-zip/Zip/Tar.lean:679) — *"GNU long-link contains NUL byte"* (long-link payload is `"safe.lnk\x00rogue.tar"` — 18 bytes; "safe.lnk" + interior NUL + "rogue.tar"; the payload's last byte is `'r'` so `stripTrailingNuls` is a no-op and the interior NUL at index 8 survives into the `findIdx?` guard, which rejects on the raw `ByteArray` before `String.fromUTF8?` / `Binary.fromLatin1` runs, so neither decode branch re-introduces NUL into logs. Pre-PR, `entry.linkname` would be the full NUL-embedded string on `Tar.list` and POSIX `open` would truncate at NUL on `Tar.extract` — classic parser-differential / filesystem-truncation smuggle. A trailing zero-length regular-file entry (`size := 0`, `path := "_"`) is appended so the fixture exercises the override application path fully — but the guard fires on the long-link pseudo-entry itself, so the trailing entry is only reached by the no-guard regression baseline. Per-slot family closure: this is the long-link arm of the 2-slot `forEntries` interior-NUL guard family — the long-name arm is `gnu-longname-nul-in-name.tar` (PR #1865, long-name slot at line 667); together the two close the GNU long-name / long-link interior-NUL guard family at every per-slot position. PR #1865 added both guards in a single landing but only emitted the long-name fixture; this fixture closes the per-slot fixture asymmetry, mirroring the post-#1880/#1934/#1937 per-slot wave that closed the 3-slot UStar `name`/`linkname`/`prefix` family and the post-#1944 4th-slot `uname` defense-in-depth extension. Test substring includes `"long-link"` to keep per-slot distinction — the bare `"GNU long-"` prefix would also match the long-name arm. Writer-side has no invariant to record — lean-zip's tar writer does not emit GNU long-name / long-link pseudo-entries) | #1953 | archive-slip |
| [testdata/tar/malformed/gnu-longlink-truncated.tar](/home/kim/lean-zip/testdata/tar/malformed/gnu-longlink-truncated.tar) | 612 B | `readEntryData` short-read at [Zip/Tar.lean:230](/home/kim/lean-zip/Zip/Tar.lean:230) — *"unexpected end of archive reading entry data"* | #1546 | partial-decoder panic |
| [testdata/tar/malformed/gnu-longname-invalid-utf8.tar](/home/kim/lean-zip/testdata/tar/malformed/gnu-longname-invalid-utf8.tar) | 1536 B | `String.fromUTF8?` → `Binary.fromLatin1` fallback at [Zip/Tar.lean:670](/home/kim/lean-zip/Zip/Tar.lean:670) (no panicking `fromUTF8!` path) | #1546 | partial-decoder panic |
| [testdata/tar/malformed/gnu-longname-no-terminator.tar](/home/kim/lean-zip/testdata/tar/malformed/gnu-longname-no-terminator.tar) | 1536 B | `stripTrailingNuls` is a no-op when the payload has no trailing NUL ([Zip/Tar.lean:619](/home/kim/lean-zip/Zip/Tar.lean:619)); full payload becomes the name without a panic | #1546 | partial-decoder panic |
| [testdata/tar/malformed/gnu-longname-nul-in-name.tar](/home/kim/lean-zip/testdata/tar/malformed/gnu-longname-nul-in-name.tar) | 1536 B | GNU long-name NUL-byte rejection at [Zip/Tar.lean:667](/home/kim/lean-zip/Zip/Tar.lean:667) — *"GNU long-name contains NUL byte"* (long-name payload is `"evil.txt\x00.tar"`; `stripTrailingNuls` preserves the interior NUL; `forEntries` rejects on the raw `ByteArray` before `String.fromUTF8?` / `Binary.fromLatin1` runs, so neither decode branch re-introduces NUL into logs. Pre-PR, `entry.path` would be the full NUL-embedded string on `Tar.list` and POSIX `open` would truncate at NUL on `Tar.extract` — classic parser-differential / filesystem-truncation smuggle. Tar-side sibling of the ZIP CD-parse NUL-byte guard (PR #1831 / `cd-nul-in-name.zip`) at the same NUL-in-filename attack dimension; the long-link typeflag `'K'` arm at [Zip/Tar.lean:679](/home/kim/lean-zip/Zip/Tar.lean:679) carries the structurally identical guard — *"GNU long-link contains NUL byte"* — now covered by the dedicated per-slot fixture `gnu-longlink-nul-in-link.tar` (PR #1953); together the two fixtures close the 2-slot GNU long-name / long-link interior-NUL family at 2/2 — sibling cadence to the 5-slot UStar interior-NUL family closure at PR #1957. PAX `path` arm closed by PR #1866 (`pax-path-nul-in-value.tar`) and `linkpath` arm closed by PR #1979 (`pax-linkpath-nul-in-value.tar`) — the 2-slot PAX value-side override family is closed 2/2) | #1865 | archive-slip |
| [testdata/tar/malformed/gnu-longname-oversized-size.tar](/home/kim/lean-zip/testdata/tar/malformed/gnu-longname-oversized-size.tar) | 512 B | `readEntryData` `maxHeaderSize` cap at [Zip/Tar.lean:252](/home/kim/lean-zip/Zip/Tar.lean:252) — *"exceeds maximum header size"* (header `size ≈ 8 GiB`, default cap `8 MiB`) | #1597 | oversized allocation |
| [testdata/tar/malformed/gnu-longname-truncated.tar](/home/kim/lean-zip/testdata/tar/malformed/gnu-longname-truncated.tar) | 612 B | `readEntryData` short-read at [Zip/Tar.lean:230](/home/kim/lean-zip/Zip/Tar.lean:230) — *"unexpected end of archive reading entry data"* | #1546 | partial-decoder panic |
| [testdata/tar/malformed/no-magic.tar](/home/kim/lean-zip/testdata/tar/malformed/no-magic.tar) | 2048 B | Tar magic check at [Zip/Tar.lean:491](/home/kim/lean-zip/Zip/Tar.lean:491) — *"unsupported format"* | `481e562` | other (header validation) |
| [testdata/tar/malformed/pax-duplicate-path.tar](/home/kim/lean-zip/testdata/tar/malformed/pax-duplicate-path.tar) | 2048 B | `parsePaxRecords` duplicate-key guard at [Zip/Tar.lean:147](/home/kim/lean-zip/Zip/Tar.lean:147) — *"tar: PAX extended header has duplicate {key.quote} record"* (ordering inside `parsePaxRecords`: UTF-8 decode → raw-byte NUL guard → duplicate-key check → push, so the duplicate-key branch only fires on records that already passed the UTF-8 and NUL filters. Unlike the sibling PR #1866 PAX NUL-byte silent-skip further below — which drops the offending record and continues — PR #1899 hard-rejects by writing `err := some …` and `break`ing the record loop; the `.error` return is rethrown unconditionally by the sole production caller at [Zip/Tar.lean:669](/home/kim/lean-zip/Zip/Tar.lean:669) inside `forEntries`'s `typePaxExtended` branch via `throw (IO.userError msg)`. `String.quote` on the duplicate key pins attribution in logs without leaking NUL or control bytes. Attack class: PAX records allow duplicate keys syntactically, and `applyPaxOverrides`'s default last-wins-silent policy leaves the smuggle exploitable unless the parser rejects duplicates structurally — a crafted second `path=` record would otherwise override the first, enabling parser-differential attacks where strict peer parsers (which reject or use first-wins) disagree with lean-zip. Closes the parser-differential *duplicate-key* dimension on `parsePaxRecords` complementary to PR #1866's NUL-byte silent-skip; together the two close both parser-differential dimensions on the PAX-record decode pipeline. Writer-side has no invariant to record — lean-zip's tar writer does not emit PAX extended headers) | #1899 | archive-slip |
| [testdata/tar/malformed/pax-extended-oversized-size.tar](/home/kim/lean-zip/testdata/tar/malformed/pax-extended-oversized-size.tar) | 512 B | `readEntryData` `maxHeaderSize` cap at [Zip/Tar.lean:252](/home/kim/lean-zip/Zip/Tar.lean:252) — *"exceeds maximum header size"* (PAX header `size ≈ 8 GiB`, default cap `8 MiB`) | #1597 | oversized allocation |
| [testdata/tar/malformed/pax-inconsistent-length.tar](/home/kim/lean-zip/testdata/tar/malformed/pax-inconsistent-length.tar) | 2048 B | `parsePaxRecords` silent-skip when no `=` is found before the declared record end (scan at [Zip/Tar.lean:118](/home/kim/lean-zip/Zip/Tar.lean:118); record dropped at [Zip/Tar.lean:118](/home/kim/lean-zip/Zip/Tar.lean:118)) | #1545 | partial-decoder panic |
| [testdata/tar/malformed/pax-invalid-utf8-key.tar](/home/kim/lean-zip/testdata/tar/malformed/pax-invalid-utf8-key.tar) | 2048 B | `parsePaxRecords` `String.fromUTF8?` guard on key/value at [Zip/Tar.lean:144](/home/kim/lean-zip/Zip/Tar.lean:144) (record dropped, no panic) | #1545 | partial-decoder panic |
| [testdata/tar/malformed/pax-invalid-utf8-value.tar](/home/kim/lean-zip/testdata/tar/malformed/pax-invalid-utf8-value.tar) | 2048 B | Same `String.fromUTF8?` guard at [Zip/Tar.lean:144](/home/kim/lean-zip/Zip/Tar.lean:144) | #1545 | partial-decoder panic |
| [testdata/tar/malformed/pax-linkpath-nul-in-value.tar](/home/kim/lean-zip/testdata/tar/malformed/pax-linkpath-nul-in-value.tar) | 2048 B | `parsePaxRecords` NUL-byte guard on `valueBytes` at [Zip/Tar.lean:146](/home/kim/lean-zip/Zip/Tar.lean:146) (record dropped silently, matching the invalid-UTF-8 precedent on the same loop). Fixture carries the PAX record `"18 linkpath=a\x00b/c\n"` — `String.fromUTF8?` accepts U+0000 so without the guard the `linkpath` override would smuggle into `applyPaxOverrides`'s `"linkpath"` arm at [Zip/Tar.lean:162](/home/kim/lean-zip/Zip/Tar.lean:162) and land as `entry.linkname = "a\x00b/c"` — a `symlink(2)` truncation smuggle that POSIX `symlink` reduces to `"a"` on the `Tar.extract` symlink path while `Tar.list` callers routing on `entry.linkname` for trust decisions see the full NUL-embedded string. Assertion is a *positive regression* (like the sibling `pax-path-nul-in-value.tar` row two rows below): the loop's `entries[0]!.path == "hello.txt"` check confirms the regular-file entry is unaffected, and a per-slot follow-up assertion confirms `entries[0]!.linkname == ""` (its declared default for `typeRegular`) rather than the smuggled `"a\x00b/c"`. Per-slot family closure: this is the `linkpath` slot of the 2-slot PAX value-side override family — sibling `pax-path-nul-in-value.tar` (PR #1866) covers the `path` slot at [Zip/Tar.lean:161](/home/kim/lean-zip/Zip/Tar.lean:161). With this fixture the 2-slot value-side override family is **fully closed 2/2** — terminal closure of the third per-slot Tar interior-NUL family in the post-#1928 wave (after the 5-slot UStar family closed at PR #1957 and the 2-slot GNU long-name / long-link family closed at PR #1953); together the three closures complete the "smuggled NUL in any user-supplied string field" attack class across the entire Tar parsing surface (UStar + GNU + PAX). The companion `keyBytes` arm at [Zip/Tar.lean:145](/home/kim/lean-zip/Zip/Tar.lean:145) is defense-in-depth (no known-key string contains `\x00`, so `applyPaxOverrides`'s case match would already drop a NUL-bearing key) and is left for a future per-arm extension. Writer-side has no invariant to record — lean-zip's tar writer does not emit PAX extended headers | #1979 | archive-slip |
| [testdata/tar/malformed/pax-oversized-length.tar](/home/kim/lean-zip/testdata/tar/malformed/pax-oversized-length.tar) | 2048 B | `parsePaxRecords` `digitCount > 20` guard at [Zip/Tar.lean:108](/home/kim/lean-zip/Zip/Tar.lean:108) (length-parse aborted before multiplying) | #1545 | oversized allocation |
| [testdata/tar/malformed/pax-path-nul-in-value.tar](/home/kim/lean-zip/testdata/tar/malformed/pax-path-nul-in-value.tar) | 2048 B | `parsePaxRecords` NUL-byte guard on `keyBytes` / `valueBytes` at [Zip/Tar.lean:122](/home/kim/lean-zip/Zip/Tar.lean:122) (record dropped silently, matching the invalid-UTF-8 precedent one line above). Fixture carries the PAX record `"14 path=a\x00b/c\n"` — `String.fromUTF8?` accepts U+0000 so without the guard the `path` override would smuggle into `applyPaxOverrides` and land as `entry.path = "a\x00b/c"`, a filesystem-truncation smuggle that POSIX `open` reduces to `"a"` while `Tar.list` callers see the full NUL-embedded string. Assertion is a *positive regression* (like `hardlink-outside.tar`): `Tar.list` returns the follow-on regular-file entry with its declared `"hello.txt"` path rather than the smuggled override. Per-slot family closure: this is the `path` slot of the 2-slot PAX value-side override family — sibling `pax-linkpath-nul-in-value.tar` (PR #1979) covers the `linkpath` slot at [Zip/Tar.lean:162](/home/kim/lean-zip/Zip/Tar.lean:162); together the family is **fully closed 2/2** — terminal closure of the third per-slot Tar interior-NUL family in the post-#1928 wave (after the 5-slot UStar family closed at PR #1957 and the 2-slot GNU long-name / long-link family closed at PR #1953). Sibling of the ZIP CD name NUL guard (PR #1831, `cd-nul-in-name.zip`), the GNU long-name / long-link 2/2 NUL guards (PRs #1865 / #1953, `gnu-longname-nul-in-name.tar` / `gnu-longlink-nul-in-link.tar`), the UStar 5/5 interior-NUL guards (PRs #1880 / #1934 / #1937 / #1944 / #1957, `ustar-{name,linkname,prefix,uname,gname}-nul-in-*.tar`), and the PAX value-side 2/2 silent-skip in `parsePaxRecords` (PRs #1866 / #1979, `pax-{path,linkpath}-nul-in-value.tar`); together the post-#1928 wave closes the "smuggled NUL in any user-supplied string field" attack class across the entire Tar parsing surface (UStar + GNU + PAX) plus the ZIP CD entry name. Writer-side has no invariant to record — lean-zip's tar writer does not emit PAX extended headers | #1866 | archive-slip |
| [testdata/tar/malformed/pax-truncated-record.tar](/home/kim/lean-zip/testdata/tar/malformed/pax-truncated-record.tar) | 2048 B | `parsePaxRecords` `recordEnd > data.size` guard at [Zip/Tar.lean:118](/home/kim/lean-zip/Zip/Tar.lean:118) (iteration breaks, remaining bytes ignored) | #1545 | partial-decoder panic |
| [testdata/tar/malformed/truncated.tar](/home/kim/lean-zip/testdata/tar/malformed/truncated.tar) | 522 B | `Tar.extract` regular-file loop short-read at [Zip/Tar.lean:783](/home/kim/lean-zip/Zip/Tar.lean:783) — *"unexpected end of archive reading {e.path} ({remaining} bytes remaining)"* | `481e562` | other (framing) |
| [testdata/tar/malformed/ustar-gname-nul-in-gname.tar](/home/kim/lean-zip/testdata/tar/malformed/ustar-gname-nul-in-gname.tar) | 1536 B | UStar `gname` field interior-NUL rejection at [Zip/Tar.lean:539](/home/kim/lean-zip/Zip/Tar.lean:539) — *"UStar gname contains NUL byte"* (UStar header for a zero-byte regular file with `path = "safe"` and `gname = "trusted\x00rogue"` — 12 meaningful bytes in the gname slot at offset 297 including the embedded NUL, then 20 bytes of NUL padding to byte 329; checksum recomputed to match. `parseHeader` runs `hasInteriorNul` on the raw 512-byte block after the checksum + magic checks and before the five `Binary.readString` calls, in source-position order (`name` → `linkname` → `prefix` → `uname` → `gname`); the four earlier-arm guards do not fire because `path` / `linkname` / `prefix` / `uname` are NUL-free, so attribution pins on the `gname` arm specifically. Without the guard, `Binary.readString` would truncate the gname at the NUL to `"trusted"` (parser-differential smuggle: `Tar.list` callers routing on `entry.gname` for a trust decision see the short prefix while strict peer parsers — GNU tar, BSD tar, libarchive — preserve the full bytes). Like `uname`, `gname` does not reach the filesystem in `Tar.extract` — the guard is defense-in-depth at the `Tar.list` layer. Two trailing zero blocks (1024 B) match the per-slot sibling fixtures' well-formed end-of-archive. Per-slot family closure: this fixture is the **5th and final** slot of the 5-slot UStar interior-NUL family — siblings `ustar-name-nul-in-name.tar` (PR #1880, `name` slot) / `ustar-linkname-nul-in-name.tar` (PR #1934, `linkname` slot) / `ustar-prefix-nul-in-name.tar` (PR #1937, `prefix` slot) cover the 3-slot filesystem-reaching arm at offsets 0 / 157 / 345; `ustar-uname-nul-in-uname.tar` (PR #1944, `uname` slot at offset 265) opened the 2-slot defense-in-depth arm; this fixture closes that arm at offset 297 / 32 B. With this fixture the 5-slot UStar interior-NUL family is **fully closed 5/5** — no more sibling per-slot fixtures expected. Test substring includes `"gname"` to keep per-slot distinction — the bare `"UStar"` prefix would also match the four earlier arms. Writer-side at `buildHeader` (`hdrGname`) uses `Binary.writeString`, which is NUL-padding-only — no interior NUL can be emitted unless `entry.gname` carries a literal `\x00` codepoint, so the guard never fires on legitimate archives produced by `Tar.create`) | #1957 | archive-slip |
| [testdata/tar/malformed/ustar-linkname-nul-in-name.tar](/home/kim/lean-zip/testdata/tar/malformed/ustar-linkname-nul-in-name.tar) | 1536 B | UStar `linkname` field interior-NUL rejection at [Zip/Tar.lean:517](/home/kim/lean-zip/Zip/Tar.lean:517) — *"UStar linkname contains NUL byte"* (UStar header for a zero-byte regular file with `path = "safe"` and `linkname = "evil.lnk\x00.tar"` — 13 meaningful bytes in the linkname slot at offset 157 including the embedded NUL, then 87 bytes of NUL padding to byte 257; checksum recomputed to match. `parseHeader` runs `hasInteriorNul` on the raw 512-byte block after the checksum + magic checks and before the three `Binary.readString` calls; the `name`-arm guard at [Zip/Tar.lean:515](/home/kim/lean-zip/Zip/Tar.lean:515) does not fire because the `path` field is NUL-free, so attribution pins on the `linkname` arm specifically. Two trailing zero blocks (1024 B) match the `name`-slot sibling fixture's well-formed end-of-archive. Per-slot family closure: the sibling `ustar-name-nul-in-name.tar` (PR #1880, `name` slot at line 515) covers offset 0 / 100 B; this fixture covers offset 157 / 100 B. The `prefix`-arm guard at [Zip/Tar.lean:519](/home/kim/lean-zip/Zip/Tar.lean:519) — *"UStar prefix contains NUL byte"* (offset 345, 155 B) — shares the same `hasInteriorNul` helper and `Binary.readString` truncation path and remains covered by symmetric code review (matching the PR #1865 long-link policy and the in-flight 6-slot ZIP64-override family per-slot-fixture cadence — PR #1745 / #1905 / #1908 / #1911 / #1922 / in-flight #1902 — where each per-slot fixture pins a distinct sub-check of a shared guard). Test substring includes `"linkname"` to keep per-slot distinction — the bare `"UStar"` prefix would also match the `name` and `prefix` arms. Writer-side at [Zip/Tar.lean:381](/home/kim/lean-zip/Zip/Tar.lean:381) (`linkname`) uses `Binary.writeString`, which is NUL-padding-only — no interior NUL can be emitted unless `entry.linkname` carries a literal `\x00` codepoint, so the guard never fires on legitimate archives produced by `Tar.create`) | #1934 | archive-slip |
| [testdata/tar/malformed/ustar-name-nul-in-name.tar](/home/kim/lean-zip/testdata/tar/malformed/ustar-name-nul-in-name.tar) | 1536 B | UStar `name` field interior-NUL rejection at [Zip/Tar.lean:497](/home/kim/lean-zip/Zip/Tar.lean:497) — *"UStar name contains NUL byte"* (UStar header at offset 0 carries `name = "evil.txt\x00.tar"` — 13 meaningful bytes including the embedded NUL, then 87 bytes of NUL padding to byte 100; checksum recomputed to match. `parseHeader` runs `hasInteriorNul` on the raw 512-byte block after the checksum + magic checks and before any `Binary.readString` call, so the NUL-truncation that `Binary.readString` would otherwise apply (returning `"evil.txt"` and silently dropping the smuggled `".tar"` suffix) cannot leak into `Tar.list` callers or POSIX `open(2)` on the `Tar.extract` path. Pre-PR, `Tar.list` would report `entry.path = "evil.txt"` while strict peer parsers (GNU tar, BSD tar, libarchive) preserve `"evil.txt\x00.tar"` or reject — a classic parser-differential / filesystem-truncation smuggle. Two trailing zero blocks (1024 B) form a well-formed end-of-archive that strict peer parsers accept; the guard fires during header parse, so the trailing blocks are only exercised by the no-guard regression baseline. Sibling-arm coverage: the `linkname` arm at [Zip/Tar.lean:499](/home/kim/lean-zip/Zip/Tar.lean:499) — *"UStar linkname contains NUL byte"* (offset 157, 100 B) — and the `prefix` arm at [Zip/Tar.lean:501](/home/kim/lean-zip/Zip/Tar.lean:501) — *"UStar prefix contains NUL byte"* (offset 345, 155 B) — share the same `hasInteriorNul` helper and the same `Binary.readString` truncation path, so they are covered by symmetric code review rather than dedicated fixtures (matching the PR #1865 long-link policy and the `hardlink-outside.tar` positive-regression precedent). Closes the UStar layer of the smuggled-NUL attack class — sibling of the ZIP CD-parse name guard (PR #1831, `cd-nul-in-name.zip`), the GNU long-name / long-link guards (PR #1865, `gnu-longname-nul-in-name.tar`), and the PAX `keyBytes` / `valueBytes` silent-skip in `parsePaxRecords` (PR #1866, `pax-path-nul-in-value.tar`); together the quartet closes the "smuggled NUL in any user-supplied string field" attack class across ZIP and Tar at every layer where a NUL could survive into `entry.path` / `entry.linkname`. Writer-side at [Zip/Tar.lean:351](/home/kim/lean-zip/Zip/Tar.lean:351) (`name`), `:363` (`linkname`), `:371` (`prefix`) uses `Binary.writeString`, which is NUL-padding-only — no interior NUL can be emitted unless `entry.path` / `entry.linkname` carries a literal `\x00` codepoint, so the guard never fires on legitimate archives produced by `Tar.create`. Interop pre-flight over `testdata/tar/{interop,malformed,security}/*.tar` returned zero hits before landing) | #1880 | archive-slip |
| [testdata/tar/malformed/ustar-prefix-nul-in-name.tar](/home/kim/lean-zip/testdata/tar/malformed/ustar-prefix-nul-in-name.tar) | 1536 B | UStar `prefix` field interior-NUL rejection at [Zip/Tar.lean:519](/home/kim/lean-zip/Zip/Tar.lean:519) — *"UStar prefix contains NUL byte"* (UStar header for a zero-byte regular file built with `pathOverride := some ("badpfx\x00bad", "name.txt")` so the prefix slot at offset 345 carries `"badpfx\x00bad"` — 10 meaningful bytes including the embedded NUL, then 145 bytes of NUL padding to byte 500; checksum recomputed to match. The `name` slot at offset 0 carries the clean `"name.txt"` so the `name`-arm guard at [Zip/Tar.lean:515](/home/kim/lean-zip/Zip/Tar.lean:515) does not fire — attribution pins on the `prefix` arm specifically. Without the guard, `Binary.readString` would truncate the prefix at the NUL to `"badpfx"`, and `pfx ++ "/" ++ name` at [Zip/Tar.lean:522](/home/kim/lean-zip/Zip/Tar.lean:522) would yield `"badpfx/name.txt"` (parser-differential / filesystem-truncation smuggle: `Tar.list` callers see the short form while POSIX `open(2)` truncates at the same NUL on `Tar.extract`). Two trailing zero blocks (1024 B) match the `name`-slot and `linkname`-slot sibling fixtures' well-formed end-of-archive. Per-slot family closure: this fixture covers offset 345 / 155 B, the third and final slot of the 3-slot UStar interior-NUL guard at lines 515 / 517 / 519 — siblings `ustar-name-nul-in-name.tar` (PR #1880, `name` slot) and `ustar-linkname-nul-in-name.tar` (PR #1934, `linkname` slot) cover offsets 0 / 100 B and 157 / 100 B respectively. Test substring includes `"prefix"` to keep per-slot distinction — the bare `"UStar"` prefix would also match the `name` and `linkname` arms. Writer-side at [Zip/Tar.lean:389](/home/kim/lean-zip/Zip/Tar.lean:389) (`prefix`) uses `Binary.writeString`, which is NUL-padding-only — no interior NUL can be emitted unless `entry.path` carries a literal `\x00` codepoint that survives `splitPath` or unless a caller passes `pathOverride` with a NUL (as this fixture does), so the guard never fires on legitimate archives produced by `Tar.create`) | #1937 | archive-slip |
| [testdata/tar/malformed/ustar-uname-nul-in-uname.tar](/home/kim/lean-zip/testdata/tar/malformed/ustar-uname-nul-in-uname.tar) | 1536 B | UStar `uname` field interior-NUL rejection at [Zip/Tar.lean:537](/home/kim/lean-zip/Zip/Tar.lean:537) — *"UStar uname contains NUL byte"* (UStar header for a zero-byte regular file with `path = "safe"` and `uname = "trusted\x00rogue"` — 12 meaningful bytes in the uname slot at offset 265 including the embedded NUL, then 20 bytes of NUL padding to byte 297; checksum recomputed to match. `parseHeader` runs `hasInteriorNul` on the raw 512-byte block after the checksum + magic checks and before the four `Binary.readString` calls, in source-position order (`name` → `linkname` → `prefix` → `uname`); the three earlier-arm guards at [Zip/Tar.lean:531](/home/kim/lean-zip/Zip/Tar.lean:531) / [:533](/home/kim/lean-zip/Zip/Tar.lean:533) / [:535](/home/kim/lean-zip/Zip/Tar.lean:535) do not fire because `path` / `linkname` / `prefix` are NUL-free, so attribution pins on the `uname` arm specifically. Without the guard, `Binary.readString` would truncate the uname at the NUL to `"trusted"` (parser-differential smuggle: `Tar.list` callers routing on `entry.uname` for a trust decision see the short prefix while strict peer parsers — GNU tar, BSD tar, libarchive — preserve the full bytes). Unlike the 3-slot filesystem-reaching family (`name` / `linkname` / `prefix`), `uname` does not reach the filesystem in `Tar.extract` — the guard is defense-in-depth at the `Tar.list` layer. Two trailing zero blocks (1024 B) match the per-slot sibling fixtures' well-formed end-of-archive. Per-slot family extension: this fixture extends the closed 3-slot family — siblings `ustar-name-nul-in-name.tar` (PR #1880, `name` slot at line 531) / `ustar-linkname-nul-in-name.tar` (PR #1934, `linkname` slot at line 533) / `ustar-prefix-nul-in-name.tar` (PR #1937, `prefix` slot at line 535) cover offsets 0 / 100 B, 157 / 100 B, and 345 / 155 B respectively; this fixture covers offset 265 / 32 B (the 4th slot). The `gname` slot at offset 297 / 32 B is the final (5-slot) sibling deferred to a follow-up planner cycle. Test substring includes `"uname"` to keep per-slot distinction — the bare `"UStar"` prefix would also match the three earlier arms. Writer-side at [Zip/Tar.lean:386](/home/kim/lean-zip/Zip/Tar.lean:386) (`uname`) uses `Binary.writeString`, which is NUL-padding-only — no interior NUL can be emitted unless `entry.uname` carries a literal `\x00` codepoint, so the guard never fires on legitimate archives produced by `Tar.create`) | #1944 | archive-slip |
| [testdata/tar/security/backslash-slip.tar](/home/kim/lean-zip/testdata/tar/security/backslash-slip.tar) | 2048 B | `Binary.isPathSafe` rejects backslashes before component-level `..` check at [Zip/Tar.lean:639](/home/kim/lean-zip/Zip/Tar.lean:639) — *"unsafe path"* | `481e562` (assertion added by #1555) | archive-slip |
| [testdata/tar/security/hardlink-outside.tar](/home/kim/lean-zip/testdata/tar/security/hardlink-outside.tar) | 512 B | `typeHardlink` silent-skip else-branch at [Zip/Tar.lean:807](/home/kim/lean-zip/Zip/Tar.lean:807); payload discarded, no `createHardlink` call, extract directory remains empty | #1555 | archive-slip |
| [testdata/tar/security/symlink-absolute.tar](/home/kim/lean-zip/testdata/tar/security/symlink-absolute.tar) | 512 B | Symlink linkname absolute/backslash check at [Zip/Tar.lean:799](/home/kim/lean-zip/Zip/Tar.lean:799) — *"unsafe symlink target"* | #1555 | archive-slip |
| [testdata/tar/security/symlink-slip.tar](/home/kim/lean-zip/testdata/tar/security/symlink-slip.tar) | 10240 B | Symlink linkname component `..` check at [Zip/Tar.lean:801](/home/kim/lean-zip/Zip/Tar.lean:801) — *"unsafe symlink target"* | `481e562` | archive-slip |
| [testdata/tar/security/tar-absolute.tar](/home/kim/lean-zip/testdata/tar/security/tar-absolute.tar) | 2048 B | `Binary.isPathSafe` rejects absolute paths at [Zip/Tar.lean:639](/home/kim/lean-zip/Zip/Tar.lean:639) — *"unsafe path"* | `481e562` | archive-slip |
| [testdata/tar/security/tar-slip.tar](/home/kim/lean-zip/testdata/tar/security/tar-slip.tar) | 10240 B | `Binary.isPathSafe` rejects `..` component traversal at [Zip/Tar.lean:639](/home/kim/lean-zip/Zip/Tar.lean:639) — *"unsafe path"* | `481e562` | archive-slip |
| [testdata/zip/malformed/bad-crc.zip](/home/kim/lean-zip/testdata/zip/malformed/bad-crc.zip) | 140 B | Post-extraction CRC32 verification at [Zip/Archive.lean:1199](/home/kim/lean-zip/Zip/Archive.lean:1199) — *"CRC32 mismatch"* | `481e562` | other (integrity check) |
| [testdata/zip/malformed/bad-method.zip](/home/kim/lean-zip/testdata/zip/malformed/bad-method.zip) | 140 B | CD-entry compression-method allowlist check at [Zip/Archive.lean:713](/home/kim/lean-zip/Zip/Archive.lean:713) — *"unsupported compression method"* (CD/LH both advertise method=14 (LZMA), outside lean-zip's `{0, 8}` allowlist; `parseCentralDir` rejects at CD parse time, pre-ZIP64-resolution, before any LH read. Previously caught by the late method-dispatch guard at [Zip/Archive.lean:1194](/home/kim/lean-zip/Zip/Archive.lean:1194) — *"unsupported method"* — which still fires as defense-in-depth if a future caller bypasses CD parsing) | #1801 | other (method validation) |
| [testdata/zip/malformed/cd-bad-lh-signature.zip](/home/kim/lean-zip/testdata/zip/malformed/cd-bad-lh-signature.zip) | 122 B | Late LH-signature guard regression coverage at [Zip/Archive.lean:1081](/home/kim/lean-zip/Zip/Archive.lean:1081) — *"bad local header signature for {label}"* (122-byte single-entry stored `hello.txt` archive — LH at file offset 0, CD at offset 45, EOCD at offset 100 — where the LH's first 4 bytes are overwritten with `0xCAFEBABE` (LE: `BE BA FE CA`) instead of the APPNOTE §4.3.7 `sigLocal = 0x04034b50`. The CD itself is byte-identical to the stock baseline so every CD-parse guard passes (`localOffset = 0`, `localOffset + 30 ≤ cdOffset = 45`, `entryEnd = 45 ≤ cdEnd = 100`, method ∈ {0, 8}, stored-method `compSize == uncompSize`, etc.) and `assertSpanInFile` / `readBoundedSpanFromHandle` clear the LH span (30 B at offset 0 ≤ fileSize 122). `Archive.list` never reads the LH and lists the fixture cleanly; only `Archive.extract` throws — confirming that the late LH-signature guard is `Archive.extract`'s defense-in-depth catch for archives that slip past every CD-parse and span guard. Fixture-only regression coverage (no new guard code, no new error wording, no caller / signature change) — pattern matches PRs #1761 / #1889 (`zip64-eocd64-bad-recsize.zip` / `zip64-eocd64-v2-record.zip` at the EOCD64 record-size guard) and in-flight #1885 (`cd-entry-past-cdend.zip` at the `entryEnd > cdEnd` guard). Sibling of `cd-entry-localoffset-past-cdstart.zip` (PR #1813, fires the per-entry `localOffset + 30 ≤ cdOffset` CD-parse guard before the LH read) and `cd-entry-past-cdend.zip` (issue #1885, fires the `entryEnd > cdEnd` CD-parse guard before the LH read): together the trio pins all three precedence levels of the local-offset → local-header validation chain at CD-parse + late-extract — the late LH-signature guard is the defense-in-depth catch, and this fixture pins that catch behaviour so future refactors of `Archive.extract` cannot silently lose the guard) | #1903 | other (LH signature regression) |
| [testdata/zip/malformed/cd-bad-method-early.zip](/home/kim/lean-zip/testdata/zip/malformed/cd-bad-method-early.zip) | 122 B | CD-entry compression-method allowlist check at [Zip/Archive.lean:668](/home/kim/lean-zip/Zip/Archive.lean:668) — *"unsupported compression method"* (CD/LH both advertise method=6 (imploded — deprecated in PKZIP 2.0, 1993), outside lean-zip's `{0, 8}` allowlist; `parseCentralDir` rejects at CD parse time, pre-ZIP64-resolution, before any LH read. Companion to `bad-method.zip` (CD/LH method=14, LZMA): both fixtures trip the same CD-parse guard, but distinct method values let paired-review distinguish which fixture fired) | #1801 | other (method validation) |
| [testdata/zip/malformed/cd-deflate-zero-compsize.zip](/home/kim/lean-zip/testdata/zip/malformed/cd-deflate-zero-compsize.zip) | 116 B | CD-entry `uncompSize > 0 → compSize > 0` math-invariant check at [Zip/Archive.lean:854](/home/kim/lean-zip/Zip/Archive.lean:854) — *"CD entry has zero compressedSize with nonzero uncompressedSize"* (CD and LH both advertise `method=8` (deflate) with `compressedSize=0` and `uncompressedSize=42`. APPNOTE §4.4.8 / §4.4.9 define the size fields; every ZIP compression method produces at least one compressed byte from non-empty uncompressed input — method 0 (APPNOTE §4.4.5) has `compSize == uncompSize`; method 8 (RFC 1951) has a 2-byte minimum block-header encoding (`03 00` empty-stored-block), so any non-empty inflate output requires at minimum a block header plus encoded data. Therefore `compSize == 0 ∧ uncompSize > 0` is structurally impossible regardless of method — a universal mathematical invariant every correct writer (Info-ZIP, Go `archive/zip`, CPython `zipfile`, 7-Zip, lean-zip's own `create`) obeys. `parseCentralDir` rejects at CD parse time, post-ZIP64-resolution, after the stored-method size invariant (`cd-stored-size-mismatch.zip`, PR #1773) and the empty-entry CRC invariant (`cd-empty-entry-crc-nonzero.zip`, PR #1857). Pre-PR, PR #1773's method=0 gate skipped this entry (its `compSize == uncompSize` check is method-gated); PR #1857's `uncompSize == 0` gate skipped this entry (since `uncompSize = 42 > 0`). `Archive.list` propagated `{method = 8, compSize = 0, uncompSize = 42, ...}` verbatim — callers routing on `entry.compressedSize == 0` as a short-circuit saw smuggled values — and `Archive.extract` failed only later inside the inflate backend (`Zlib.decompress` / `Gzip.decompress` / `Zip.Native.Inflate.inflate`) with a decompression error whose attribution did not pin the structural anomaly. Sibling of PR #1773 and PR #1857 at the CD-parse mathematical-invariant family — three contiguous columns: #1773 closes `compSize == uncompSize` (tautological for stored, method=0 only); #1857 closes `uncompSize == 0 → crc == 0` (tautological for empty entries, method-agnostic); PR #1886 closes `uncompSize > 0 → compSize > 0` (structurally required under any compression method, method-agnostic). LH and CD fields match byte-for-byte (method / sizes / crc / version / flags) so no CD/LH skew guard fires first; CRC is `0` so PR #1857 does not interact. Interop pre-flight over `testdata/zip/{interop,malformed,security}/*.zip` returned zero hits before landing) | #1886 | other (math invariant / method-agnostic) |
| [testdata/zip/malformed/cd-empty-entry-crc-nonzero.zip](/home/kim/lean-zip/testdata/zip/malformed/cd-empty-entry-crc-nonzero.zip) | 116 B | CD-entry empty-entry CRC invariant check at [Zip/Archive.lean:794](/home/kim/lean-zip/Zip/Archive.lean:794) — *"CD entry CRC must be zero when uncompressedSize is zero"* (CD and LH both advertise a zero-byte stored entry (`method=0, compSize=0, uncompSize=0`) but carry a crafted nonzero CRC (`0xDEADBEEF`). APPNOTE §4.4.7 defines the CRC32 field as the ANSI-CRC-32 of the uncompressed payload; the empty byte string has CRC32 `0x00000000` by the CRC-32 start-state `0xFFFFFFFF` + final-complement identity, so `uncompSize == 0 → crc == 0` is a universal mathematical invariant that every correct writer — Info-ZIP, Go `archive/zip`, CPython `zipfile`, 7-Zip, lean-zip's own `create` — obeys. `parseCentralDir` rejects at CD parse time post-ZIP64-resolution, after the stored-method size invariant — so the resolved `uncompSize : UInt64` is the value checked rather than the `0xFFFFFFFF` sentinel, and attribution pins on the empty-file premise rather than a generic CRC check. LH and CD carry the same crafted CRC so the CD/LH `crc32` consistency check (`cd-lh-crc-mismatch.zip`, PR #1728) does not fire first; `compSize == uncompSize == 0` so the stored-method size invariant (`cd-stored-size-mismatch.zip`, PR #1773) does not fire first. Closes both `Archive.list` (pre-PR propagated the crafted CRC into `Entry.crc32` verbatim — callers routing on `entry.crc32` saw the smuggled value) and `Archive.extract` (pre-PR caught the mismatch only post-extraction via the `"CRC32 mismatch"` guard at [Zip/Archive.lean:1088](/home/kim/lean-zip/Zip/Archive.lean:1088), after any I/O work had been performed) dimensions simultaneously. Sibling of PR #1773 at the CD-parse mathematical-invariant family — #1773 closes the `compSize == uncompSize` column (tautological for stored), PR #1857 closes the `uncompSize == 0 → crc == 0` column (tautological for empty entries, method-agnostic)) | #1857 | other (CRC/empty-file invariant) |
| [testdata/zip/malformed/cd-empty-name.zip](/home/kim/lean-zip/testdata/zip/malformed/cd-empty-name.zip) | 104 B | CD-entry empty-filename rejection at [Zip/Archive.lean:578](/home/kim/lean-zip/Zip/Archive.lean:578) — *"CD entry has empty filename"* (CD and LH entries both carry `name_bytes=b""`, so the `name length` UInt16 at CD +28 — APPNOTE §4.4.10 — reads as `0`. `parseCentralDir` rejects at CD parse time immediately after the `nameLen` read, before the `entryEnd > cdEnd` overrun check and before the sibling NUL-byte / path-safety filename guards — so the failure attribution pins cleanly to the structural anomaly rather than the path-safety predicate (which would otherwise catch the empty string via its empty-component rejection, but only if the decode succeeds). Every legitimate ZIP entry has at least one byte of name; `nameLen == 0` is structurally pathological and a parser-differential smuggling vector (lenient readers emit `entry.path = ""` — an `Entry` with no useful identity; `Archive.extract` would resolve `outDir / ""` to either `outDir` itself or a path with a trailing separator, surfacing as an unrelated `IO.FS.writeBinFile` / `createDir` error). Sibling of `cd-nul-in-name.zip` (PR #1831, byte-content dimension) and `cd-path-unsafe.zip` (PR #1840, path-shape dimension): together they close the smuggled-name attack class at CD parse — zero-length, NUL-embedded, and path-traversal forms all rejected pre-decode. Interop pre-flight over `testdata/zip/{interop,malformed}/*.zip` returned zero hits before landing) | #1848 | other (filename validation) |
| [testdata/zip/malformed/cd-entry-disknum-mismatch.zip](/home/kim/lean-zip/testdata/zip/malformed/cd-entry-disknum-mismatch.zip) | 122 B | CD per-entry `diskNumberStart` consistency check at [Zip/Archive.lean:549](/home/kim/lean-zip/Zip/Archive.lean:549) — *"CD entry diskNumberStart mismatch"* (CD entry's APPNOTE §4.4.11 disk-number field at offset +34 is `7`; lean-zip supports single-disk archives only, so any nonzero value is rejected. Per-entry counterpart to `eocd-disknum-mismatch.zip` which covers the archive-level EOCD disk-number fields) | #1759 | other (CD/EOCD consistency) |
| [testdata/zip/malformed/cd-entry-internal-attrs-reserved.zip](/home/kim/lean-zip/testdata/zip/malformed/cd-entry-internal-attrs-reserved.zip) | 122 B | CD per-entry `internalFileAttributes` reserved-bits check at [Zip/Archive.lean:567](/home/kim/lean-zip/Zip/Archive.lean:567) — *"internalAttrs reserved bits set"* (CD entry's APPNOTE §4.4.10 field at offset +36 carries `0x0080` — bit 7 set, reserved; only bit 0 "apparent ASCII/text data" is defined in version 1.0, bits 1-2 are PKWARE-reserved, bits 3-15 unused. Guard `internalAttrs &&& 0xFFFE == 0` preserves Info-ZIP bit-0 interop while rejecting smuggled reserved-bit values. Contiguous writer-zero `UInt16` sibling of `cd-entry-disknum-mismatch.zip` (CD +34): `parseCentralDir` reads both fields in order and both guards fire pre-ZIP64-resolution, before the `entryEnd > cdEnd` span check) | #1819 | other (CD writer-invariant) |
| [testdata/zip/malformed/cd-entry-localoffset-past-cdstart.zip](/home/kim/lean-zip/testdata/zip/malformed/cd-entry-localoffset-past-cdstart.zip) | 122 B | CD-entry `localOffset + 30 ≤ cdOffset` archive-layout invariant check at [Zip/Archive.lean:728](/home/kim/lean-zip/Zip/Archive.lean:728) — *"entry local offset overlaps central directory"* (LH+data at file offset 0 length 45, CD starts at offset 45, and the CD entry's `localOffset` field at CD +42 claims `50` — past `cdOffset - 30 = 15`, so the 30-byte fixed LH header cannot be read strictly before the CD region as APPNOTE §4.3.6 requires. Per-entry micro-shape sibling of the archive-level `cdOffset + cdSize ≤ eocdPos` macro-shape guard; pre-PR `Archive.list` had no gate at all, and only the extract path's late LH-signature check caught a subset of the construction) | #1813 | other (archive-layout invariant) |
| [testdata/zip/malformed/cd-entry-past-cdend.zip](/home/kim/lean-zip/testdata/zip/malformed/cd-entry-past-cdend.zip) | 122 B | Per-entry `entryEnd > cdEnd` footprint guard regression coverage at [Zip/Archive.lean:615](/home/kim/lean-zip/Zip/Archive.lean:615) — *"central directory entry extends past end of central directory"* (122-byte single-entry stored `hello.txt` archive — LH at file offset 0, CD at offset 45, EOCD at offset 100 — where the sole CD entry's `commentLen` field at CD +32 (UInt16) is `16` while no comment payload is physically present, so `cdSize = 55` (header + name only). At parse time `entryEnd = 45 + 46 + 9 + 0 + 16 = 116 > cdEnd = 100`, firing the per-entry footprint guard before any name decode. All earlier CD-parse guards pass (loop entry `pos + 46 ≤ cdEnd` (91 ≤ 100), CD signature match, `nameLen = 9 > 0`, `diskNumberStart = 0`, `internalAttrs = 0`) so attribution pins to the footprint guard rather than a sibling early-reject. Fixture-only regression coverage (no new guard code, no new error wording, no caller / signature change) — pattern matches PRs #1761 / #1889 (`zip64-eocd64-bad-recsize.zip` / `zip64-eocd64-v2-record.zip`) and #1903 (`cd-bad-lh-signature.zip`). Companion to in-flight `cd-trailing-garbage.zip` (issue #1775, trailing bytes inside `[lastEntryEnd, cdEnd)`) and `cd-extends-past-eocd.zip` (issue #1799, archive-level `cdOffset + cdSize ≤ eocdPos`) — together the trio closes the three CD-region overrun shapes. Pins the paired-review precedence chain alongside `cd-entry-localoffset-past-cdstart.zip` (PR #1813) and `cd-bad-lh-signature.zip` (PR #1903) so future refactors of `parseCentralDir` cannot silently regress the per-entry footprint fence. Sentinel `commentLen = 16` is canonical "obviously crafted" overrun — any positive value satisfying `46 + nameLen + extraLen + commentLen > cdSize` fires the same guard) | #1921 | other (CD-region overrun regression) |
| [testdata/zip/malformed/cd-extra-overrun-datasize.zip](/home/kim/lean-zip/testdata/zip/malformed/cd-extra-overrun-datasize.zip) | 138 B | CD/LH extra-data sub-field structural check at [Zip/Archive.lean:690](/home/kim/lean-zip/Zip/Archive.lean:690) — *"malformed extra field"* (CD/LH extra-data carries a single sub-field with `headerId=0x5455` extended-timestamp but declared `dataSize=0xFF` while only 4 payload bytes remain; no ZIP64 sentinel is set so pre-PR `parseCentralDir` skipped `parseZip64Extra` entirely and the anomaly was entirely invisible. `validateExtraFieldStructure` runs unconditionally on the extra-data blob before the sentinel guard at both the CD and LH sites (mirror assertion at [Zip/Archive.lean:1006](/home/kim/lean-zip/Zip/Archive.lean:1006) — *"malformed local extra field"*). Outer-sub-field sibling of `zip64-extra-oversized-datasize.zip` at the inner-0x0001 layer of the same APPNOTE §4.5 extra-data smuggling class) | #1788 | other (ZIP64 consistency) |
| [testdata/zip/malformed/cd-lh-crc-mismatch.zip](/home/kim/lean-zip/testdata/zip/malformed/cd-lh-crc-mismatch.zip) | 122 B | CD/LH `crc32` consistency check at [Zip/Archive.lean:1178](/home/kim/lean-zip/Zip/Archive.lean:1178) — *"crc32 mismatch between CD and local header"* (LH crc differs from CD; both stored, sizes match so earlier guards do not fire first) | #1728 | other (CD/LH consistency) |
| [testdata/zip/malformed/cd-lh-flags-mismatch.zip](/home/kim/lean-zip/testdata/zip/malformed/cd-lh-flags-mismatch.zip) | 122 B | CD/LH flags-consistency check (bit-3-masked) at [Zip/Archive.lean:1147](/home/kim/lean-zip/Zip/Archive.lean:1147) — *"flags mismatch between CD and local header"* (CD sets bit 11 UTF-8-name, LH clears it — a known ZIP-smuggling vector) | #1715 | other (CD/LH consistency) |
| [testdata/zip/malformed/cd-lh-method-mismatch.zip](/home/kim/lean-zip/testdata/zip/malformed/cd-lh-method-mismatch.zip) | 122 B | CD/LH method-consistency check at [Zip/Archive.lean:1138](/home/kim/lean-zip/Zip/Archive.lean:1138) — *"method mismatch between CD and local header"* | #1554 | other (CD/LH consistency) |
| [testdata/zip/malformed/cd-lh-modtime-mismatch.zip](/home/kim/lean-zip/testdata/zip/malformed/cd-lh-modtime-mismatch.zip) | 122 B | CD/LH `lastModTime`/`lastModDate` consistency check at [Zip/Archive.lean:1167](/home/kim/lean-zip/Zip/Archive.lean:1167) — *"lastModTime/Date mismatch between CD and local header"* (LH time `0x1234` disagrees with CD time `0`; the two DOS-encoded `UInt16` slots — LH +10/+12, CD +12/+14 — are compared together and the check is ungated since APPNOTE §4.4.6 restricts the bit-3 data-descriptor allowance to crc/compSize/uncompSize only) | #1769 | other (CD/LH consistency) |
| [testdata/zip/malformed/cd-lh-size-mismatch.zip](/home/kim/lean-zip/testdata/zip/malformed/cd-lh-size-mismatch.zip) | 122 B | CD/LH `compressedSize` consistency check at [Zip/Archive.lean:1172](/home/kim/lean-zip/Zip/Archive.lean:1172) — *"compressedSize mismatch between CD and local header"* | #1554 | other (CD/LH consistency) |
| [testdata/zip/malformed/cd-lh-uncompsize-mismatch.zip](/home/kim/lean-zip/testdata/zip/malformed/cd-lh-uncompsize-mismatch.zip) | 122 B | CD/LH `uncompressedSize` consistency check at [Zip/Archive.lean:1175](/home/kim/lean-zip/Zip/Archive.lean:1175) — *"uncompressedSize mismatch between CD and local header"* (LH uncomp differs from CD; both stored, compressed sizes match so earlier guards do not fire first) | #1728 | other (CD/LH consistency) |
| [testdata/zip/malformed/cd-lh-version-mismatch.zip](/home/kim/lean-zip/testdata/zip/malformed/cd-lh-version-mismatch.zip) | 122 B | CD/LH `versionNeededToExtract` downgrade check at [Zip/Archive.lean:1157](/home/kim/lean-zip/Zip/Archive.lean:1157) — *"LH versionNeededToExtract (…) exceeds CD versionNeededToExtract (…)"* (LH claims higher version than CD — a capability-smuggle; CD > LH is legitimate per Go/Python ZIP64 producers and is allowed) | #1736 | other (CD/LH consistency) |
| [testdata/zip/malformed/cd-nul-in-name.zip](/home/kim/lean-zip/testdata/zip/malformed/cd-nul-in-name.zip) | 118 B | CD-entry name NUL-byte rejection at [Zip/Archive.lean:589](/home/kim/lean-zip/Zip/Archive.lean:589) — *"CD entry name contains NUL byte"* (CD and LH entries both carry raw name bytes `b"a\x00b.txt"` — 7 bytes, NUL at index 1. `parseCentralDir` guards on the raw `ByteArray` before the UTF-8 decode, so neither the UTF-8-flagged branch nor the Latin-1 fallback re-introduces NUL into the error message or the decoded `path`. Closes a classic parser-differential / filesystem-truncation smuggling vector: POSIX `open`/`stat` truncates at NUL so `Archive.extract` would deposit files at the short-form prefix, while `Archive.list` callers routing on `entry.path` see the full NUL-embedded string. Interop pre-flight over `testdata/zip/{interop,malformed}/*.zip` returned zero hits before landing) | #1831 | other (filename validation) |
| [testdata/zip/malformed/cd-path-unsafe.zip](/home/kim/lean-zip/testdata/zip/malformed/cd-path-unsafe.zip) | 126 B | CD-entry path-safety rejection at [Zip/Archive.lean:631](/home/kim/lean-zip/Zip/Archive.lean:631) — *"CD entry has unsafe path"* (CD and LH entries both carry raw name bytes `b"../evil.txt"` — 11 bytes, a canonical archive-slip `..`-traversal smuggle. `parseCentralDir` runs `Binary.isPathSafe` on the decoded `name` String immediately after the UTF-8 / Latin-1 decode block and before the `versionNeeded` upper-bound check, mirroring the trailing-slash carve-out from the extract-time check so legitimate directory entries (which end in `/`) are not tripped. Closes the path-traversal / archive-slip smuggling dimension on the `Archive.list` path, which pre-PR returned the `Entry` with the unsafe path verbatim — exposing the full smuggled form to callers that route on `entry.path` before any filesystem I/O. Extract-time `Binary.isPathSafe` calls at [Zip/Archive.lean:1133](/home/kim/lean-zip/Zip/Archive.lean:1133) / :1107 remain as defense-in-depth. Quotes the smuggled name via `String.quote` so control bytes never reach logs unescaped. Sibling of `cd-nul-in-name.zip` (PR #1831): together they close the smuggled-name attack class — NUL-byte content (PR #1831) and path-shape (PR #1840). Interop pre-flight over `testdata/zip/{interop,malformed}/*.zip` returned zero hits before landing; the three `testdata/zip/security/` counter-fixtures (`zip-slip.zip`, `absolute-path.zip`, `backslash-slip.zip`) continue to pass via substring matching — their `unsafe path` assertion is a substring of the new `CD entry has unsafe path` wording) | #1840 | archive-slip |
| [testdata/zip/malformed/cd-past-eof.zip](/home/kim/lean-zip/testdata/zip/malformed/cd-past-eof.zip) | 22 B | `cdOffset + cdSize ≤ fileSize` check at [Zip/Archive.lean:946](/home/kim/lean-zip/Zip/Archive.lean:946) — *"central directory extends beyond file"* | `481e562` | oversized allocation |
| [testdata/zip/malformed/cd-patched-data-flag.zip](/home/kim/lean-zip/testdata/zip/malformed/cd-patched-data-flag.zip) | 122 B | CD-entry general-purpose flag bit-5 (compressed patched data) rejection at [Zip/Archive.lean:682](/home/kim/lean-zip/Zip/Archive.lean:682) — *"patched-data flag bit 5 set"* (CD and LH both advertise `flags = 0x0020`, APPNOTE §4.4.4 bit 5 — PKWARE's proprietary compressed-patched-data format §4.6; lean-zip implements neither creation nor extraction, the writer emits `flags = 0x0800` bit 11 UTF-8 names only. `parseCentralDir` rejects at CD parse time pre-ZIP64-resolution, closing a parser-differential smuggling vector where crafted archives with bit 5 set would otherwise be silently extracted as if the payload were plain Deflate/stored data. Sibling of in-flight PR #1771 (issue #1762, encryption-related bits 0/6/13) at the same CD+8 `flags` field — distinct bit, distinct error substring) | #1824 | other (flag-bit validation) |
| [testdata/zip/malformed/cd-stored-size-mismatch.zip](/home/kim/lean-zip/testdata/zip/malformed/cd-stored-size-mismatch.zip) | 122 B | CD-entry stored-method size-invariant check at [Zip/Archive.lean:786](/home/kim/lean-zip/Zip/Archive.lean:786) — *"stored-method size mismatch"* (both CD and LH advertise `method=0` with `compressedSize=6, uncompressedSize=7` — no CD/LH divergence, but APPNOTE §4.4.5 *"no compression"* makes `compSize == uncompSize` a tautology. `parseCentralDir` rejects at CD parse time, post-ZIP64-resolution, before any LH read; complements the CD/LH `uncompressedSize` check which catches CD-vs-LH skew) | #1773 | other (CD/LH consistency) |
| [testdata/zip/malformed/cd-zip64-extra-duplicate.zip](/home/kim/lean-zip/testdata/zip/malformed/cd-zip64-extra-duplicate.zip) | 158 B | CD-side duplicate ZIP64 extra-block guard at [Zip/Archive.lean:694](/home/kim/lean-zip/Zip/Archive.lean:694) — *"duplicate ZIP64 extra field"* (CD entry's extra-data carries two `headerId == 0x0001` blocks back-to-back with `uncompSize` payloads `6` and `106`; APPNOTE §4.5 forbids more than one instance of any registered header ID per entry's extra-data, and the layout of each block depends on which standard 32-bit fields are at sentinel — two blocks make the resolved sizes ambiguous. `hasDuplicateZip64Extra` fires before `parseZip64Extra` so the error attributes the fault to the CD side; LH carries a single valid 0x0001 block. Sibling of `lh-zip64-extra-duplicate.zip`, `cd-extra-overrun-datasize.zip`, and `zip64-extra-oversized-datasize.zip` — together they close the ZIP64 extra-field layout-smuggling attack class) | #1793 | other (ZIP64 consistency) |
| [testdata/zip/malformed/eocd-disknum-mismatch.zip](/home/kim/lean-zip/testdata/zip/malformed/eocd-disknum-mismatch.zip) | 122 B | CD-vs-EOCD disk-number consistency check at [Zip/Archive.lean:480](/home/kim/lean-zip/Zip/Archive.lean:480) — *"EOCD disk-number mismatch"* (standard EOCD `diskWhereCDStarts=1`; lean-zip supports single-disk archives only, so any nonzero value in either disk-number field is rejected post-ZIP64-override) | #1742 | other (CD/EOCD consistency) |
| [testdata/zip/malformed/eocd-numentries-mismatch.zip](/home/kim/lean-zip/testdata/zip/malformed/eocd-numentries-mismatch.zip) | 122 B | CD-vs-EOCD `totalEntries` consistency check at [Zip/Archive.lean:759](/home/kim/lean-zip/Zip/Archive.lean:759) — *"EOCD totalEntries mismatch"* (EOCD declares 2 entries, CD has 1 — parser's trailing-signature loop would silently accept the short list without this guard) | #1733 | other (CD/EOCD consistency) |
| [testdata/zip/malformed/eocd-numentries-thisdisk-mismatch.zip](/home/kim/lean-zip/testdata/zip/malformed/eocd-numentries-thisdisk-mismatch.zip) | 122 B | EOCD-internal `numEntriesThisDisk` vs. `totalEntries` consistency check at [Zip/Archive.lean:484](/home/kim/lean-zip/Zip/Archive.lean:484) — *"EOCD numEntriesThisDisk mismatch"* (`numEntriesThisDisk=2`, `totalEntries=1`; single-disk archives must have the sibling EOCD entry-count fields equal, and the writer emits them at the same value) | #1752 | other (CD/EOCD consistency) |
| [testdata/zip/malformed/eocd-zip64-override-cdsize-mismatch.zip](/home/kim/lean-zip/testdata/zip/malformed/eocd-zip64-override-cdsize-mismatch.zip) | 198 B | ZIP64/standard-EOCD override sentinel check — `cdSize` slot at [Zip/Archive.lean:396](/home/kim/lean-zip/Zip/Archive.lean:396) — *"EOCD ZIP64-override mismatch"* (standard-EOCD `cdSize=99`, ZIP64 `cdSize=55`; standard value is neither the APPNOTE §4.3.16 sentinel `0xFFFFFFFF` nor a numeric match with the ZIP64 override. All other override slots remain at their sentinels so the relaxed sentinel arm passes for `cdOffset` (line 399), `totalEntries` (line 402), `numberOfThisDisk` (line 405), `diskWhereCDStarts` (line 408), `numEntriesThisDisk` (line 411), and the `cdSize` sub-check at line 396 is the one that trips. Per-slot sibling of `eocd-zip64-override-nosentinel.zip` (PR #1745, `cdOffset` slot at line 399) at the 6-field EOCD ZIP64-override mismatch family — the per-slot fixtures pin attribution to one specific override-slot guard rather than the family-wide check) | #1900 | other (ZIP64 consistency) |
| [testdata/zip/malformed/eocd-zip64-override-diskcd-mismatch.zip](/home/kim/lean-zip/testdata/zip/malformed/eocd-zip64-override-diskcd-mismatch.zip) | 198 B | ZIP64/standard-EOCD override sentinel check — `diskWhereCDStarts` slot at [Zip/Archive.lean:408](/home/kim/lean-zip/Zip/Archive.lean:408) — *"EOCD ZIP64-override mismatch"* (standard-EOCD `diskWhereCDStarts=99`, ZIP64 `diskWhereCDStarts=0`; standard value is neither the APPNOTE §4.3.16 sentinel `0xFFFF` nor a numeric match with the ZIP64 override. All other override slots remain at their sentinels so the relaxed sentinel arm passes for `cdSize` (line 396), `cdOffset` (line 399), `totalEntries` (line 402), `numberOfThisDisk` (line 405), `numEntriesThisDisk` (line 411), and the `diskWhereCDStarts` sub-check at line 408 is the one that trips. `diskWhereCDStarts` is the cross-disk dispatch dual of the `numberOfThisDisk` smuggling vector: standard EOCD declares "the CD lives on disk N" while the ZIP64 EOCD64 declares "the CD lives on disk M", letting an attacker present two different archives to two different parsers from the same byte sequence. The downstream EOCD-level disk-number sanity check at [Zip/Archive.lean:521](/home/kim/lean-zip/Zip/Archive.lean:521) (`numberOfThisDisk == 0 && diskWhereCDStarts == 0`) cannot be reached when the ZIP64-override sub-check at line 408 fires first; this fixture exercises the upstream override-mismatch arm specifically. Per-slot sibling of `eocd-zip64-override-nosentinel.zip` (PR #1745, `cdOffset` slot at line 399), `eocd-zip64-override-cdsize-mismatch.zip` (PR #1900, `cdSize` slot at line 396), and `eocd-zip64-override-totalentries-mismatch.zip` (PR #1901, `totalEntries` slot at line 402) at the 6-field EOCD ZIP64-override mismatch family — the per-slot fixtures pin attribution to one specific override-slot guard rather than the family-wide check) | #1906 | other (ZIP64 consistency) |
| [testdata/zip/malformed/eocd-zip64-override-entriesthisdisk-mismatch.zip](/home/kim/lean-zip/testdata/zip/malformed/eocd-zip64-override-entriesthisdisk-mismatch.zip) | 198 B | ZIP64/standard-EOCD override sentinel check — `numEntriesThisDisk` slot at [Zip/Archive.lean:411](/home/kim/lean-zip/Zip/Archive.lean:411) — *"EOCD ZIP64-override mismatch"* (standard-EOCD `numEntriesThisDisk=99`, ZIP64 `numEntriesThisDisk=1`; standard value is neither the APPNOTE §4.3.16 sentinel `0xFFFF` nor a numeric match with the ZIP64 override. All other override slots remain at their sentinels so the relaxed sentinel arm passes for `cdSize` (line 396), `cdOffset` (line 399), `totalEntries` (line 402), `numberOfThisDisk` (line 405), `diskWhereCDStarts` (line 408), and the `numEntriesThisDisk` sub-check at line 411 is the one that trips. Distinct from the EOCD-internal `numEntriesThisDisk` vs. `totalEntries` consistency guard exercised by `eocd-numentries-thisdisk-mismatch.zip` (PR #1752): the same field name appears in two distinct guards — the override-arm at line 411 compares the standard EOCD against the ZIP64 record, the internal-consistency arm at [Zip/Archive.lean:531](/home/kim/lean-zip/Zip/Archive.lean:531) compares the post-override resolved values — and this fixture pins the override-arm specifically. The standard EOCD's `totalEntries` stays at the `0xFFFF` sentinel so the line-402 override sub-check passes on its sentinel branch *before* line-411 is reached; the downstream EOCD-internal consistency check is unreachable because the override sub-check fires first. Per-slot sibling of `eocd-zip64-override-nosentinel.zip` (PR #1745, `cdOffset` slot at line 399), `eocd-zip64-override-cdsize-mismatch.zip` (PR #1905, `cdSize` slot at line 396), `eocd-zip64-override-totalentries-mismatch.zip` (PR #1908, `totalEntries` slot at line 402), and `eocd-zip64-override-diskcd-mismatch.zip` (PR #1911, `diskWhereCDStarts` slot at line 408) at the 6-field EOCD ZIP64-override mismatch family — the per-slot fixtures pin attribution to one specific override-slot guard rather than the family-wide check) | #1907 | other (ZIP64 consistency) |
| [testdata/zip/malformed/eocd-zip64-override-totalentries-mismatch.zip](/home/kim/lean-zip/testdata/zip/malformed/eocd-zip64-override-totalentries-mismatch.zip) | 198 B | ZIP64/standard-EOCD override sentinel check — `totalEntries` slot at [Zip/Archive.lean:402](/home/kim/lean-zip/Zip/Archive.lean:402) — *"EOCD ZIP64-override mismatch"* (standard-EOCD `totalEntries=99`, ZIP64 `totalEntries=1`; standard value is neither the APPNOTE §4.3.16 sentinel `0xFFFF` nor a numeric match with the ZIP64 override. All other override slots remain at their sentinels so the relaxed sentinel arm passes for `cdSize` (line 396), `cdOffset` (line 399), `numberOfThisDisk` (line 405), `diskWhereCDStarts` (line 408), `numEntriesThisDisk` (line 411), and the `totalEntries` sub-check at line 402 is the one that trips. `totalEntries` is a particularly notable smuggling vector because it controls the entry-iteration loop of the CD walker — a relaxed reader that trusts a smuggled value walks more or fewer CD entries than the strict reader, opening entry-injection / entry-hiding attacks. Per-slot sibling of `eocd-zip64-override-nosentinel.zip` (PR #1745, `cdOffset` slot at line 399) and `eocd-zip64-override-cdsize-mismatch.zip` (PR #1900, `cdSize` slot at line 396) at the 6-field EOCD ZIP64-override mismatch family — the per-slot fixtures pin attribution to one specific override-slot guard rather than the family-wide check) | #1901 | other (ZIP64 consistency) |
| [testdata/zip/malformed/eocd-zip64-override-nosentinel.zip](/home/kim/lean-zip/testdata/zip/malformed/eocd-zip64-override-nosentinel.zip) | 198 B | ZIP64/standard-EOCD override sentinel check at [Zip/Archive.lean:355](/home/kim/lean-zip/Zip/Archive.lean:355) — *"EOCD ZIP64-override mismatch"* (standard-EOCD `cdOffset=42`, ZIP64 `cdOffset=45`; standard value is neither the APPNOTE §4.3.16 sentinel `0xFFFFFFFF` nor a numeric match with the ZIP64 override — a parser-differential smuggling vector) | #1745 | other (ZIP64 consistency) |
| [testdata/zip/malformed/invalid-utf8-with-flag.zip](/home/kim/lean-zip/testdata/zip/malformed/invalid-utf8-with-flag.zip) | 120 B | UTF-8-flagged entry name strict parse at [Zip/Archive.lean:595](/home/kim/lean-zip/Zip/Archive.lean:595) — *"invalid UTF-8 in entry name (UTF-8 flag set)"* | `481e562` | partial-decoder panic |
| [testdata/zip/malformed/lh-zip64-extra-duplicate.zip](/home/kim/lean-zip/testdata/zip/malformed/lh-zip64-extra-duplicate.zip) | 158 B | LH-side duplicate ZIP64 extra-block guard at [Zip/Archive.lean:1013](/home/kim/lean-zip/Zip/Archive.lean:1013) — *"duplicate ZIP64 local extra field"* (CD entry has a single valid `headerId == 0x0001` block so CD parse passes; LH carries two 0x0001 blocks with `uncompSize` payloads `6` and `106`. `hasDuplicateZip64Extra` fires inside `readEntryData` before any CD/LH consistency check. Sibling of `cd-zip64-extra-duplicate.zip` — the two distinct error wordings keep attribution between the parse layers loud under future refactors) | #1793 | other (ZIP64 consistency) |
| [testdata/zip/malformed/no-eocd.zip](/home/kim/lean-zip/testdata/zip/malformed/no-eocd.zip) | 44 B | EOCD-scan failure at [Zip/Archive.lean:1056](/home/kim/lean-zip/Zip/Archive.lean:1056) — *"cannot find end of central directory"* | `481e562` | other (framing) |
| [testdata/zip/malformed/oversized-compressed-size.zip](/home/kim/lean-zip/testdata/zip/malformed/oversized-compressed-size.zip) | 122 B | CD-entry stored-method size-invariant check at [Zip/Archive.lean:786](/home/kim/lean-zip/Zip/Archive.lean:786) — *"stored-method size mismatch"* (CD/LH both advertise method=0 with compSize=2 MiB and uncompSize=6; `parseCentralDir` rejects post-ZIP64-resolution before any LH read. Previously caught by the later `local data span` check in `readEntryData` — PR #1773's CD-parse guard fires first, kept in-corpus for regression coverage at the earlier layer) | #1497 | oversized allocation |
| [testdata/zip/malformed/oversized-zip64-compressed-size.zip](/home/kim/lean-zip/testdata/zip/malformed/oversized-zip64-compressed-size.zip) | 134 B | CD-entry stored-method size-invariant check at [Zip/Archive.lean:786](/home/kim/lean-zip/Zip/Archive.lean:786) — *"stored-method size mismatch"* (ZIP64 extra resolves compSize=1<<60, uncompSize=6 with method=0; `parseCentralDir` rejects post-ZIP64-resolution before any LH read. Previously caught by the later `local data span` check in `readEntryData` — PR #1773's CD-parse guard fires first, kept in-corpus for regression coverage at the earlier layer) | #1543 | oversized allocation |
| [testdata/zip/malformed/oversized-zip64-uncompressed-size.zip](/home/kim/lean-zip/testdata/zip/malformed/oversized-zip64-uncompressed-size.zip) | 134 B | CD-entry stored-method size-invariant check at [Zip/Archive.lean:786](/home/kim/lean-zip/Zip/Archive.lean:786) — *"stored-method size mismatch"* (ZIP64 extra resolves compSize=6, uncompSize=1<<60 with method=0; `parseCentralDir` rejects post-ZIP64-resolution before any LH read. Previously caught by the LH ZIP64 truncation check in `readEntryData` — PR #1773's CD-parse guard fires first, kept in-corpus for regression coverage at the earlier layer) | #1544 | oversized allocation |
| [testdata/zip/malformed/too-short.zip](/home/kim/lean-zip/testdata/zip/malformed/too-short.zip) | 10 B | EOCD-scan failure at [Zip/Archive.lean:1056](/home/kim/lean-zip/Zip/Archive.lean:1056) — *"cannot find end of central directory"* | `481e562` | other (framing) |
| [testdata/zip/malformed/zip64-eocd64-bad-recsize.zip](/home/kim/lean-zip/testdata/zip/malformed/zip64-eocd64-bad-recsize.zip) | 198 B | ZIP64 EOCD64 self-declared record-size check at [Zip/Archive.lean:345](/home/kim/lean-zip/Zip/Archive.lean:345) — *"ZIP64 EOCD64 record-size mismatch"* (EOCD64 `size of this record` field at `bufPos + 4` carries `0` instead of the required `44` for a v1 EOCD64; lean-zip reads the record at fixed per-field offsets from a hard-coded 56-byte layout, while a stricter parser that trusts the self-declared length would read past or short of that — a parser-differential smuggling vector) | #1761 | other (ZIP64 consistency) |
| [testdata/zip/malformed/zip64-eocd64-v2-record.zip](/home/kim/lean-zip/testdata/zip/malformed/zip64-eocd64-v2-record.zip) | 214 B | ZIP64 EOCD64 self-declared record-size check at [Zip/Archive.lean:345](/home/kim/lean-zip/Zip/Archive.lean:345) — *"ZIP64 EOCD64 record-size mismatch"* (EOCD64 `size of this record` field at `bufPos + 4` carries `60` — the APPNOTE §4.3.14.2 v2 shape with a 16-byte "zip64 extensible data sector" for strong-encryption (SES) fields `compositeSize` + `encryptionAlgID`, making the declared body `56 + 16 - 12 = 60` bytes; the physical record is internally consistent at `4 + 8 + 60 = 72` bytes, so a reader that trusts the declared length and parses per APPNOTE v2 semantics would accept the archive. lean-zip does not implement strong encryption, so v2 records remain rejected by policy — sibling of `zip64-eocd64-bad-recsize.zip` at the specific APPNOTE-documented v2-record angle, pinning the rejection behaviour against the v2 shape rather than a generic `recSize ≠ 44` boundary) | #1889 | other (ZIP64 consistency) |
| [testdata/zip/malformed/zip64-eocd64-versionmadeby-too-high.zip](/home/kim/lean-zip/testdata/zip/malformed/zip64-eocd64-versionmadeby-too-high.zip) | 198 B | ZIP64 EOCD64 `versionMadeBy` lower-byte upper-bound check at [Zip/Archive.lean:363](/home/kim/lean-zip/Zip/Archive.lean:363) — *"ZIP64 EOCD64 versionMadeBy spec-version byte too high"* (EOCD64 `versionMadeBy` field at `bufPos + 12` carries `0x0340` — low byte `0x40 = 64`, one past the APPNOTE §4.4.2.2 cap of `63` (spec version 6.3); archive-level counterpart to the per-entry CD+4 `versionMadeBy` fixture, closing the `versionMadeBy` upper-bound dimension across both ZIP layers) | #1826 | other (ZIP64 consistency) |
| [testdata/zip/malformed/zip64-eocd64-versionneeded-too-high.zip](/home/kim/lean-zip/testdata/zip/malformed/zip64-eocd64-versionneeded-too-high.zip) | 198 B | ZIP64 EOCD64 `versionNeededToExtract` upper-bound check at [Zip/Archive.lean:380](/home/kim/lean-zip/Zip/Archive.lean:380) — *"ZIP64 EOCD64 versionNeededToExtract too high"* (EOCD64 `versionNeededToExtract` field at `bufPos + 14` carries `0x00FF` — spec version 25.5, well above the APPNOTE §4.4.3.2 cap of `63` (spec version 6.3); upper-bound sibling of the lower-bound `≥ 45` check (issue #1758 / PR #1764), together closing the EOCD64 `versionNeededToExtract` two-sided-bound dimension. Archive-level analog of the per-entry CD+6 upper bound (PR #1807, `cd-version-needed-too-high.zip`); the archive-level cap is `63` (not `45`) because APPNOTE §4.4.3.2 documents the EOCD64 field as the version needed to interpret the record rather than to extract the largest entry) | #1852 | other (ZIP64 consistency) |
| [testdata/zip/malformed/zip64-extra-oversized-datasize.zip](/home/kim/lean-zip/testdata/zip/malformed/zip64-extra-oversized-datasize.zip) | 162 B | ZIP64 extra-field `dataSize` exactness check at [Zip/Archive.lean:697](/home/kim/lean-zip/Zip/Archive.lean:697) — *"malformed ZIP64 extra field"* (CD entry's ZIP64 extra `dataSize=16` claims two 8-byte slots while only `stdCompSize` is the sentinel, so APPNOTE §4.5.3 requires exactly `8 * 1 = 8` bytes; the trailing 8 bytes `0xDEADBEEFCAFEBABE` are attacker-chosen slack that a lenient parser silently discards. `parseZip64Extra` enforces `fpos == fieldEnd` after the three conditional reads — sibling of `zip64-eocd64-bad-recsize.zip` at a different layer of the same parser-differential attack class) | #1785 | other (ZIP64 consistency) |

## Required Maintenance Rule

Whenever a new parser, extraction path, FFI helper, or streaming API is
added, this file must be updated in the same change set with:

- trust status
- guardrails
- known missing work
- regression references if a bug prompted the change

Run `bash scripts/check-inventory-links.sh` after any change touching
`Zip/**`, `ZipTest/**`, `testdata/**`, or this file, and resolve any
hard-failure errors before merging. The script also emits advisory
warnings when a cited line number may have drifted relative to the
quoted error-substring prose — treat these as hints, not blockers.
