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
    (`testdata/zip/malformed/eocd-zip64-override-nosentinel.zip`)
    rejects archives where the standard EOCD carries a real value
    instead of the APPNOTE §4.3.16 sentinel (`0xFFFFFFFF` / `0xFFFF`)
    in any of `cdSize`/`cdOffset`/`totalEntries`/`numberOfThisDisk`/
    `diskWhereCDStarts`/`numEntriesThisDisk` that the ZIP64 record
    overrides with a numerically different value. The check is relaxed
    to "sentinel or numeric match" to accommodate real-world producers
    such as Go's `archive/zip` that emit real zeros in the standard
    EOCD's disk-number fields when ZIP64 is used (see
    `testdata/zip/interop/go-zip64.zip`). Closes the
    parser-differential smuggling vector where one reader trusts the
    standard EOCD and another trusts the ZIP64 override
  - ZIP64 EOCD64 self-declared record-size check — PR #1761
    (`testdata/zip/malformed/zip64-eocd64-bad-recsize.zip`) rejects
    archives whose EOCD64 `size of this record` field (APPNOTE §4.3.14,
    at `bufPos + 4`) is not exactly `44` — the v1 EOCD64 shape lean-zip
    produces and consumes. lean-zip reads the EOCD64 at fixed per-field
    offsets from a hard-coded 56-byte layout; a stricter parser that
    trusts the self-declared length would read past or short of that,
    yielding a parser-differential smuggling vector (writer-side at
    [Zip/Archive.lean:142](/home/kim/lean-zip/Zip/Archive.lean:142)
    hard-codes `44`)
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
    conditional reads (Zip/Archive.lean:410). Sibling of the outer
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
    [Zip/Archive.lean:388](/home/kim/lean-zip/Zip/Archive.lean:388)
    walks the TLV structure once and is invoked by both the CD-side
    caller in `parseCentralDir`
    ([Zip/Archive.lean:585](/home/kim/lean-zip/Zip/Archive.lean:585))
    and the LH-side caller in `readEntryData`
    ([Zip/Archive.lean:875](/home/kim/lean-zip/Zip/Archive.lean:875))
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
    [Zip/Archive.lean:868](/home/kim/lean-zip/Zip/Archive.lean:868).
    Net-new dimension observed during the CD-parse guard coverage
    sweep — the *Missing work* block had not previously flagged the
    stored-method invariant
  - CD-entry compression-method allowlist check — PR #1801
    (`testdata/zip/malformed/cd-bad-method-early.zip`) rejects CD
    entries whose `method` field is outside lean-zip's `{0, 8}`
    allowlist (`0` = stored, `8` = deflate) at `parseCentralDir` time
    ([Zip/Archive.lean:572](/home/kim/lean-zip/Zip/Archive.lean:572)),
    before the ZIP64 extra resolution. The check is safe to run
    pre-ZIP64-resolution because `method` is a plain `UInt16` field
    with no sentinel-gating (APPNOTE §4.4.5). Pre-PR, only
    `Archive.extract`'s late `"unsupported method"` dispatch in
    `readEntryData` (`"unsupported method"` throw at [Zip/Archive.lean:975](/home/kim/lean-zip/Zip/Archive.lean:975))
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
    ([Zip/Archive.lean:620](/home/kim/lean-zip/Zip/Archive.lean:620)).
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
    [Zip/Archive.lean:862](/home/kim/lean-zip/Zip/Archive.lean:862))
    caught a subset of the construction (and could be defeated by a
    carefully chosen overlap where the CD bytes happened to match
    `sigLocal`). Uses the asymmetric `SpanInFile`-shaped subtraction
    to avoid `UInt64` wrap on crafted very-large `localOff`. Placed
    after ZIP64 resolution so the resolved `UInt64` `localOff` is
    checked, not the `0xFFFFFFFF` sentinel. Net-new dimension
    observed during the CD-parse archive-layout-invariant coverage
    sweep
  - CD-entry `versionMadeBy` lower-byte upper-bound check — PR #1820
    (`testdata/zip/malformed/cd-entry-versionmadeby-too-high.zip`)
    rejects CD entries whose `versionMadeBy` field at CD +4 carries
    a lower byte greater than `63` (spec version 6.3, APPNOTE 6.3.10)
    at `parseCentralDir` time
    ([Zip/Archive.lean:498](/home/kim/lean-zip/Zip/Archive.lean:498)).
    APPNOTE §4.4.2.2 defines the lower byte as the ZIP spec version in
    decimal-coded form (20 = 2.0, 45 = 4.5, 63 = 6.3); any higher value
    is beyond the defined spec and a parser-differential smuggling
    vector against strict readers. Writer-side at
    [Zip/Archive.lean:116](/home/kim/lean-zip/Zip/Archive.lean:116)
    emits `3 * 256 + (if z64 then 45 else 20)`, so lean-zip-produced
    archives never exceed lower-byte 45. Only the lower byte is
    checked — real archives vary widely in host-OS code (upper byte:
    Info-ZIP emits `3`, Windows producers emit `11` NTFS, Mac
    producers emit `19`/`20` OS/X/darwin, legacy DOS emits `0`); the
    lower byte is a pure spec-version field with a well-defined
    APPNOTE maximum, making the check spec-aligned with negligible
    interop risk. Single-side writer-invariant check (like
    `cd-entry-disknum-mismatch.zip` — PR #1759) since the Local File
    Header has no `versionMadeBy` field (APPNOTE §4.3.7). Companion
    of the CD+6 `versionNeeded ≤ 45` guard (PR #1807,
    `cd-version-needed-too-high.zip`): together the two fixtures pin
    the two version-byte fields at CD+4 and CD+6 to APPNOTE-defined
    ranges, closing the version-byte smuggling dimension. Placed
    before the `versionNeeded` read so CD+4 is attributed before any
    CD+6 anomaly. Net-new dimension observed during the CD-parse
    version-byte coverage sweep; spot-check of
    `testdata/zip/interop/*` confirms every interop fixture's lower
    byte is ≤ 45 (max observed: `go-zip64.zip` at 45)
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

#### Symlink/hardlink extraction policy

`Tar.extract` (in [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean:210))
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

- File: [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean:473)
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
  - [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean:675)
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
| [Archive.list](/home/kim/lean-zip/Zip/Archive.lean:990) | `maxCentralDirSize : Nat` | `67108864` (64 MiB) | no limit | metadata-only; caps CD allocation, not decompressed payload. |
| [Archive.extract](/home/kim/lean-zip/Zip/Archive.lean:1014) | `maxCentralDirSize : Nat` | `67108864` (64 MiB) | no limit | CD allocation cap. |
| [Archive.extract](/home/kim/lean-zip/Zip/Archive.lean:1014) | `maxEntrySize : UInt64` | `1 * 1024^3` (1 GiB) | pass `0` for unlimited (FFI backend only; native inflate rejects `0`) | per-entry cap on the decompressed payload. |
| [Archive.extract](/home/kim/lean-zip/Zip/Archive.lean:1014) | `maxTotalSize : UInt64` | `0` | no whole-archive cap | running sum across all entries; intended as a second line of defence against many-small-entries bombs. |
| [Archive.extractFile](/home/kim/lean-zip/Zip/Archive.lean:1059) | `maxCentralDirSize : Nat` | `67108864` (64 MiB) | no limit | CD allocation cap. |
| [Archive.extractFile](/home/kim/lean-zip/Zip/Archive.lean:1059) | `maxEntrySize : UInt64` | `1 * 1024^3` (1 GiB) | pass `0` for unlimited (FFI backend only; native inflate rejects `0`) | per-entry cap. |
| [Tar.extract](/home/kim/lean-zip/Zip/Tar.lean:651) | `maxEntrySize : UInt64` | `1 * 1024^3` (1 GiB) | pass `0` for unlimited | per-entry byte cap, applied via header `e.size` before any I/O (see [Zip/Tar.lean:651](/home/kim/lean-zip/Zip/Tar.lean:651)). |
| [Tar.extract](/home/kim/lean-zip/Zip/Tar.lean:651) | `maxTotalSize : UInt64` | `0` | no whole-archive cap | running sum across all regular-file entries; directories and symlinks contribute zero. |
| [Tar.extractTarGz](/home/kim/lean-zip/Zip/Tar.lean:779) | `maxEntrySize : UInt64` | `1 * 1024^3` (1 GiB) | pass `0` for unlimited | per-entry cap. Outer gzip decode is streaming via `Gzip.InflateState`; no per-stream output cap. |
| [Tar.extractTarGz](/home/kim/lean-zip/Zip/Tar.lean:779) | `maxTotalSize : UInt64` | `0` | no whole-archive cap | forwarded to inner `Tar.extract`. |
| [Tar.extractTarGzNative](/home/kim/lean-zip/Zip/Tar.lean:848) | `maxEntrySize : UInt64` | `1 * 1024^3` (1 GiB) | pass `0` for unlimited | per-entry cap. |
| [Tar.extractTarGzNative](/home/kim/lean-zip/Zip/Tar.lean:848) | `maxTotalSize : UInt64` | `0` | no whole-archive cap | forwarded to inner `Tar.extract`. |
| [Tar.extractTarGzNative](/home/kim/lean-zip/Zip/Tar.lean:851) | `maxOutputSize : Nat` | `256 * 1024^2` (256 MiB) | hard cap at 0 bytes (explicit) | whole-archive tar-buffer cap for the outer native gzip decode. |

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
`readExact` ([Zip/Archive.lean:761](/home/kim/lean-zip/Zip/Archive.lean:761),
[Zip/Tar.lean:189](/home/kim/lean-zip/Zip/Tar.lean:189)),
`readExactStream` ([Zip/Archive.lean:775](/home/kim/lean-zip/Zip/Archive.lean:775)),
`readEntryData` ([Zip/Tar.lean:220](/home/kim/lean-zip/Zip/Tar.lean:220)),
`skipEntryData` ([Zip/Tar.lean:539](/home/kim/lean-zip/Zip/Tar.lean:539)),
or open-coded read loops. Each row below names the call site that
drives an `n`-byte read; the `readExact`-family helpers themselves
perform a `Nat → USize` roundtrip check before every `Handle.read`.

| Callsite (file:line) | Reads driven by | Local guard | Failure mode if guard absent |
|---|---|---|---|
| [Zip/Archive.lean:775](/home/kim/lean-zip/Zip/Archive.lean:775) `readExactStream` helper (inner `s.read` at line 695) | caller-provided `n : Nat` | `Nat → USize` roundtrip at [Zip/Archive.lean:776](/home/kim/lean-zip/Zip/Archive.lean:776) | no production parser reaches this helper today — only `ZipTest/Archive.lean` exercises it. Any future stream-fed parser that wires into `readExactStream` must apply its own `n`-bound before calling; otherwise this row downgrades to caller-bounded |
| [Zip/Archive.lean:833](/home/kim/lean-zip/Zip/Archive.lean:833) `readExact h tailSize "EOCD tail"` | `tailSize = min fileSize 65558` at [Zip/Archive.lean:830](/home/kim/lean-zip/Zip/Archive.lean:830) | `min` clamp (≤ 65 558 bytes regardless of input); `Nat → USize` roundtrip in `readExact` | N/A — the read is structurally bounded to ≤ 65 558 bytes |
| [Zip/Archive.lean:815](/home/kim/lean-zip/Zip/Archive.lean:815) `readExact h cdSize "central directory"` | `cdSize` parsed from EOCD (attacker-controlled) | `cdOffset + cdSize ≤ fileSize` check at [Zip/Archive.lean:838](/home/kim/lean-zip/Zip/Archive.lean:838); `maxCentralDirSize` cap (default 64 MiB) at [Zip/Archive.lean:811](/home/kim/lean-zip/Zip/Archive.lean:811); `Nat → USize` roundtrip in `readExact` | would request a crafted multi-GB allocation; depends on runtime to reject or OOM |
| [Zip/Archive.lean:859](/home/kim/lean-zip/Zip/Archive.lean:859) `readBoundedSpanFromHandle h fileSize entry.localOffset 30 "local header for {label}"` | fixed `30` bytes | `assertSpanInFile fileSize entry.localOffset 30` internal to `readBoundedSpanFromHandle` at [Zip/Archive.lean:859](/home/kim/lean-zip/Zip/Archive.lean:859) | N/A — fixed 30-byte read |
| [Zip/Archive.lean:887](/home/kim/lean-zip/Zip/Archive.lean:887) `readBoundedSpanFromHandle h fileSize (entry.localOffset + 30) (nameLen + extraLen) "local name+extra for {label}"` | `nameLen + extraLen`, both `UInt16` read from the local header (≤ 2·`UInt16.max` ≈ 128 KiB) | `assertSpanInFile` at [Zip/Archive.lean:887](/home/kim/lean-zip/Zip/Archive.lean:887); `UInt16` type bound on each addend | N/A — `UInt16` type bounds each addend, total ≤ 128 KiB regardless of input |
| [Zip/Archive.lean:931](/home/kim/lean-zip/Zip/Archive.lean:931) `readExact h entry.compressedSize.toNat "compressed data for {label}"` | `entry.compressedSize` from CD / ZIP64 local extra (attacker-controlled `UInt64`) | `assertSpanInFile fileSize (entry.localOffset + headerAndNames) entry.compressedSize` at [Zip/Archive.lean:856](/home/kim/lean-zip/Zip/Archive.lean:856); CD-vs-LH `compressedSize` consistency check at [Zip/Archive.lean:953](/home/kim/lean-zip/Zip/Archive.lean:953) (only skipped when the LH data-descriptor flag bit 3 is set); CD-vs-LH flags-consistency check (bit-3-masked) at [Zip/Archive.lean:928](/home/kim/lean-zip/Zip/Archive.lean:928) — *"flags mismatch between CD and local header"* — rejects mismatched general-purpose flag words before the payload read; CD-vs-LH `versionNeededToExtract` one-sided downgrade check at [Zip/Archive.lean:938](/home/kim/lean-zip/Zip/Archive.lean:938) — *"LH versionNeededToExtract (…) exceeds CD versionNeededToExtract (…)"* — rejects LH claiming a higher version than CD (a capability-smuggle vector) before the payload read; `Nat → USize` roundtrip in `readExact`. Regression fixtures: `testdata/zip/malformed/oversized-compressed-size.zip`, `oversized-zip64-compressed-size.zip`, `cd-lh-flags-mismatch.zip`, `cd-lh-uncompsize-mismatch.zip`, `cd-lh-crc-mismatch.zip`, `cd-lh-version-mismatch.zip` | would request petabyte allocation on a crafted oversized `compressedSize`; relies on `assertSpanInFile` + CD/LH consistency to reject before `Handle.read` |
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
| [testdata/tar/malformed/bad-checksum.tar](/home/kim/lean-zip/testdata/tar/malformed/bad-checksum.tar) | 2048 B | Tar header checksum verification at [Zip/Tar.lean:444](/home/kim/lean-zip/Zip/Tar.lean:444) — *"header checksum mismatch"* | `481e562` | other (integrity check) |
| [testdata/tar/malformed/gnu-longlink-truncated.tar](/home/kim/lean-zip/testdata/tar/malformed/gnu-longlink-truncated.tar) | 612 B | `readEntryData` short-read at [Zip/Tar.lean:230](/home/kim/lean-zip/Zip/Tar.lean:230) — *"unexpected end of archive reading entry data"* | #1546 | partial-decoder panic |
| [testdata/tar/malformed/gnu-longname-invalid-utf8.tar](/home/kim/lean-zip/testdata/tar/malformed/gnu-longname-invalid-utf8.tar) | 1536 B | `String.fromUTF8?` → `Binary.fromLatin1` fallback at [Zip/Tar.lean:575](/home/kim/lean-zip/Zip/Tar.lean:575) (no panicking `fromUTF8!` path) | #1546 | partial-decoder panic |
| [testdata/tar/malformed/gnu-longname-no-terminator.tar](/home/kim/lean-zip/testdata/tar/malformed/gnu-longname-no-terminator.tar) | 1536 B | `stripTrailingNuls` is a no-op when the payload has no trailing NUL ([Zip/Tar.lean:528](/home/kim/lean-zip/Zip/Tar.lean:528)); full payload becomes the name without a panic | #1546 | partial-decoder panic |
| [testdata/tar/malformed/gnu-longname-oversized-size.tar](/home/kim/lean-zip/testdata/tar/malformed/gnu-longname-oversized-size.tar) | 512 B | `readEntryData` `maxHeaderSize` cap at [Zip/Tar.lean:222](/home/kim/lean-zip/Zip/Tar.lean:222) — *"exceeds maximum header size"* (header `size ≈ 8 GiB`, default cap `8 MiB`) | #1597 | oversized allocation |
| [testdata/tar/malformed/gnu-longname-truncated.tar](/home/kim/lean-zip/testdata/tar/malformed/gnu-longname-truncated.tar) | 612 B | `readEntryData` short-read at [Zip/Tar.lean:230](/home/kim/lean-zip/Zip/Tar.lean:230) — *"unexpected end of archive reading entry data"* | #1546 | partial-decoder panic |
| [testdata/tar/malformed/no-magic.tar](/home/kim/lean-zip/testdata/tar/malformed/no-magic.tar) | 2048 B | Tar magic check at [Zip/Tar.lean:448](/home/kim/lean-zip/Zip/Tar.lean:448) — *"unsupported format"* | `481e562` | other (header validation) |
| [testdata/tar/malformed/pax-extended-oversized-size.tar](/home/kim/lean-zip/testdata/tar/malformed/pax-extended-oversized-size.tar) | 512 B | `readEntryData` `maxHeaderSize` cap at [Zip/Tar.lean:222](/home/kim/lean-zip/Zip/Tar.lean:222) — *"exceeds maximum header size"* (PAX header `size ≈ 8 GiB`, default cap `8 MiB`) | #1597 | oversized allocation |
| [testdata/tar/malformed/pax-inconsistent-length.tar](/home/kim/lean-zip/testdata/tar/malformed/pax-inconsistent-length.tar) | 2048 B | `parsePaxRecords` silent-skip when no `=` is found before the declared record end (scan at [Zip/Tar.lean:79](/home/kim/lean-zip/Zip/Tar.lean:79); record dropped at [Zip/Tar.lean:79](/home/kim/lean-zip/Zip/Tar.lean:79)) | #1545 | partial-decoder panic |
| [testdata/tar/malformed/pax-invalid-utf8-key.tar](/home/kim/lean-zip/testdata/tar/malformed/pax-invalid-utf8-key.tar) | 2048 B | `parsePaxRecords` `String.fromUTF8?` guard on key/value at [Zip/Tar.lean:122](/home/kim/lean-zip/Zip/Tar.lean:122) (record dropped, no panic) | #1545 | partial-decoder panic |
| [testdata/tar/malformed/pax-invalid-utf8-value.tar](/home/kim/lean-zip/testdata/tar/malformed/pax-invalid-utf8-value.tar) | 2048 B | Same `String.fromUTF8?` guard at [Zip/Tar.lean:122](/home/kim/lean-zip/Zip/Tar.lean:122) | #1545 | partial-decoder panic |
| [testdata/tar/malformed/pax-oversized-length.tar](/home/kim/lean-zip/testdata/tar/malformed/pax-oversized-length.tar) | 2048 B | `parsePaxRecords` `digitCount > 20` guard at [Zip/Tar.lean:95](/home/kim/lean-zip/Zip/Tar.lean:95) (length-parse aborted before multiplying) | #1545 | oversized allocation |
| [testdata/tar/malformed/pax-truncated-record.tar](/home/kim/lean-zip/testdata/tar/malformed/pax-truncated-record.tar) | 2048 B | `parsePaxRecords` `recordEnd > data.size` guard at [Zip/Tar.lean:105](/home/kim/lean-zip/Zip/Tar.lean:105) (iteration breaks, remaining bytes ignored) | #1545 | partial-decoder panic |
| [testdata/tar/malformed/truncated.tar](/home/kim/lean-zip/testdata/tar/malformed/truncated.tar) | 522 B | `Tar.extract` regular-file loop short-read at [Zip/Tar.lean:686](/home/kim/lean-zip/Zip/Tar.lean:686) — *"unexpected end of archive reading {e.path} ({remaining} bytes remaining)"* | `481e562` | other (framing) |
| [testdata/tar/security/backslash-slip.tar](/home/kim/lean-zip/testdata/tar/security/backslash-slip.tar) | 2048 B | `Binary.isPathSafe` rejects backslashes before component-level `..` check at [Zip/Tar.lean:639](/home/kim/lean-zip/Zip/Tar.lean:639) — *"unsafe path"* | `481e562` (assertion added by #1555) | archive-slip |
| [testdata/tar/security/hardlink-outside.tar](/home/kim/lean-zip/testdata/tar/security/hardlink-outside.tar) | 512 B | `typeHardlink` silent-skip else-branch at [Zip/Tar.lean:710](/home/kim/lean-zip/Zip/Tar.lean:710); payload discarded, no `createHardlink` call, extract directory remains empty | #1555 | archive-slip |
| [testdata/tar/security/symlink-absolute.tar](/home/kim/lean-zip/testdata/tar/security/symlink-absolute.tar) | 512 B | Symlink linkname absolute/backslash check at [Zip/Tar.lean:701](/home/kim/lean-zip/Zip/Tar.lean:701) — *"unsafe symlink target"* | #1555 | archive-slip |
| [testdata/tar/security/symlink-slip.tar](/home/kim/lean-zip/testdata/tar/security/symlink-slip.tar) | 10240 B | Symlink linkname component `..` check at [Zip/Tar.lean:703](/home/kim/lean-zip/Zip/Tar.lean:703) — *"unsafe symlink target"* | `481e562` | archive-slip |
| [testdata/tar/security/tar-absolute.tar](/home/kim/lean-zip/testdata/tar/security/tar-absolute.tar) | 2048 B | `Binary.isPathSafe` rejects absolute paths at [Zip/Tar.lean:639](/home/kim/lean-zip/Zip/Tar.lean:639) — *"unsafe path"* | `481e562` | archive-slip |
| [testdata/tar/security/tar-slip.tar](/home/kim/lean-zip/testdata/tar/security/tar-slip.tar) | 10240 B | `Binary.isPathSafe` rejects `..` component traversal at [Zip/Tar.lean:639](/home/kim/lean-zip/Zip/Tar.lean:639) — *"unsafe path"* | `481e562` | archive-slip |
| [testdata/zip/malformed/bad-crc.zip](/home/kim/lean-zip/testdata/zip/malformed/bad-crc.zip) | 140 B | Post-extraction CRC32 verification at [Zip/Archive.lean:980](/home/kim/lean-zip/Zip/Archive.lean:980) — *"CRC32 mismatch"* | `481e562` | other (integrity check) |
| [testdata/zip/malformed/bad-method.zip](/home/kim/lean-zip/testdata/zip/malformed/bad-method.zip) | 140 B | CD-entry compression-method allowlist check at [Zip/Archive.lean:572](/home/kim/lean-zip/Zip/Archive.lean:572) — *"unsupported compression method"* (CD/LH both advertise method=14 (LZMA), outside lean-zip's `{0, 8}` allowlist; `parseCentralDir` rejects at CD parse time, pre-ZIP64-resolution, before any LH read. Previously caught by the late method-dispatch guard at [Zip/Archive.lean:975](/home/kim/lean-zip/Zip/Archive.lean:975) — *"unsupported method"* — which still fires as defense-in-depth if a future caller bypasses CD parsing) | #1801 | other (method validation) |
| [testdata/zip/malformed/cd-bad-method-early.zip](/home/kim/lean-zip/testdata/zip/malformed/cd-bad-method-early.zip) | 122 B | CD-entry compression-method allowlist check at [Zip/Archive.lean:572](/home/kim/lean-zip/Zip/Archive.lean:572) — *"unsupported compression method"* (CD/LH both advertise method=6 (imploded — deprecated in PKZIP 2.0, 1993), outside lean-zip's `{0, 8}` allowlist; `parseCentralDir` rejects at CD parse time, pre-ZIP64-resolution, before any LH read. Companion to `bad-method.zip` (CD/LH method=14, LZMA): both fixtures trip the same CD-parse guard, but distinct method values let paired-review distinguish which fixture fired) | #1801 | other (method validation) |
| [testdata/zip/malformed/cd-entry-disknum-mismatch.zip](/home/kim/lean-zip/testdata/zip/malformed/cd-entry-disknum-mismatch.zip) | 122 B | CD per-entry `diskNumberStart` consistency check at [Zip/Archive.lean:521](/home/kim/lean-zip/Zip/Archive.lean:521) — *"CD entry diskNumberStart mismatch"* (CD entry's APPNOTE §4.4.11 disk-number field at offset +34 is `7`; lean-zip supports single-disk archives only, so any nonzero value is rejected. Per-entry counterpart to `eocd-disknum-mismatch.zip` which covers the archive-level EOCD disk-number fields) | #1759 | other (CD/EOCD consistency) |
| [testdata/zip/malformed/cd-entry-localoffset-past-cdstart.zip](/home/kim/lean-zip/testdata/zip/malformed/cd-entry-localoffset-past-cdstart.zip) | 122 B | CD-entry `localOffset + 30 ≤ cdOffset` archive-layout invariant check at [Zip/Archive.lean:620](/home/kim/lean-zip/Zip/Archive.lean:620) — *"entry local offset overlaps central directory"* (LH+data at file offset 0 length 45, CD starts at offset 45, and the CD entry's `localOffset` field at CD +42 claims `50` — past `cdOffset - 30 = 15`, so the 30-byte fixed LH header cannot be read strictly before the CD region as APPNOTE §4.3.6 requires. Per-entry micro-shape sibling of the archive-level `cdOffset + cdSize ≤ eocdPos` macro-shape guard; pre-PR `Archive.list` had no gate at all, and only the extract path's late LH-signature check caught a subset of the construction) | #1813 | other (archive-layout invariant) |
| [testdata/zip/malformed/cd-entry-versionmadeby-too-high.zip](/home/kim/lean-zip/testdata/zip/malformed/cd-entry-versionmadeby-too-high.zip) | 122 B | CD per-entry `versionMadeBy` lower-byte upper-bound check at [Zip/Archive.lean:498](/home/kim/lean-zip/Zip/Archive.lean:498) — *"versionMadeBy spec-version byte out of range"* (CD entry's `versionMadeBy` field at CD +4 carries `0x03FF` — upper byte `3` UNIX host-OS, lower byte `255` = spec version 25.5, beyond the APPNOTE 6.3.10 maximum of `63` = spec version 6.3. `parseCentralDir` rejects at CD parse time before the sibling CD+6 `versionNeeded` read. LH has no `versionMadeBy` field (APPNOTE §4.3.7), so this is a single-side writer-invariant check like `cd-entry-disknum-mismatch.zip`. Companion of `cd-version-needed-too-high.zip` — together the two fixtures pin CD+4 and CD+6 to APPNOTE-defined ranges) | #1820 | other (writer-invariant) |
| [testdata/zip/malformed/cd-extra-overrun-datasize.zip](/home/kim/lean-zip/testdata/zip/malformed/cd-extra-overrun-datasize.zip) | 138 B | CD/LH extra-data sub-field structural check at [Zip/Archive.lean:582](/home/kim/lean-zip/Zip/Archive.lean:582) — *"malformed extra field"* (CD/LH extra-data carries a single sub-field with `headerId=0x5455` extended-timestamp but declared `dataSize=0xFF` while only 4 payload bytes remain; no ZIP64 sentinel is set so pre-PR `parseCentralDir` skipped `parseZip64Extra` entirely and the anomaly was entirely invisible. `validateExtraFieldStructure` runs unconditionally on the extra-data blob before the sentinel guard at both the CD and LH sites (mirror assertion at [Zip/Archive.lean:898](/home/kim/lean-zip/Zip/Archive.lean:898) — *"malformed local extra field"*). Outer-sub-field sibling of `zip64-extra-oversized-datasize.zip` at the inner-0x0001 layer of the same APPNOTE §4.5 extra-data smuggling class) | #1788 | other (ZIP64 consistency) |
| [testdata/zip/malformed/cd-lh-crc-mismatch.zip](/home/kim/lean-zip/testdata/zip/malformed/cd-lh-crc-mismatch.zip) | 122 B | CD/LH `crc32` consistency check at [Zip/Archive.lean:959](/home/kim/lean-zip/Zip/Archive.lean:959) — *"crc32 mismatch between CD and local header"* (LH crc differs from CD; both stored, sizes match so earlier guards do not fire first) | #1728 | other (CD/LH consistency) |
| [testdata/zip/malformed/cd-lh-flags-mismatch.zip](/home/kim/lean-zip/testdata/zip/malformed/cd-lh-flags-mismatch.zip) | 122 B | CD/LH flags-consistency check (bit-3-masked) at [Zip/Archive.lean:928](/home/kim/lean-zip/Zip/Archive.lean:928) — *"flags mismatch between CD and local header"* (CD sets bit 11 UTF-8-name, LH clears it — a known ZIP-smuggling vector) | #1715 | other (CD/LH consistency) |
| [testdata/zip/malformed/cd-lh-method-mismatch.zip](/home/kim/lean-zip/testdata/zip/malformed/cd-lh-method-mismatch.zip) | 122 B | CD/LH method-consistency check at [Zip/Archive.lean:919](/home/kim/lean-zip/Zip/Archive.lean:919) — *"method mismatch between CD and local header"* | #1554 | other (CD/LH consistency) |
| [testdata/zip/malformed/cd-lh-modtime-mismatch.zip](/home/kim/lean-zip/testdata/zip/malformed/cd-lh-modtime-mismatch.zip) | 122 B | CD/LH `lastModTime`/`lastModDate` consistency check at [Zip/Archive.lean:948](/home/kim/lean-zip/Zip/Archive.lean:948) — *"lastModTime/Date mismatch between CD and local header"* (LH time `0x1234` disagrees with CD time `0`; the two DOS-encoded `UInt16` slots — LH +10/+12, CD +12/+14 — are compared together and the check is ungated since APPNOTE §4.4.6 restricts the bit-3 data-descriptor allowance to crc/compSize/uncompSize only) | #1769 | other (CD/LH consistency) |
| [testdata/zip/malformed/cd-lh-size-mismatch.zip](/home/kim/lean-zip/testdata/zip/malformed/cd-lh-size-mismatch.zip) | 122 B | CD/LH `compressedSize` consistency check at [Zip/Archive.lean:953](/home/kim/lean-zip/Zip/Archive.lean:953) — *"compressedSize mismatch between CD and local header"* | #1554 | other (CD/LH consistency) |
| [testdata/zip/malformed/cd-lh-uncompsize-mismatch.zip](/home/kim/lean-zip/testdata/zip/malformed/cd-lh-uncompsize-mismatch.zip) | 122 B | CD/LH `uncompressedSize` consistency check at [Zip/Archive.lean:956](/home/kim/lean-zip/Zip/Archive.lean:956) — *"uncompressedSize mismatch between CD and local header"* (LH uncomp differs from CD; both stored, compressed sizes match so earlier guards do not fire first) | #1728 | other (CD/LH consistency) |
| [testdata/zip/malformed/cd-lh-version-mismatch.zip](/home/kim/lean-zip/testdata/zip/malformed/cd-lh-version-mismatch.zip) | 122 B | CD/LH `versionNeededToExtract` downgrade check at [Zip/Archive.lean:938](/home/kim/lean-zip/Zip/Archive.lean:938) — *"LH versionNeededToExtract (…) exceeds CD versionNeededToExtract (…)"* (LH claims higher version than CD — a capability-smuggle; CD > LH is legitimate per Go/Python ZIP64 producers and is allowed) | #1736 | other (CD/LH consistency) |
| [testdata/zip/malformed/cd-past-eof.zip](/home/kim/lean-zip/testdata/zip/malformed/cd-past-eof.zip) | 22 B | `cdOffset + cdSize ≤ fileSize` check at [Zip/Archive.lean:838](/home/kim/lean-zip/Zip/Archive.lean:838) — *"central directory extends beyond file"* | `481e562` | oversized allocation |
| [testdata/zip/malformed/cd-stored-size-mismatch.zip](/home/kim/lean-zip/testdata/zip/malformed/cd-stored-size-mismatch.zip) | 122 B | CD-entry stored-method size-invariant check at [Zip/Archive.lean:635](/home/kim/lean-zip/Zip/Archive.lean:635) — *"stored-method size mismatch"* (both CD and LH advertise `method=0` with `compressedSize=6, uncompressedSize=7` — no CD/LH divergence, but APPNOTE §4.4.5 *"no compression"* makes `compSize == uncompSize` a tautology. `parseCentralDir` rejects at CD parse time, post-ZIP64-resolution, before any LH read; complements the CD/LH `uncompressedSize` check which catches CD-vs-LH skew) | #1773 | other (CD/LH consistency) |
| [testdata/zip/malformed/cd-zip64-extra-duplicate.zip](/home/kim/lean-zip/testdata/zip/malformed/cd-zip64-extra-duplicate.zip) | 158 B | CD-side duplicate ZIP64 extra-block guard at [Zip/Archive.lean:586](/home/kim/lean-zip/Zip/Archive.lean:586) — *"duplicate ZIP64 extra field"* (CD entry's extra-data carries two `headerId == 0x0001` blocks back-to-back with `uncompSize` payloads `6` and `106`; APPNOTE §4.5 forbids more than one instance of any registered header ID per entry's extra-data, and the layout of each block depends on which standard 32-bit fields are at sentinel — two blocks make the resolved sizes ambiguous. `hasDuplicateZip64Extra` fires before `parseZip64Extra` so the error attributes the fault to the CD side; LH carries a single valid 0x0001 block. Sibling of `lh-zip64-extra-duplicate.zip`, `cd-extra-overrun-datasize.zip`, and `zip64-extra-oversized-datasize.zip` — together they close the ZIP64 extra-field layout-smuggling attack class) | #1793 | other (ZIP64 consistency) |
| [testdata/zip/malformed/eocd-disknum-mismatch.zip](/home/kim/lean-zip/testdata/zip/malformed/eocd-disknum-mismatch.zip) | 122 B | CD-vs-EOCD disk-number consistency check at [Zip/Archive.lean:462](/home/kim/lean-zip/Zip/Archive.lean:462) — *"EOCD disk-number mismatch"* (standard EOCD `diskWhereCDStarts=1`; lean-zip supports single-disk archives only, so any nonzero value in either disk-number field is rejected post-ZIP64-override) | #1742 | other (CD/EOCD consistency) |
| [testdata/zip/malformed/eocd-numentries-mismatch.zip](/home/kim/lean-zip/testdata/zip/malformed/eocd-numentries-mismatch.zip) | 122 B | CD-vs-EOCD `totalEntries` consistency check at [Zip/Archive.lean:651](/home/kim/lean-zip/Zip/Archive.lean:651) — *"EOCD totalEntries mismatch"* (EOCD declares 2 entries, CD has 1 — parser's trailing-signature loop would silently accept the short list without this guard) | #1733 | other (CD/EOCD consistency) |
| [testdata/zip/malformed/eocd-numentries-thisdisk-mismatch.zip](/home/kim/lean-zip/testdata/zip/malformed/eocd-numentries-thisdisk-mismatch.zip) | 122 B | EOCD-internal `numEntriesThisDisk` vs. `totalEntries` consistency check at [Zip/Archive.lean:466](/home/kim/lean-zip/Zip/Archive.lean:466) — *"EOCD numEntriesThisDisk mismatch"* (`numEntriesThisDisk=2`, `totalEntries=1`; single-disk archives must have the sibling EOCD entry-count fields equal, and the writer emits them at the same value) | #1752 | other (CD/EOCD consistency) |
| [testdata/zip/malformed/eocd-zip64-override-nosentinel.zip](/home/kim/lean-zip/testdata/zip/malformed/eocd-zip64-override-nosentinel.zip) | 198 B | ZIP64/standard-EOCD override sentinel check at [Zip/Archive.lean:337](/home/kim/lean-zip/Zip/Archive.lean:337) — *"EOCD ZIP64-override mismatch"* (standard-EOCD `cdOffset=42`, ZIP64 `cdOffset=45`; standard value is neither the APPNOTE §4.3.16 sentinel `0xFFFFFFFF` nor a numeric match with the ZIP64 override — a parser-differential smuggling vector) | #1745 | other (ZIP64 consistency) |
| [testdata/zip/malformed/invalid-utf8-with-flag.zip](/home/kim/lean-zip/testdata/zip/malformed/invalid-utf8-with-flag.zip) | 120 B | UTF-8-flagged entry name strict parse at [Zip/Archive.lean:532](/home/kim/lean-zip/Zip/Archive.lean:532) — *"invalid UTF-8 in entry name (UTF-8 flag set)"* | `481e562` | partial-decoder panic |
| [testdata/zip/malformed/lh-zip64-extra-duplicate.zip](/home/kim/lean-zip/testdata/zip/malformed/lh-zip64-extra-duplicate.zip) | 158 B | LH-side duplicate ZIP64 extra-block guard at [Zip/Archive.lean:905](/home/kim/lean-zip/Zip/Archive.lean:905) — *"duplicate ZIP64 local extra field"* (CD entry has a single valid `headerId == 0x0001` block so CD parse passes; LH carries two 0x0001 blocks with `uncompSize` payloads `6` and `106`. `hasDuplicateZip64Extra` fires inside `readEntryData` before any CD/LH consistency check. Sibling of `cd-zip64-extra-duplicate.zip` — the two distinct error wordings keep attribution between the parse layers loud under future refactors) | #1793 | other (ZIP64 consistency) |
| [testdata/zip/malformed/no-eocd.zip](/home/kim/lean-zip/testdata/zip/malformed/no-eocd.zip) | 44 B | EOCD-scan failure at [Zip/Archive.lean:837](/home/kim/lean-zip/Zip/Archive.lean:837) — *"cannot find end of central directory"* | `481e562` | other (framing) |
| [testdata/zip/malformed/oversized-compressed-size.zip](/home/kim/lean-zip/testdata/zip/malformed/oversized-compressed-size.zip) | 122 B | CD-entry stored-method size-invariant check at [Zip/Archive.lean:635](/home/kim/lean-zip/Zip/Archive.lean:635) — *"stored-method size mismatch"* (CD/LH both advertise method=0 with compSize=2 MiB and uncompSize=6; `parseCentralDir` rejects post-ZIP64-resolution before any LH read. Previously caught by the later `local data span` check in `readEntryData` — PR #1773's CD-parse guard fires first, kept in-corpus for regression coverage at the earlier layer) | #1497 | oversized allocation |
| [testdata/zip/malformed/oversized-zip64-compressed-size.zip](/home/kim/lean-zip/testdata/zip/malformed/oversized-zip64-compressed-size.zip) | 134 B | CD-entry stored-method size-invariant check at [Zip/Archive.lean:635](/home/kim/lean-zip/Zip/Archive.lean:635) — *"stored-method size mismatch"* (ZIP64 extra resolves compSize=1<<60, uncompSize=6 with method=0; `parseCentralDir` rejects post-ZIP64-resolution before any LH read. Previously caught by the later `local data span` check in `readEntryData` — PR #1773's CD-parse guard fires first, kept in-corpus for regression coverage at the earlier layer) | #1543 | oversized allocation |
| [testdata/zip/malformed/oversized-zip64-uncompressed-size.zip](/home/kim/lean-zip/testdata/zip/malformed/oversized-zip64-uncompressed-size.zip) | 134 B | CD-entry stored-method size-invariant check at [Zip/Archive.lean:635](/home/kim/lean-zip/Zip/Archive.lean:635) — *"stored-method size mismatch"* (ZIP64 extra resolves compSize=6, uncompSize=1<<60 with method=0; `parseCentralDir` rejects post-ZIP64-resolution before any LH read. Previously caught by the LH ZIP64 truncation check in `readEntryData` — PR #1773's CD-parse guard fires first, kept in-corpus for regression coverage at the earlier layer) | #1544 | oversized allocation |
| [testdata/zip/malformed/too-short.zip](/home/kim/lean-zip/testdata/zip/malformed/too-short.zip) | 10 B | EOCD-scan failure at [Zip/Archive.lean:837](/home/kim/lean-zip/Zip/Archive.lean:837) — *"cannot find end of central directory"* | `481e562` | other (framing) |
| [testdata/zip/malformed/zip64-eocd64-bad-recsize.zip](/home/kim/lean-zip/testdata/zip/malformed/zip64-eocd64-bad-recsize.zip) | 198 B | ZIP64 EOCD64 self-declared record-size check at [Zip/Archive.lean:319](/home/kim/lean-zip/Zip/Archive.lean:319) — *"ZIP64 EOCD64 record-size mismatch"* (EOCD64 `size of this record` field at `bufPos + 4` carries `0` instead of the required `44` for a v1 EOCD64; lean-zip reads the record at fixed per-field offsets from a hard-coded 56-byte layout, while a stricter parser that trusts the self-declared length would read past or short of that — a parser-differential smuggling vector) | #1761 | other (ZIP64 consistency) |
| [testdata/zip/malformed/zip64-extra-oversized-datasize.zip](/home/kim/lean-zip/testdata/zip/malformed/zip64-extra-oversized-datasize.zip) | 162 B | ZIP64 extra-field `dataSize` exactness check at [Zip/Archive.lean:589](/home/kim/lean-zip/Zip/Archive.lean:589) — *"malformed ZIP64 extra field"* (CD entry's ZIP64 extra `dataSize=16` claims two 8-byte slots while only `stdCompSize` is the sentinel, so APPNOTE §4.5.3 requires exactly `8 * 1 = 8` bytes; the trailing 8 bytes `0xDEADBEEFCAFEBABE` are attacker-chosen slack that a lenient parser silently discards. `parseZip64Extra` enforces `fpos == fieldEnd` after the three conditional reads — sibling of `zip64-eocd64-bad-recsize.zip` at a different layer of the same parser-differential attack class) | #1785 | other (ZIP64 consistency) |

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
