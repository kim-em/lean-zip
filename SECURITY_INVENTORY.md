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
  - the April 2026 report against Lean runtime allocation/read paths is
    exactly the kind of risk this inventory must track
- Missing work:
  - prove or enforce stronger preconditions before every `Handle.read`
    and `Stream.read` driven by archive metadata
  - add regression fixtures for oversized ZIP64 size claims

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
- Missing work:
  - maintain sanitizer coverage for all FFI entry points
  - add dedicated malformed-input regression tests for streaming paths
  - audit all formatted error and allocation helpers after any C changes

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
  - prove bounded-read lemmas for the guarded read paths if tractable
- Recent wins:
  - central-directory vs. local-header mismatch checks — PR #1554
    (`testdata/zip/malformed/cd-lh-method-mismatch.zip`,
    `cd-lh-size-mismatch.zip`)
  - oversized ZIP64 compressed-size fixture — PR #1543
    (`testdata/zip/malformed/oversized-zip64-compressed-size.zip`)
  - oversized ZIP64 uncompressed-size fixture — PR #1544
    (`testdata/zip/malformed/oversized-zip64-uncompressed-size.zip`)

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

`Tar.extract` (in [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean:1))
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
  - inventory all call sites using unlimited decompression (`0 = no limit`)
  - decide whether all public extraction APIs should default to bounded mode
  - add sanitizer-backed regression coverage for streaming decode paths

## Known Immediate Audit Targets

### 1. ZIP metadata to `Handle.read`

- File: [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean:341)
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

- File: [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean:216)
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
  - [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean:386)
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
| [Zlib.decompress](/home/kim/lean-zip/Zip/Basic.lean:11) (FFI) | `maxDecompressedSize : UInt64` | `0` | no limit | whole-buffer zlib (RFC 1950). Only API with a committed bomb-limit regression test today ([ZipTest/Zlib.lean:14-19](/home/kim/lean-zip/ZipTest/Zlib.lean:14)). |
| [Gzip.decompress](/home/kim/lean-zip/Zip/Gzip.lean:12) (FFI) | `maxDecompressedSize : UInt64` | `0` | no limit | whole-buffer gzip (RFC 1952) + auto-zlib. No bomb-limit regression test. |
| [RawDeflate.decompress](/home/kim/lean-zip/Zip/RawDeflate.lean:16) (FFI) | `maxDecompressedSize : UInt64` | `0` | no limit | whole-buffer raw DEFLATE (ZIP method 8). No bomb-limit regression test. |
| [Gzip.decompressStream](/home/kim/lean-zip/Zip/Gzip.lean:73) (FFI) | — | — | — | streaming; no per-call output cap. Bounded only by caller's sink / disk. |
| [Gzip.decompressFile](/home/kim/lean-zip/Zip/Gzip.lean:97) (FFI) | — | — | — | writes direct to disk via `decompressStream`; no cap. |
| [RawDeflate.decompressStream](/home/kim/lean-zip/Zip/RawDeflate.lean:45) (FFI) | — | — | — | streaming; no per-call output cap. |
| [Zip.Native.Inflate.inflate](/home/kim/lean-zip/Zip/Native/Inflate.lean:379) | `maxOutputSize : Nat` | `1 * 1024^3` (1 GiB) | hard cap at 0 bytes (explicit) | no unlimited mode; default is 1 GiB. |
| [Zip.Native.GzipDecode.decompress](/home/kim/lean-zip/Zip/Native/Gzip.lean:30) | `maxOutputSize : Nat` | `256 * 1024^2` (256 MiB) | hard cap at 0 bytes (explicit) | no unlimited mode; default is 256 MiB. |
| [Zip.Native.ZlibDecode.decompress](/home/kim/lean-zip/Zip/Native/Gzip.lean:122) | `maxOutputSize : Nat` | `256 * 1024^2` (256 MiB) | hard cap at 0 bytes (explicit) | no unlimited mode; default is 256 MiB. |
| [Zip.Native.decompressAuto](/home/kim/lean-zip/Zip/Native/Gzip.lean:212) | `maxOutputSize : Nat` | `256 * 1024^2` (256 MiB) | hard cap at 0 bytes (explicit) | format-auto dispatch over the three natives above. |
| [Archive.list](/home/kim/lean-zip/Zip/Archive.lean:494) | `maxCentralDirSize : Nat` | `67108864` (64 MiB) | no limit | metadata-only; caps CD allocation, not decompressed payload. |
| [Archive.extract](/home/kim/lean-zip/Zip/Archive.lean:500) | `maxCentralDirSize : Nat` | `67108864` (64 MiB) | no limit | CD allocation cap. |
| [Archive.extract](/home/kim/lean-zip/Zip/Archive.lean:500) | `maxEntrySize : UInt64` | `0` | **asymmetric** — FFI: no limit; native: silently upgraded to 256 MiB inside `readEntryData` (see [Zip/Archive.lean:477](/home/kim/lean-zip/Zip/Archive.lean:477)) | per-entry cap on the decompressed payload. |
| [Archive.extractFile](/home/kim/lean-zip/Zip/Archive.lean:524) | `maxCentralDirSize : Nat` | `67108864` (64 MiB) | no limit | CD allocation cap. |
| [Archive.extractFile](/home/kim/lean-zip/Zip/Archive.lean:524) | `maxEntrySize : UInt64` | `0` | same asymmetry as `Archive.extract` | per-entry cap. |
| [Tar.extract](/home/kim/lean-zip/Zip/Tar.lean:537) | `maxEntrySize : UInt64` | `0` | no limit | per-entry byte cap, applied via header `e.size` before any I/O (see [Zip/Tar.lean:544](/home/kim/lean-zip/Zip/Tar.lean:544)). No whole-archive cap. |
| [Tar.extractTarGz](/home/kim/lean-zip/Zip/Tar.lean:625) | `maxEntrySize : UInt64` | `0` | no limit | per-entry cap. Outer gzip decode is streaming via `Gzip.InflateState`; no per-stream output cap. |
| [Tar.extractTarGzNative](/home/kim/lean-zip/Zip/Tar.lean:660) | `maxEntrySize : UInt64` | `0` | no limit | per-entry cap. |
| [Tar.extractTarGzNative](/home/kim/lean-zip/Zip/Tar.lean:660) | `maxOutputSize : Nat` | `256 * 1024^2` (256 MiB) | hard cap at 0 bytes (explicit) | whole-archive tar-buffer cap for the outer native gzip decode. |

### Known inconsistencies

- **`Archive.readEntryData` per-entry cap asymmetry.** When
  `maxEntrySize = 0`, the FFI path (`RawDeflate.decompress`) runs
  unlimited, but the native path (`Zip.Native.Inflate.inflate`)
  silently upgrades to a hard 256 MiB cap — see the
  `nativeMax := if maxEntrySize == 0 then 256 * 1024 * 1024 else ...`
  branch at [Zip/Archive.lean:477](/home/kim/lean-zip/Zip/Archive.lean:477).
  The same caller argument therefore produces different bomb-rejection
  behaviour depending on `useNative`.
- **`Tar.extractTarGz.maxOutputSize` vs. low-level defaults.**
  `Tar.extractTarGzNative` caps the outer gzip decode at 256 MiB,
  mirroring `Zip.Native.GzipDecode.decompress`. But the lower-level
  FFI APIs — `Zlib.decompress`, `Gzip.decompress`,
  `RawDeflate.decompress` — default to **unlimited** for the same
  kind of whole-buffer decompression. A caller copying the
  `Tar.extractTarGz`-style pattern with the FFI decoders gets no
  default protection.
- **Native decompression defaults disagree with each other.**
  `Zip.Native.Inflate.inflate` defaults to **1 GiB**;
  `Zip.Native.GzipDecode.decompress`,
  `Zip.Native.ZlibDecode.decompress`, and
  `Zip.Native.decompressAuto` default to **256 MiB**. Picking a
  format auto-dispatch vs. raw DEFLATE directly changes the default
  cap by a factor of 4.
- **`maxCentralDirSize` vs. `maxEntrySize` semantics.** In
  `Archive.list` / `Archive.extract` / `Archive.extractFile`, the CD
  cap defaults to a finite 64 MiB (good), while the per-entry cap
  defaults to `0 = unlimited` (weak). The mixed semantics are easy to
  misread — a caller who sees "limits default to sensible values" on
  the CD side might reasonably assume the entry side is also
  bounded.
- **Streaming FFI APIs have no output cap at all.**
  `Gzip.decompressStream`, `Gzip.decompressFile`, and
  `RawDeflate.decompressStream` take no output-size parameter — they
  are bounded only by the caller's sink (`output.write`). Any tool
  built on top that writes to disk is a potential bomb target with
  no library-level guard.

### Recommended policy

This is a **proposal** for the safer-default direction; numbers are
placeholders to seed discussion, not final values. Treat each
recommendation as a starting point for the bomb-limit regression
issues and the follow-up docstring/default change.

1. **Low-level whole-buffer FFI decoders** — `Zlib.decompress`,
   `Gzip.decompress`, `RawDeflate.decompress`.
   - Keep `0 = no limit` as the literal encoding, but change the
     **default** to a finite value (suggested: **256 MiB**, matching
     the native decoders).
   - Callers that genuinely need unlimited mode pass `0` explicitly
     — the intent is visible at the call site.
2. **Streaming FFI decoders** — `Gzip.decompressStream`,
   `Gzip.decompressFile`, `RawDeflate.decompressStream`.
   - Add an optional `maxDecompressedSize : UInt64 := 256 * 1024^2`
     parameter and enforce it by counting pushed output bytes.
   - The streaming case is the one with no current guard; adding
     the parameter is the only way to expose a cap without
     reading into memory.
3. **Archive extraction — per-entry cap** —
   `Archive.extract.maxEntrySize`, `Archive.extractFile.maxEntrySize`,
   `Tar.extract.maxEntrySize`, `Tar.extractTarGz.maxEntrySize`,
   `Tar.extractTarGzNative.maxEntrySize`.
   - Change default from `0` to a finite per-entry cap
     (suggested: **1 GiB** per entry). `0` continues to mean
     "no per-entry limit" for callers that opt in.
   - Remove the silent `0 → 256 MiB` upgrade in
     `Archive.readEntryData` for the native backend; once the
     default is finite, the two backends behave identically.
4. **Archive extraction — whole-archive cap**.
   - Add a new `maxTotalSize : UInt64 := 0` (sum of decompressed
     entries) to `Archive.extract` and the tar extractors. Default
     `0 = no limit` is acceptable here as a starting point because
     `maxEntrySize` (recommendation 3) already bounds the common
     case; the total cap is a second line of defence against
     many-small-entries bombs.
5. **Native-side uniformity**.
   - Normalise the native decoder defaults to match one value
     (suggested: **1 GiB**, matching `Zip.Native.Inflate.inflate`).
     Whichever value is chosen, all four — `Inflate.inflate`,
     `GzipDecode.decompress`, `ZlibDecode.decompress`,
     `decompressAuto` — should agree.
6. **Docstrings and error messages**.
   - Every decompression API should state its default, the
     meaning of `0`, and the exact error thrown on cap overflow.
     This is Priority 2 item 4 on the audit checklist and is a
     separate issue.

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

- No bomb-limit regression test yet exists for any FFI decompression
  default except `Zlib.decompress`. Sibling issues in this session
  add coverage for `Gzip.decompress`, `RawDeflate.decompress`,
  `Zip.Native.GzipDecode.decompress`, `Archive.extract`,
  `Archive.extractFile`, `Tar.extract`, and `Tar.extractTarGz`.
- No cap is enforced on the streaming FFI decoders
  (`Gzip.decompressStream`, `Gzip.decompressFile`,
  `RawDeflate.decompressStream`) — see recommendation 2. A crafted
  input that inflates to terabytes will happily write terabytes to
  the caller's sink today.
- There is no public API for "whole-archive" decompressed-size cap
  on ZIP or tar extraction — see recommendation 4.

## Required Maintenance Rule

Whenever a new parser, extraction path, FFI helper, or streaming API is
added, this file must be updated in the same change set with:

- trust status
- guardrails
- known missing work
- regression references if a bug prompted the change
