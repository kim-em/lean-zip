---
name: error-wording-catalogue
description: Use when writing a test that must match an error message thrown by lean-zip — bomb-limit tests, malformed-archive assertThrows, CD/LH consistency assertions, or any `.toBaseIO` + `msg.contains` block. Tabulates the error-substring families so you pick the right match string the first time.
allowed-tools: Read, Bash, Grep
---

# Error-Wording Catalogue (lean-zip)

Project-local reference for choosing the `msg.contains "..."`
substring when asserting a failure path. The project has several
error-wording families; picking the wrong one fails CI with
confusing "unexpected error" output, and picking an over-specific
one makes the test brittle to message rewrites.

## Canonical substrings by subsystem

| Subsystem | Emits from | Full message (approx.) | Recommended match substring |
|-----------|------------|------------------------|-----------------------------|
| FFI whole-buffer decoders | `c/zlib_ffi.c:195` | `ZLib: decompressed data exceeds limit (…)` | `"exceeds limit"` |
| FFI streaming decoders (gzip) | `Zip/Gzip.lean` (`decompressStream`, `decompressFile`) | `gzip: decompressed stream exceeds limit (<N> bytes)` | `"exceeds limit"` |
| FFI streaming decoders (raw deflate) | `Zip/RawDeflate.lean` (`decompressStream`) | `raw deflate: decompressed stream exceeds limit (<N> bytes)` | `"exceeds limit"` |
| Archive per-entry bomb | `Zip/Archive.lean:408-410` | `Archive: entry <name> exceeds limit (…)` | `"exceeds limit"` |
| Whole-archive bomb | `Zip/Archive.lean:677`, `Zip/Tar.lean:677` (`extract` `maxTotalSize`) | `zip:`/`tar: total extracted size (…) exceeds whole-archive limit (…)` | `"exceeds whole-archive limit"` |
| Archive ZIP64 span check | `Zip/Archive.lean:428-429` | `Archive: local data span for <name> (…)` | `"local data span"` |
| Archive CD/LH consistency | `Zip/Archive.lean` | `mismatch between CD and local header (<field>)` | `"mismatch between CD and local header"` |
| Archive CD/LH lastModTime/Date | `Zip/Archive.lean` (`readEntryData`, ungated — fires even when bit 3 data-descriptor is set) | `zip: lastModTime/Date mismatch between CD and local header for <label> (CD time=<Tcd>, date=<Dcd>; LH time=<Tlh>, date=<Dlh>)` | `"lastModTime/Date mismatch"` |
| Archive CD/EOCD totalEntries | `Zip/Archive.lean` (`parseCentralDir` tail) | `zip: EOCD totalEntries mismatch (EOCD=<n>, parsed=<m>)` | `"EOCD totalEntries mismatch"` |
| Archive CD/EOCD disk-number | `Zip/Archive.lean` (`parseCentralDir` head) | `zip: EOCD disk-number mismatch (numberOfThisDisk=<n>, diskWhereCDStarts=<m>); lean-zip supports single-disk archives only` | `"EOCD disk-number mismatch"` |
| Archive CD/EOCD numEntriesThisDisk | `Zip/Archive.lean` (`parseCentralDir` head) | `zip: EOCD numEntriesThisDisk mismatch (this-disk=<n>, total=<m>)` | `"EOCD numEntriesThisDisk mismatch"` |
| Archive ZIP64/standard-EOCD override sentinel | `Zip/Archive.lean` (`findEndOfCentralDir` ZIP64 branch) | `zip: EOCD ZIP64-override mismatch: standard EOCD <field>=<V>, ZIP64 <field>=<Z> (expected sentinel <S> or numeric match)` | `"EOCD ZIP64-override mismatch"`
| Archive ZIP64 EOCD64 record-size | `Zip/Archive.lean` (`findEndOfCentralDir` ZIP64 branch) | `zip: ZIP64 EOCD64 record-size mismatch (size=<n>, expected 44 for v1 EOCD64)` | `"ZIP64 EOCD64 record-size mismatch"` |
| Archive LH ZIP64 parse | `Zip/Archive.lean` | `truncated ZIP64 local extra field` | `"truncated ZIP64 local extra field"` |
| Tar per-entry bomb | `Zip/Tar.lean:565-566` | `Tar: entry <name> exceeds limit (…)` | `"exceeds limit"` |
| Tar header pseudo-entry cap | `Zip/Tar.lean:223` | `tar: header entry size (…) exceeds maximum header size (…)` | `"exceeds maximum header size"` |
| Tar unsafe path | `Zip/Tar.lean` (via `Binary.isPathSafe`) | `Tar: unsafe path <name>` | `"unsafe path"` |
| Tar unsafe symlink | `Zip/Tar.lean` | `Tar: unsafe symlink target <linkname>` | `"unsafe symlink"` |
| Tar short-read | `Zip/Tar.lean` | `tar: unexpected end of archive reading entry data` | `"unexpected end of archive"` |
| Native Inflate overrun | `Zip/Native/Inflate.lean:269, 285, 321` | `Inflate: output exceeds maximum size` | `"exceeds maximum size"` |
| Native Gzip overrun (outer loop) | `Zip/Native/Gzip.lean:88` | `Gzip: total output exceeds maximum size` | `"exceeds maximum size"` |
| Native GzipDecode header/footer | `Zip/Native/Gzip.lean` | `Gzip: too large` or header-validation text | use `"exceeds maximum size"` if the test can force overrun via `inflateRaw`; see notes |

## FFI vs native: the user-visible split

`"exceeds limit"` is emitted by the FFI path (`c/zlib_ffi.c`) and by
the archive/tar per-entry size check (which measures against the
caller-supplied `maxEntrySize`). `"exceeds maximum size"` is emitted
by the native Lean path (`Zip/Native/Inflate.lean`,
`Zip/Native/Gzip.lean`) when the output budget is exhausted inside
the Lean-level inflater.

A third family — `"exceeds maximum header size"` — was added in
#1597 for the Tar header-path pseudo-entries (GNU long-name /
long-link, PAX extended / global). It sits on a *separate* knob
(`maxHeaderSize`, default 8 MiB) from the per-entry cap
(`maxEntrySize`), so a test that wants to exercise the header cap
**must** match the long form — `"exceeds maximum header size"` —
not bare `"exceeds"` or `"exceeds limit"`, both of which would
also succeed against the payload path and produce false positives.

This divergence is **intentional today** but documented as a
Track E Priority 2 item 4 follow-up candidate — if you are landing a
test that needs to be stable under a future rewording, match the
short shared noun (`"exceeds"`) only after reading the source and
confirming no other message in the call graph contains it.

**Streaming-FFI docstring phrasing differs from whole-buffer
phrasing.** Streaming FFI docstrings (post-#1610 / #1631) use
*"bomb-unsafe — only do this when the input is trusted"* while
whole-buffer docstrings (post-#1573) use *"bomb-unsafe for
untrusted input"*. Mild drift, not a bug. Tests that grep on
docstring text (there are currently none) should match
*"bomb-unsafe"* as the stable substring.

## Which message fires first

When a function composes several checks, the *earlier* check wins.
Knowing the order matters for picking the right substring:

- **`Tar.extractTarGzNative`**: calls `Zip.Native.GzipDecode.decompress`,
  which calls `Zip.Native.Inflate.inflateRaw`. When
  `maxOutputSize := 10` is passed and input is larger, the Inflate-level
  check (`"Inflate: output exceeds maximum size"`) fires before the
  outer GzipDecode/`"too large"` check. Match `"exceeds maximum size"`,
  not `"too large"`. See #1561.
- **`Archive.readEntryData` on a malformed ZIP64 LH**: the strict LH
  ZIP64 parse check (`"truncated ZIP64 local extra field"`, added in
  #1554) fires before the existing `"size mismatch"` check. A fixture
  that previously matched `"size mismatch"` must be updated — or
  supplemented by a companion fixture with consistent LH/CD metadata
  and a deliberately wrong decompressed size.
- **`Archive.readEntryData` on an oversized ZIP64 compressedSize
  claim**: the second `assertSpanInFile` (span check for local data)
  fires before the read is attempted. Match `"local data span"`. See
  #1543.
- **`Tar.extract` on an archive-slip symlink**: the unsafe-symlink
  reject fires before `Handle.createSymlink`. Match
  `"unsafe symlink"`. See #1555.
- **`Tar.extract` on a backslash path**: `Binary.isPathSafe` on the
  regular path component fires before any typeflag-specific branch.
  Match `"unsafe path"` even for `typeSymlink` entries whose linkname
  would *also* be rejected. See #1555.

## Probe-then-finalise workflow

Don't guess. Write the assertion with a placeholder substring and
let the test surface the real error:

    unless msg.contains "<<PROBE>>" do
      throw (IO.userError s!"unexpected error: {msg}")

Then `lake exe test` will print the actual `msg` in its failure
output. Copy the matching substring from there into the final
assertion and re-run.

This is cheaper than reading three source files to trace which
branch fires, and it catches the case where a new check has been
added in a recent PR.

## When to match `"exceeds"` vs something more specific

- **Bomb tests** that just want "budget exhausted, somewhere":
  match `"exceeds"` (works for both FFI and native). Note this in
  a comment so the next reader knows the test is deliberately
  subsystem-agnostic.
- **Subsystem-specific tests** (e.g., testing that the native path
  took a specific branch): match the subsystem's specific substring
  from the table above.
- **Regression tests for a specific PR**: match the substring the
  PR introduced, so future refactors that reword the message
  surface the test failure loudly.

## Maintenance

When a Track E PR changes an error message, the PR must update this
skill in the same commit. That's also the rule for the reverse
direction: if this catalogue doesn't name a substring you need,
add a row before the test lands.
