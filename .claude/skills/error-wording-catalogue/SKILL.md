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
| Archive CD stored-method size invariant | `Zip/Archive.lean` (`parseCentralDir`, post-ZIP64-resolution) | `zip: stored-method size mismatch for <name> (method=0, compressedSize=<C>, uncompressedSize=<U>)` | `"stored-method size mismatch"` |
| Archive CD compression-method allowlist | `Zip/Archive.lean` (`parseCentralDir`, pre-ZIP64-resolution, after `name` decode) | `zip: unsupported compression method <method> for <name> (lean-zip supports method 0 (stored) and method 8 (deflate))` | `"unsupported compression method"` (distinct from the late `"unsupported method"` dispatch in `readEntryData` — see precedence note below) |
| Archive CD general-purpose flag bit-5 (compressed patched data) | `Zip/Archive.lean` (`parseCentralDir`, pre-ZIP64-resolution, immediately after the method-allowlist check) | `zip: CD entry patched-data flag bit 5 set (flags=<flags>) for <name> at CD offset <pos>; lean-zip does not support APPNOTE §4.4.4 compressed patched data` | `"patched-data flag bit 5 set"` — distinguishable from the sibling encryption-related flag-bit family (`"encryption-related flag bit"`, in-flight PR #1771 / issue #1762) and from the CD/LH flags-consistency check (`"flags mismatch between CD and local header"`, PR #1715). The bit-5 check rejects archives where CD and LH agree on the flag word (bit 5 set on both); the CD/LH check rejects archives where they disagree modulo bit 3 |
| Archive CD versionNeededToExtract upper bound | `Zip/Archive.lean` (`parseCentralDir`, pre-ZIP64-resolution, after `name` decode) | `zip: unsupported versionNeededToExtract (<v>) for <name> at CD offset <pos>; lean-zip supports values up to 45 (ZIP64)` | `"unsupported versionNeededToExtract"` — must include the `"unsupported "` prefix to distinguish from the `"LH versionNeededToExtract"` CD/LH-downgrade substring below; both messages contain the word `versionNeededToExtract`, so matching bare `"versionNeededToExtract"` is ambiguous |
| Archive CD/LH versionNeededToExtract downgrade | `Zip/Archive.lean` (`readEntryData`, one-sided `LH > CD` check) | `zip: LH versionNeededToExtract (<lv>) exceeds CD versionNeededToExtract (<cv>) for <label>` | `"LH versionNeededToExtract"` — must include the `"LH "` prefix to distinguish from the `"unsupported versionNeededToExtract"` upper-bound substring above; the two guards live at different layers (CD-parse upper-bound before any LH read; CD/LH downgrade inside `readEntryData`) |
| Archive CD/LH lastModTime/Date | `Zip/Archive.lean` (`readEntryData`, ungated — fires even when bit 3 data-descriptor is set) | `zip: lastModTime/Date mismatch between CD and local header for <label> (CD time=<Tcd>, date=<Dcd>; LH time=<Tlh>, date=<Dlh>)` | `"lastModTime/Date mismatch"` |
| Archive CD/EOCD totalEntries | `Zip/Archive.lean` (`parseCentralDir` tail) | `zip: EOCD totalEntries mismatch (EOCD=<n>, parsed=<m>)` | `"EOCD totalEntries mismatch"` |
| Archive CD/EOCD disk-number | `Zip/Archive.lean` (`parseCentralDir` head) | `zip: EOCD disk-number mismatch (numberOfThisDisk=<n>, diskWhereCDStarts=<m>); lean-zip supports single-disk archives only` | `"EOCD disk-number mismatch"` |
| Archive CD/EOCD numEntriesThisDisk | `Zip/Archive.lean` (`parseCentralDir` head) | `zip: EOCD numEntriesThisDisk mismatch (this-disk=<n>, total=<m>)` | `"EOCD numEntriesThisDisk mismatch"` |
| Archive CD entry diskNumberStart | `Zip/Archive.lean` (`parseCentralDir` per-entry loop, immediately after `commentLen` read; fires before the `entryEnd > cdEnd` span check) | `zip: CD entry diskNumberStart mismatch (diskNumberStart=<n>) for entry at CD offset <pos>; lean-zip supports single-disk archives only` | `"CD entry diskNumberStart mismatch"` |
| Archive CD entry internalAttrs reserved bits | `Zip/Archive.lean` (`parseCentralDir` per-entry loop, immediately after the `diskNumberStart` guard; fires before the `entryEnd > cdEnd` span check) | `zip: CD entry internalAttrs reserved bits set (internalAttrs=<n>) for entry at CD offset <pos>` | `"internalAttrs reserved bits set"` — APPNOTE §4.4.10 defines only bit 0 ("apparent ASCII/text data"); bits 1-15 are reserved/unused, so the guard is `internalAttrs &&& 0xFFFE == 0` (preserves Info-ZIP bit-0 interop). Structurally unique across the project — `internalAttrs` appears in no other `Zip/Archive.lean` error message or assertThrows substring. Writer-zero single-field sibling of `"CD entry diskNumberStart mismatch"` (CD +34) on the same fast-fail layer |
| Archive CD entry name NUL byte | `Zip/Archive.lean` (`parseCentralDir` per-entry loop, immediately after `nameBytes := data.extract …`; fires on the raw `ByteArray` before the UTF-8 / Latin-1 decode block) | `zip: CD entry name contains NUL byte at CD offset <pos>` | `"name contains NUL byte"` — must include the `"name "` prefix to distinguish from the existing UTF-8 wording `"invalid UTF-8 in entry name (UTF-8 flag set)"` and any future name-bytes-mismatch substring (issue #1722). Matches APPNOTE §4.4.17 filename-field smuggling: NUL in filenames is a classic parser-differential / filesystem-truncation vector (POSIX `open`/`stat` truncates `evil.txt\x00.zip` to `evil.txt`; `Archive.list` callers routing on `entry.path` see the full NUL-embedded string). The guard is on the raw bytes so neither the UTF-8 nor the Latin-1 decode path re-introduces NUL into logs. Substring is short enough to survive CD-offset-value churn and specific enough to distinguish from every existing CD/LH name-related substring |
| Archive CD entry path-unsafe | `Zip/Archive.lean` (`parseCentralDir` per-entry loop, immediately after the UTF-8 / Latin-1 decode block at line :560-570; fires on the decoded `name : String` before the `versionNeeded` upper-bound check at :621) | `zip: CD entry has unsafe path <name.quote> at CD offset <pos>` | `"CD entry has unsafe path"` — must include the `"CD entry has "` prefix to keep attribution at CD parse explicit; the shorter `"unsafe path"` substring is shared with the extract-time `Binary.isPathSafe` calls at `Zip/Archive.lean:1103` / `:1107` (`zip: unsafe path: <entry.path>`) and with the Tar extract-time equivalent, so matching the bare `"unsafe path"` substring is ambiguous between CD-parse and extract-time layers. The existing `testdata/zip/security/{zip-slip,absolute-path,backslash-slip}.zip` fixtures assert the `"unsafe path"` substring and continue to pass because `"unsafe path"` is a substring of `"CD entry has unsafe path"` — but new tests should prefer the CD-parse-specific form so a future split between the two layers stays distinguishable. Mirrors the trailing-slash carve-out from the extract-time check (`name.endsWith "/"` → check the slash-stripped form) so legitimate directory entries are not tripped. Sibling of `"CD entry name contains NUL byte"` on the same filename-validation layer — the pair together closes the "smuggled name" attack class (byte content + path shape) |
| Archive CD entry empty filename | `Zip/Archive.lean` (`parseCentralDir` per-entry loop, immediately after the `nameLen` read at CD +28; fires on the raw `UInt16` field before `extraLen` / `commentLen` are read, before the `entryEnd > cdEnd` overrun check, and before the sibling NUL-byte / path-safety filename guards) | `zip: CD entry has empty filename (nameLen=0) at CD offset <pos>` | `"CD entry has empty filename"` — must include the `"CD entry has empty "` prefix to distinguish from the sibling `"CD entry has unsafe path"` substring (both start with `"CD entry has "`, so the shorter form is ambiguous). The two guards fire at different points in the per-entry loop: the empty-filename guard runs on the raw `nameLen` UInt16 before any decode, while the path-safety guard runs on the decoded `name : String` after the UTF-8 / Latin-1 block. Every legitimate ZIP entry has at least one byte of name (APPNOTE §4.4.10), so `nameLen == 0` is structurally pathological; writer-side at `Zip/Archive.lean:84` / :110 inherits the invariant from caller-supplied `entry.path`. Deliberate precedence: the empty-name guard fires before the CD-parse path-safety guard so failure attribution pins to the structural anomaly rather than the path-safety predicate (which would otherwise catch `""` via its empty-component rejection, but only if the decode succeeds). Sibling of `"CD entry name contains NUL byte"` (byte-content dimension) and `"CD entry has unsafe path"` (path-shape dimension) on the same filename-validation layer — the trio together closes the "smuggled name" attack class at CD parse (zero-length, NUL-embedded, and path-traversal forms all rejected pre-decode) |
| Archive CD-entry `localOffset + 30 ≤ cdOffset` archive-layout invariant | `Zip/Archive.lean` (`parseCentralDir`, post-ZIP64-resolution, before the stored-method size invariant) | `zip: entry local offset overlaps central directory for <name> (localOffset=<lo>, cdOffset=<co>)` | `"entry local offset overlaps central directory"` — the micro-shape per-entry counterpart to the macro-shape archive-level `cdOffset + cdSize ≤ eocdPos` check (`"central directory extends past EOCD"`) and to the late LH-signature check (`"bad local header signature"`) in `readEntryData`; the new substring fires first and on both `Archive.list` and `Archive.extract` paths, whereas the LH-signature check is extract-only |
| Archive ZIP64/standard-EOCD override sentinel | `Zip/Archive.lean` (`findEndOfCentralDir` ZIP64 branch) | `zip: EOCD ZIP64-override mismatch: standard EOCD <field>=<V>, ZIP64 <field>=<Z> (expected sentinel <S> or numeric match)` | `"EOCD ZIP64-override mismatch"`
| Archive ZIP64 EOCD64 record-size | `Zip/Archive.lean` (`findEndOfCentralDir` ZIP64 branch) | `zip: ZIP64 EOCD64 record-size mismatch (size=<n>, expected 44 for v1 EOCD64)` | `"ZIP64 EOCD64 record-size mismatch"` |
| Archive ZIP64 EOCD64 versionMadeBy lower-byte upper bound | `Zip/Archive.lean` (`findEndOfCentralDir` ZIP64 branch, immediately after the record-size check, at `bufPos + 12`) | `zip: ZIP64 EOCD64 versionMadeBy spec-version byte too high (versionMadeBy=<vmb>, spec-version=<lb>, max supported 63)` | `"ZIP64 EOCD64 versionMadeBy spec-version byte too high"` — must include the `"ZIP64 EOCD64 "` prefix to distinguish from the sibling per-entry CD+4 `versionMadeBy` check (issue #1812 / PR #1820, which uses the substring `"versionMadeBy spec-version byte out of range"`; both messages mention `versionMadeBy spec-version byte` so the bare phrase is ambiguous). APPNOTE §4.4.2.2 caps the lower byte at `63` (spec version 6.3); only the lower byte is checked, since host OS codes in the upper byte vary widely across real producers. Writer-side at [Zip/Archive.lean:153](/home/kim/lean-zip/Zip/Archive.lean:153) hard-codes `3 * 256 + 45 = 0x032D` (low byte 45) |
| Archive CD ZIP64 extra-field parse | `Zip/Archive.lean` (`parseCentralDir`, `parseZip64Extra` caller) | `zip: malformed ZIP64 extra field for <name>` | `"malformed ZIP64 extra field"` |
| Archive CD/LH extra-data sub-field structural check | `Zip/Archive.lean` (`validateExtraFieldStructure`, unconditionally in `parseCentralDir` / `readEntryData` before any ZIP64-sentinel guard) | CD: `zip: malformed extra field for <name>`; LH: `zip: malformed local extra field for <label>` | CD: `"malformed extra field"`; LH: `"malformed local extra field"` (both distinct from `"malformed ZIP64 extra field"`, which fires only when a sentinel is set and the inner `0x0001` block is malformed) |
| Archive CD ZIP64 duplicate extra-block | `Zip/Archive.lean` (`parseCentralDir`, `hasDuplicateZip64Extra` guard before `parseZip64Extra` call) | `zip: duplicate ZIP64 extra field for <name>` | `"duplicate ZIP64 extra field"` |
| Archive LH ZIP64 parse | `Zip/Archive.lean` | `truncated ZIP64 local extra field` | `"truncated ZIP64 local extra field"` |
| Archive LH ZIP64 duplicate extra-block | `Zip/Archive.lean` (`readEntryData`, `hasDuplicateZip64Extra` guard before `parseZip64Extra` call) | `zip: duplicate ZIP64 local extra field for <label>` | `"duplicate ZIP64 local extra field"` |
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
- **`Archive.extract` on a method=0 archive with mismatched CD sizes**:
  the `parseCentralDir` stored-method size-invariant check
  (`"stored-method size mismatch"`) fires before `readEntryData` runs,
  so it precedes the `"local data span"` check (#1497, #1543) and the
  `"truncated ZIP64 local extra field"` check (#1554) for the subset of
  fixtures where method=0 and the CD-resolved `compSize ≠ uncompSize`.
  The three `oversized-*.zip` fixtures in `testdata/zip/malformed/`
  all shifted to this substring as of the CD-parse-guard addition. If
  you need a regression that still exercises the later span or
  ZIP64-truncation checks, use method=8 (deflate) with the oversized
  claim so the stored-method check does not fire.
- **`Archive.extract` on an archive whose CD `method` is outside
  `{0, 8}`**: the `parseCentralDir` compression-method allowlist
  (`"unsupported compression method"`, added in PR #1801) fires
  pre-ZIP64-resolution and shadows the late `readEntryData`
  `"unsupported method"` dispatch for all CD-parseable archives.
  `bad-method.zip` (CD/LH method=14) and `cd-bad-method-early.zip`
  (CD/LH method=6) both trip the new substring; the late
  `"unsupported method"` throw is preserved as defense-in-depth
  but is unreachable via the public API today. If you need a
  regression that still exercises the late dispatch, you would
  need to bypass `parseCentralDir` — currently impossible from the
  public API. Substring discipline: match
  `"unsupported compression method"` (the new wording, with the
  word "compression"); the bare `"unsupported method"` substring
  also matches the new message (it's a substring of the new
  wording), but tests should prefer the more specific form so a
  future split between the two layers stays distinguishable.
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
