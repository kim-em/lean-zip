---
name: malformed-fixture-builder
description: Use when authoring new malformed-archive regression fixtures for lean-zip — tar malformed PAX/GNU fixtures, tar symlink/hardlink archive-slip fixtures, or malformed ZIP fixtures under testdata/{tar,zip}/malformed/ or testdata/tar/security/. Covers the fixture-builder script shape, size budgets, determinism checklist, and assertion-writing patterns.
allowed-tools: Read, Write, Edit, Bash, Glob, Grep
---

# Malformed-Fixture Builder (Track E)

This skill captures the conventions that converged across the Track E
security-audit fixture cluster (PRs #1543, #1544, #1545, #1546, #1554,
#1555). Use it whenever an issue asks you to add a new malformed
archive fixture, archive-slip fixture, or CD/LH mismatch fixture.

## Layout

Fixtures live under one of three `testdata/` subtrees — match the
existing siblings:

| Fixture family | Directory | Example |
|----------------|-----------|---------|
| Malformed ZIP | `testdata/zip/malformed/` | `oversized-zip64-compressed-size.zip` |
| Malformed tar (PAX / GNU / truncated) | `testdata/tar/malformed/` | `pax-invalid-utf8-key.tar`, `gnu-longname-truncated.tar` |
| Tar security (archive-slip / symlink / hardlink) | `testdata/tar/security/` | `symlink-absolute.tar`, `tar-slip.tar` |

Builder scripts live under `scripts/`. Use Lean for tar-format fixtures
(reuse `Tar.buildHeader` + `Tar.paddingFor`); use Python for ZIP
fixtures (CRC32 + PKZIP little-endian headers are already idiomatic in
`scripts/build-cd-lh-mismatch.py`).

## Lean fixture-builder skeleton

Every Lean builder in `scripts/` follows this shape:

    import Zip

    /-! Build <what> regression fixtures for Track E Priority <N>.

    <one short paragraph describing the fixture family and which guard
    path it exercises>

    Run once at development time:

        lake env lean --run scripts/<name>.lean

    Output (byte-deterministic):
    - testdata/<subtree>/<fixture-1>.tar
    - testdata/<subtree>/<fixture-2>.tar
    -/

    def build<Variant> (<args>) (outPath : System.FilePath) : IO Unit := do
      let entry : Tar.Entry :=
        { path     := "..."
          size     := ...
          mode     := 0o644
          typeflag := Tar.type<Kind> }
      let hdr ← Tar.buildHeader entry
      let pad := Tar.paddingFor entry.size
      let out := hdr ++ payload ++ Binary.zeros pad
      IO.FS.writeBinFile outPath out

    def main : IO Unit := do
      let outDir : System.FilePath := "testdata/<subtree>"
      build<Variant> ... (outDir / "<name>.tar")
      ...
      IO.println s!"Built <N> fixtures under {outDir}."

**Key building blocks** (all already exist):

- `Tar.buildHeader : Tar.Entry → IO ByteArray` — 512-byte UStar header
  with checksum. Entry fields: `path`, `linkname`, `size : UInt64`,
  `mode`, `typeflag : UInt8`.
- `Tar.paddingFor (size : UInt64) : Nat` — pad count to next 512-block.
- `Binary.zeros : Nat → ByteArray` — zero-filled array.
- Typeflag constants: `Tar.typeRegular`, `Tar.typeSymlink`,
  `Tar.typeHardlink`, `Tar.typePaxExtended`, and the GNU long-name /
  long-link bytes `0x4C`/`0x4B` (referenced as `'L'`/`'K'` literals;
  add named constants when introducing a new typeflag into a fixture).

## Fixture-size budgets

These are the observed budgets for each family. Match them unless the
issue specifies otherwise — the existing test-suite reporting code
assumes fixtures stay in these size ranges:

| Family | Budget | Rationale |
|--------|--------|-----------|
| ZIP64 malformed | ≤200 B (observed 134 B) | Minimal stored entry + CD + ZIP64 extra + EOCD. |
| ZIP CD/LH mismatch | ≤200 B | Same as above. |
| PAX malformed | 2048 B | Matches `bad-checksum.tar`/`no-magic.tar` precedent. Two 512-byte entries × 2 blocks of payload. |
| GNU long malformed | ≤1536 B | Pseudo-header (512) + truncated or NUL-terminated payload (≤512) + optional trailing regular entry (512). |
| Symlink/hardlink | 512 B (single header) | `size == 0`, no payload, no trailing zero blocks. Matches `tar-slip.tar` / `symlink-slip.tar`. |

## End-of-archive policy

`Tar.forEntries` terminates on a short read (`readExact input 512`
returns a block with `block.size < 512`), so trailing zero-blocks are
**not required** for tar fixtures. Every Track E tar builder omits
them. This keeps fixtures minimal and makes byte-diffs easier to read.

Exception: if a future fixture genuinely needs to test zero-block
termination behaviour, add the zero blocks and document why in the
builder's module docstring.

## Exabyte sentinel value

When a fixture needs an "obviously impossible" size (ZIP64 oversized
compressed/uncompressed claims), use:

    0x1000000000000000  -- = 2^60 bytes ≈ 1.15 EiB

Rationale (from #1543's progress entry): *"using a named power of two
at exabyte scale makes the intent obvious in future hex-diffs."* Any
value exceeding `fileSize - headerBytes` fires the same span check,
but a canonical sentinel keeps the intent readable.

Use this same value in sibling fixtures (#1544 mirrored #1543
verbatim) so cross-fixture hex-diffs are minimal.

## Determinism checklist

Every builder script must produce byte-identical output across runs.
Verify before committing:

    # Build twice, compare
    nix-shell --run "lake env lean --run scripts/<builder>.lean"
    sha256sum testdata/<subtree>/*.tar > /tmp/fixtures-run1.txt
    rm testdata/<subtree>/*.tar
    nix-shell --run "lake env lean --run scripts/<builder>.lean"
    sha256sum testdata/<subtree>/*.tar > /tmp/fixtures-run2.txt
    diff /tmp/fixtures-run1.txt /tmp/fixtures-run2.txt  # must be empty

Record the SHA-256 of every fixture in the progress entry. This makes
regressions obvious the next time the builder is rerun.

Sources of nondeterminism to avoid:

- Timestamps: set `mtime := 0` in `Tar.Entry` (the default is already
  0). `Tar.buildHeader` emits `000000000000` for `mtime`, `uid`, `gid`
  by default.
- Random UUIDs or PIDs: never embed runtime values.
- `IO.currTime` / `IO.FS.metadata`: never read filesystem state.

## Per-slot printable-prefix discipline (interior-NUL fixtures)

Per-slot fixtures that smuggle an interior NUL into a fixed-width
header field should use a **slot-distinct printable ASCII prefix**.
That prefix is what a parser-differential caller would see if
`Binary.fromLatin1` (or its reader equivalent) truncated at the
NUL — making it slot-distinct encodes slot-identity for human
readers of `xxd` diffs.

Accumulated post-#1928 wave examples (sources:
`scripts/build-ustar-malformed-fixtures.lean` and
`scripts/build-gnu-long-malformed-fixtures.lean`):

| Family | Slot | Fixture | Smuggled value | Prefix | PR |
|--------|------|---------|----------------|--------|----|
| UStar interior-NUL | name      | `ustar-name-nul-in-name.tar`     | `"evil.txt\x00.tar"`      | `evil.txt` | #1880 |
| UStar interior-NUL | linkname  | `ustar-linkname-nul-in-name.tar` | `"evil.lnk\x00.tar"`      | `evil.lnk` | #1934 |
| UStar interior-NUL | prefix    | `ustar-prefix-nul-in-name.tar`   | `"badpfx\x00bad"`         | `badpfx`   | #1937 |
| UStar interior-NUL | uname     | `ustar-uname-nul-in-uname.tar`   | `"trusted\x00rogue"`      | `trusted`  | #1944 |
| UStar interior-NUL | gname     | `ustar-gname-nul-in-gname.tar`   | `"trusted\x00rogue"`      | `trusted`  | #1957 |
| GNU long-name      | long-name | `gnu-longname-nul-in-name.tar`   | `"evil.txt\x00.tar"`      | `evil.txt` | #1865 |
| GNU long-name      | long-link | `gnu-longlink-nul-in-link.tar`   | `"safe.lnk\x00rogue.tar"` | `safe.lnk` | #1953 |

Cross-cutting rules:

1. **`.lnk` filename-extension marks link-typed slots** (PR #1953).
   Both link-typed fixtures — UStar `linkname` (`evil.lnk\x00.tar`)
   and GNU `long-link` (`safe.lnk\x00rogue.tar`) — use `.lnk` to
   encode "this fixture probes a link-typed slot". Prose /
   trust-rhetoric prefixes (`trusted`, `safe`, `badpfx`) cover the
   non-link slots; `.txt` covers regular-file `name`.
2. **trailing-NUL invariant.** The smuggled value's last byte must
   be **non-NUL** — otherwise `stripTrailingNuls` (GNU long-name
   path) or the `findIdx? (· == 0)` interior-NUL guard's input
   invariant (UStar path) would erase the interior NUL the test
   intends. Observed in PR #1953's `"safe.lnk\x00rogue.tar"` (last
   byte `r`).

### Writer-side override hooks

The builder needs an injection path only for header fields whose
value is **transformed** by the writer:

- **Transformed slot → `Option`-typed override.** The UStar
  `prefix` slot is auto-derived from `entry.path` via `splitPath`
  inside `Tar.buildHeader`; the builder threads a
  `pathOverride : Option (String × String)` and bypasses
  `splitPath` when `some`. This is the **only** override hook in
  `Tar.buildHeader` today — see
  `scripts/build-ustar-malformed-fixtures.lean`'s
  `buildUstarPrefixNulInName` for the canonical use.
- **Verbatim-written slot → use the first-class entry field.**
  `linkname`, `uname`, `gname` are copied byte-for-byte by
  `Binary.writeString`, which accepts arbitrary bytes including
  interior NULs. Set `entry.linkname` / `entry.uname` /
  `entry.gname` directly — no override needed. PRs #1934 / #1944 /
  #1957 followed this pattern despite early planning notes
  proposing parallel `linknameOverride` / `unameOverride` /
  `gnameOverride` hooks; see the post-#1944 paired-review §E.7.g
  and post-#1957 feature-progress *Patterns / decisions* for the
  rationale.

## Assertion-writing pattern

The test in `ZipTest/*Fixtures.lean` is the other half of the fixture.
Match the sibling tests in the same file:

### For `IO`-returning paths (`Archive.extract`, `Tar.extract`, most FFI paths):

    let path : System.FilePath := "testdata/<subtree>/<fixture>"
    let result ← (<function> path ...).toBaseIO
    match result with
    | .ok _ => throw (IO.userError s!"expected error; got ok")
    | .error e =>
      let msg := e.toString
      unless msg.contains "<SUBSTRING>" do
        throw (IO.userError s!"unexpected error: {msg}")

This is the style already used by the central-directory limit test in
`ZipTest/Archive.lean`. Prefer it to `assertThrows` when the issue
explicitly calls for `.toBaseIO` + pattern match (e.g. #1561).

### For `assertThrows`-based tests (older Track E tests, `ZipTest/ZipFixtures.lean`):

    assertThrows "oversized-zip64-*.zip rejected"
      (Archive.list path) "local data span"

Match whatever the file already uses for consistency. Don't mix styles
within a single test file.

### Probe-then-finalise for substring choice

**Before committing**, run the fixture test once with a fake
substring like `<<PROBE>>`. `assertThrows` surfaces the actual error
text; `.toBaseIO` + `msg.contains` prints the mismatch. Copy the real
substring from the output and commit.

This catches the case where an earlier-landing PR adds a new check
that fires *before* the one you expected — which happened in #1554
when the new strict LH ZIP64 parse pre-empted
`oversized-zip64-uncompressed-size.zip`'s original `"size mismatch"`
assertion. Probe-first surfaces the new error; you update the
assertion instead of debugging "why does my fixture not match?".

## Error-substring choice

Use the short, source-file-linked substring rather than the full
error message. The project has several error-wording families — see
the `error-wording-catalogue` skill for the canonical match string for
each subsystem.

Common substrings:

- `"exceeds limit"` — FFI whole-buffer decoders and archive bomb paths.
- `"exceeds maximum size"` — native Inflate / Gzip overrun.
- `"local data span"` — `Archive.readEntryData` span check for
  oversized ZIP64 claims.
- `"unsafe path"` / `"unsafe symlink"` — `Binary.isPathSafe` rejects.
- `"truncated ZIP64 local extra field"` — strict LH ZIP64 parse.
- `"mismatch between CD and local header"` — CD/LH consistency check.

## Register the fixture

After landing the builder and fixtures, update:

1. **Test file** (`ZipTest/<Name>Fixtures.lean` or similar) —
   add the `assertThrows` / `.toBaseIO` block *and* add the new
   filenames to the cleanup loop (`for f in #[...] do`, `for d in
   #[...] do`). This is where #1544's rebase hit a conflict — the
   cleanup lists are hot.

   **maxRecDepth cap.** The cleanup `for` loops use large array
   literals that trip Lean's default `maxRecDepth` once they cross
   ~25 entries. Symptom: `maximum recursion depth has been reached`
   at the `for` line of the cleanup loop. Fix: add
   `set_option maxRecDepth 2048` at file scope — the same setting
   `ZipTest/Helpers.lean` and `ZipTest/Gzip.lean` already carry.
   First hit by PR #1761 (ZIP64 EOCD64 record-size).
2. **Checklist** (`plans/track-e-current-audit-checklist.md`) — move
   the bullet from `- [ ]` to `- [x]` and add the fixture names +
   closing PR number in parentheses.
3. **Inventory** (`SECURITY_INVENTORY.md`) — if the bullet appears
   here (it usually does for "Missing work" / "Recent wins"), update
   it in the *same* PR. Avoid drift between the two documents.

## Pitfalls

1. **Don't re-run the builder as part of CI.** The fixtures are
   checked in. `lake exe test` reads them; the builder script is
   manual (and only reachable via `lake env lean --run ...`).
2. **Don't introduce new typeflag constants in the builder.** Add them
   to `Zip/Tar.lean` (like `typeHardlink := 0x31` did in #1555) and
   import from there. Keeps the typeflag surface auditable.
3. **Don't skip the cleanup loop.** Test runs leave extracted files in
   temp directories; the cleanup loops in `ZipTest/*Fixtures.lean`
   must list every new fixture's extract-destination path.
4. **Don't forget the progress entry.** Record the fixture SHA-256s
   and the chosen error substring. The next worker who needs to
   regenerate the fixture or adjust the substring will grep for it.
5. **Don't inline a Python generator for tar.** Use Lean. Python is
   reserved for ZIP (where `struct` + `zlib` is the standard toolkit)
   or for inline one-shot recipes in test-file comments (which is the
   pattern for the 32-bit `oversized-compressed-size.zip` and ZIP64
   variants #1543/#1544 — see `ZipTest/ZipFixtures.lean`).
