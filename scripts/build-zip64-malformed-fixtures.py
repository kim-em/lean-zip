"""Build ZIP64-boundary malformed fixtures.

Each fixture exercises a ZIP64 / standard-EOCD boundary violation.
The fixtures share a common `hello.txt` stored body; the writer emits a
valid ZIP64 EOCD64 + Locator pair and an otherwise-well-formed standard
EOCD whose sentinel fields are intentionally corrupted.  The reader's
sentinel check (APPNOTE §4.3.16) is relaxed to "sentinel or numeric
match" — so a fixture must encode a standard-EOCD value that is BOTH
non-sentinel AND numerically disagrees with the ZIP64 override to trip
the guard.

Outputs:
- testdata/zip/malformed/eocd-zip64-override-nosentinel.zip
- testdata/zip/malformed/zip64-eocd64-bad-recsize.zip
- testdata/zip/malformed/zip64-eocd64-versionmadeby-too-high.zip
- testdata/zip/malformed/zip64-eocd64-versionneeded-too-high.zip
- testdata/zip/malformed/zip64-eocd64-v2-record.zip
- testdata/zip/malformed/zip64-extra-oversized-datasize.zip
- testdata/zip/malformed/cd-extra-overrun-datasize.zip
- testdata/zip/malformed/cd-zip64-extra-duplicate.zip
- testdata/zip/malformed/lh-zip64-extra-duplicate.zip
"""
import os, struct, zlib

OUT_DIR = "testdata/zip/malformed"
PAYLOAD = b"hello\n"
NAME = b"hello.txt"
CRC = zlib.crc32(PAYLOAD) & 0xFFFFFFFF
N = len(NAME)
P = len(PAYLOAD)
SENTINEL_32 = 0xFFFFFFFF
SENTINEL_16 = 0xFFFF


def make_lh(crc=CRC, comp_size=P, uncomp_size=P):
    # Plain (non-ZIP64) local header — sizes fit in 32 bits.
    return struct.pack(
        "<IHHHHHIIIHH",
        0x04034b50, 20, 0, 0, 0, 0,
        crc, comp_size, uncomp_size, N, 0,
    )


def make_cd():
    # Plain (non-ZIP64) central-directory header — no ZIP64 extra field.
    return struct.pack(
        "<IHHHHHHIIIHHHHHII",
        0x02014b50, 20, 20, 0, 0, 0, 0,
        CRC, P, P, N, 0, 0, 0, 0, 0, 0,
    )


def make_eocd64(cd_size, cd_offset, record_size=44, version_made_by=45,
                version_needed=45, extensible_data=b""):
    # v1 EOCD64 record: 56 bytes (4-byte signature + 8-byte recSize field
    # + 44-byte v1 body).  When `extensible_data` is non-empty the record
    # is a v2-shape EOCD64 (APPNOTE §4.3.14.2) whose extensible data
    # sector follows the v1 body.  Stores real (non-sentinel) values for
    # the v1 fields — we are forcing ZIP64 emission even though sizes fit
    # in 32 bits, so the reader's override branch fires.
    #
    # `record_size` is the APPNOTE §4.3.14 "size of zip64 end of central
    # directory record" field at bufPos+4.  Default `44` matches the v1
    # EOCD64 shape (56 bytes - 12 bytes for signature + size-field).
    # Override to forge a mismatch for the reader's record-size check,
    # or set to `44 + len(extensible_data)` for an internally-consistent
    # v2-shape record whose claimed length matches its physical layout.
    #
    # `version_made_by` is the APPNOTE §4.4.2 `versionMadeBy` field at
    # bufPos+12.  Low byte encodes the ZIP spec version (APPNOTE-defined
    # values 1.0 through 6.3, encoded `10`..`63`), high byte encodes the
    # host OS code.  Default `45` matches lean-zip's writer emission
    # (low byte 45 for spec version 4.5 = ZIP64; writer actually emits
    # host OS 3 / `0x032D` but `45` suffices for fixtures not probing
    # the host-OS byte).  Override to forge a low byte > 63 for the
    # reader's versionMadeBy upper-bound check.
    #
    # `version_needed` is the APPNOTE §4.4.3.2 `versionNeededToExtract`
    # field at bufPos+14.  Encodes the minimum ZIP spec version needed
    # to interpret the EOCD64 record.  Default `45` matches lean-zip's
    # writer emission (ZIP64 support requires at least spec version
    # 4.5).  Override to forge a value > 63 for the reader's
    # versionNeededToExtract upper-bound check.
    #
    # `extensible_data` is the APPNOTE §4.3.14.2 "zip64 extensible data
    # sector" — appended to the v1 body, making the physical record
    # `56 + len(extensible_data)` bytes.  Default empty (v1 shape).
    v1 = struct.pack(
        "<IQHHIIQQQQ",
        0x06064b50,
        record_size,
        version_made_by, version_needed, 0, 0,  # versionMade, versionNeeded, thisDisk, diskCD
        1, 1,          # numEntriesThisDisk, totalEntries
        cd_size, cd_offset,
    )
    return v1 + extensible_data


def make_locator(eocd64_offset):
    return struct.pack(
        "<IIQI",
        0x07064b50, 0, eocd64_offset, 1,
    )


def make_eocd(*,
              cd_size=SENTINEL_32, cd_offset=SENTINEL_32,
              total_entries=SENTINEL_16,
              this_disk=SENTINEL_16, disk_cd=SENTINEL_16,
              entries_this_disk=SENTINEL_16):
    return struct.pack(
        "<IHHHHIIH",
        0x06054b50,
        this_disk, disk_cd, entries_this_disk, total_entries,
        cd_size, cd_offset, 0,
    )


def write_fixture(path, *, eocd64_record_size=44, eocd64_version_made_by=45,
                  eocd64_version_needed=45, eocd64_extensible_data=b"",
                  **overrides):
    lh = make_lh()
    lhe = lh + NAME + PAYLOAD
    cd = make_cd()
    cde = cd + NAME
    cd_size = len(cde)
    cd_offset = len(lhe)
    eocd64 = make_eocd64(
        cd_size, cd_offset,
        record_size=eocd64_record_size,
        version_made_by=eocd64_version_made_by,
        version_needed=eocd64_version_needed,
        extensible_data=eocd64_extensible_data,
    )
    eocd64_offset = len(lhe) + len(cde)
    locator = make_locator(eocd64_offset)
    eocd = make_eocd(**overrides)
    with open(path, "wb") as f:
        f.write(lhe + cde + eocd64 + locator + eocd)
    print(f"wrote {path} ({os.path.getsize(path)} bytes)")


os.makedirs(OUT_DIR, exist_ok=True)
# Standard EOCD carries a real `cdOffset` (42 bytes — chosen so it
# numerically disagrees with the ZIP64 value of 45, avoiding the
# "numeric match" relaxation in the reader's sentinel check).
# All other fields remain at their sentinels.
write_fixture(
    os.path.join(OUT_DIR, "eocd-zip64-override-nosentinel.zip"),
    cd_offset=42,
)
# Per-slot sibling of the `cdOffset`-slot fixture above: the standard
# EOCD carries a real `cdSize` (99 bytes — chosen so it numerically
# disagrees with the ZIP64 value of `len(cde) = 55`, avoiding the
# "numeric match" relaxation).  All other slots stay at their sentinels
# so the relaxed sentinel arm passes for `cdOffset` / `totalEntries` /
# `numberOfThisDisk` / `diskWhereCDStarts` / `numEntriesThisDisk`, and
# the `cdSize` sub-check at [Zip/Archive.lean:396] is the one that
# trips.  Closes the per-slot `cdSize` regression coverage of the
# 6-field EOCD ZIP64-override mismatch family.
write_fixture(
    os.path.join(OUT_DIR, "eocd-zip64-override-cdsize-mismatch.zip"),
    cd_size=99,
)
# Per-slot sibling of the `cdOffset`/`cdSize`-slot fixtures above: the
# standard EOCD carries a real `totalEntries=99` (a UInt16 value that
# is neither the APPNOTE §4.3.16 sentinel `0xFFFF` nor numerically
# equal to the ZIP64 override of `1`, the actual archive's entry
# count).  All other slots stay at their sentinels so the relaxed
# sentinel arm passes for `cdSize` / `cdOffset` / `numberOfThisDisk` /
# `diskWhereCDStarts` / `numEntriesThisDisk`, and the `totalEntries`
# sub-check at [Zip/Archive.lean:402] is the one that trips.  Closes
# the per-slot `totalEntries` regression coverage of the 6-field EOCD
# ZIP64-override mismatch family — `totalEntries` is a particularly
# notable smuggling vector because it controls the entry-iteration
# loop of the CD walker, so a relaxed reader that trusts a smuggled
# value walks more or fewer CD entries than the strict reader.
write_fixture(
    os.path.join(OUT_DIR, "eocd-zip64-override-totalentries-mismatch.zip"),
    total_entries=99,
)
# EOCD64 `size of this record` field (APPNOTE §4.3.14) carries the
# value `0` instead of the expected `44` for a v1 EOCD64.  Standard
# EOCD keeps the sentinel layout so the ZIP64-override sentinel check
# does not fire first — the record-size check must run on the EOCD64
# branch regardless of whether any override mismatch is present.
write_fixture(
    os.path.join(OUT_DIR, "zip64-eocd64-bad-recsize.zip"),
    eocd64_record_size=0,
)
# EOCD64 `versionMadeBy` field (APPNOTE §4.4.2.1 / §4.4.2.2) carries
# `0x0340` — low byte `0x40 = 64`, exceeding the APPNOTE-defined cap
# of `63` (spec version 6.3).  High byte `3` = Unix host OS, matching
# lean-zip's writer.  Standard EOCD keeps the sentinel layout so the
# ZIP64-override sentinel check does not fire first.  Record-size is
# the valid `44`, so the record-size check passes before the new
# versionMadeBy guard fires.  Sibling of per-entry CD+4 fixture
# `cd-entry-versionmadeby-too-high.zip` (issue #1812 / PR #1820):
# together they close the versionMadeBy upper-bound dimension across
# both ZIP layers (archive-level EOCD64 and per-entry CD+4).
write_fixture(
    os.path.join(OUT_DIR, "zip64-eocd64-versionmadeby-too-high.zip"),
    eocd64_version_made_by=0x0340,
)
# EOCD64 `versionNeededToExtract` field (APPNOTE §4.4.3.2, at bufPos+14)
# carries `0x00FF` — spec version 25.5, well beyond the APPNOTE-defined
# cap of `63` (spec version 6.3).  Standard EOCD keeps the sentinel
# layout so the ZIP64-override sentinel check does not fire first.
# Record-size and versionMadeBy pass the preceding guards (defaults 44
# and 45), so the new versionNeededToExtract upper-bound guard is the
# one that trips.  Sibling of the lower-bound `≥ 45` fixture
# `zip64-eocd64-version-low.zip` (issue #1758 / PR #1764): together
# they close the EOCD64 `versionNeededToExtract` two-sided-bound
# dimension.  Archive-level analog of the per-entry CD +6 upper bound
# (PR #1807).
write_fixture(
    os.path.join(OUT_DIR, "zip64-eocd64-versionneeded-too-high.zip"),
    eocd64_version_needed=0x00FF,
)
# EOCD64 v2-shape record (APPNOTE §4.3.14.2).  The v2 EOCD64 extends the
# v1 56-byte record with a "zip64 extensible data sector" tied to the
# APPNOTE strong-encryption (SES) extension; the extensible sector
# carries fields such as `compositeSize` + `encryptionAlgID` and makes
# the on-disk record `56 + N` bytes for an N-byte sector.  Per APPNOTE
# §4.3.14 the `size of this record` field encodes
# `SizeOfFixedFields + SizeOfVariableData - 12`, so a v2 record with a
# 16-byte extensible sector declares `recSize = 56 + 16 - 12 = 60`.
#
# lean-zip does not implement strong encryption and so cannot consume
# v2 EOCD64 records; the existing record-size guard
# (`unless recSize == 44` at
# [Zip/Archive.lean:343](/home/kim/lean-zip/Zip/Archive.lean:343))
# rejects them by falling outside the v1-only `44` expectation.  This
# fixture is an *internally-consistent* v2-shape probe: the claimed
# `recSize=60` matches the 72-byte physical record layout
# (`4 signature + 8 recSize + 44 v1 body + 16 extensible sector`), so
# a reader that trusts the declared length and parses per APPNOTE v2
# semantics would *accept* the archive.  Sibling of
# `zip64-eocd64-bad-recsize.zip` (PR #1761), which probes the same
# guard at the `recSize=0` boundary; this fixture pins the rejection
# behaviour specifically against the APPNOTE-documented v2 shape.
#
# The extensible sector payload is 16 zero bytes — a plausible v2 shape
# for a reader that expects `compositeSize` + `encryptionAlgID` fields
# but does not validate their contents.  The fixture is not exercising
# SES semantics; it documents v2-record rejection at the entry guard.
#
# Archive-layout invariant (PR #1856, `bufPos + 56 ≤ pos - 20`) passes
# because the 72-byte physical record places the Locator at
# `bufPos + 72 > bufPos + 56`, so the layout guard does not fire first
# and the record-size check is the one that rejects.
write_fixture(
    os.path.join(OUT_DIR, "zip64-eocd64-v2-record.zip"),
    eocd64_record_size=60,
    eocd64_extensible_data=b"\x00" * 16,
)


def write_zip64_overlap_locator_fixture(path):
    # APPNOTE §4.3.6 pins the ZIP64 archive layout as
    # `[LH+data]* [CD] [EOCD64] [Locator] [EOCD]`, so a legitimate archive
    # satisfies `eocd64Offset + 56 <= locatorPos = eocdPos - 20` — the
    # 56-byte v1 EOCD64 record must end strictly before the Locator
    # begins.  This fixture emits a *truncated* 48-byte EOCD64 "record"
    # whose trailing 8 bytes would be the `cdOffset` field (APPNOTE
    # §4.3.14 at `bufPos + 48`) and places the Locator immediately after
    # — so a reader that trusts the layout (and reads the full 56-byte
    # record at the claimed `eocd64Offset`) silently overlaps 8 bytes of
    # the Locator, reading `sigLocator64` + `diskWithZip64EOCD` as the
    # EOCD64's `cdOffset`.
    #
    # The Locator's `eocd64Offset` points to the start of the 48-byte
    # block (`locatorPos - 48`), so `eocd64Offset + 56 = locatorPos + 8
    # > locatorPos` trips the archive-layout-invariant guard.  Standard
    # EOCD keeps sentinel values so the ZIP64-override sentinel check
    # does not fire first; the `sigEOCD64` check at the claimed offset
    # passes because the synthetic block starts with a valid signature.
    # Record-size (44), versionMadeBy (45), and versionNeededToExtract
    # (45) are all stored as valid values so the subsequent guards
    # would pass — the new layout-invariant guard is the *only* thing
    # that rejects this archive.
    #
    # Archive-level macro sibling: `cdOffset + cdSize <= eocdPos`
    # (issue #1799 / in-flight PR #1809).  Per-entry micro sibling:
    # `localOffset + 30 <= cdOffset` (PR #1813).  Together the three
    # invariants close the ZIP archive-layout dimension.
    lh = make_lh()
    lhe = lh + NAME + PAYLOAD
    cd = make_cd()
    cde = cd + NAME
    # Full 56-byte EOCD64, then we drop the last 8 bytes (cdOffset field)
    # so the synthetic record is only 48 bytes.  Trailing reader will
    # spill the final 8 bytes into the Locator.
    eocd64_full = make_eocd64(len(cde), len(lhe))
    assert len(eocd64_full) == 56
    eocd64_truncated = eocd64_full[:48]
    eocd64_offset = len(lhe) + len(cde)          # points at sigEOCD64
    locator_pos   = eocd64_offset + 48            # 8 bytes short of 56
    # Locator claims eocd64Offset = locator_pos - 48:
    locator = make_locator(eocd64_offset)
    eocd = make_eocd(
        cd_size=len(cde), cd_offset=len(lhe),
        total_entries=1, entries_this_disk=1,
        this_disk=0, disk_cd=0,
    )
    with open(path, "wb") as f:
        f.write(lhe + cde + eocd64_truncated + locator + eocd)
    print(f"wrote {path} ({os.path.getsize(path)} bytes)")


write_zip64_overlap_locator_fixture(
    os.path.join(OUT_DIR, "zip64-eocd64-overlap-locator.zip"),
)


def make_lh_zip64(comp_sentinel=True):
    # Local header whose `stdCompSize` is the ZIP64 sentinel so the file is
    # parseable as a ZIP64-per-entry archive without needing an outer
    # EOCD64.  The LH ZIP64 extra block matches the CD's oversized-dataSize
    # layout so the LH strict-parse (if reached) sees the same anomaly.
    comp = SENTINEL_32 if comp_sentinel else P
    return struct.pack(
        "<IHHHHHIIIHH",
        0x04034b50, 45, 0, 0, 0, 0,
        CRC, comp, P, N, 20,
    )


def make_cd_zip64():
    # CD entry whose `stdCompSize` is the ZIP64 sentinel.  nameLen=9,
    # extraLen=20 (4-byte header + 16-byte dataSize-claimed block).
    return struct.pack(
        "<IHHHHHHIIIHHHHHII",
        0x02014b50, (3 << 8) | 45, 45, 0, 0, 0, 0,
        CRC, SENTINEL_32, P, N, 20, 0, 0, 0, 0, 0,
    )


def make_zip64_extra_oversized():
    # APPNOTE §4.5.3: ZIP64 extra-field `Data Size` is exactly `8 * N`
    # where N is the count of standard 32-bit fields set to the
    # `0xFFFFFFFF` sentinel.  Here only `stdCompSize` is a sentinel, so N=1
    # and the compliant `dataSize` is 8.  This fixture declares
    # `dataSize=16` and supplies 8 bytes of attacker-chosen slack
    # (`0xDEADBEEFCAFEBABE`) past the single legitimate `compSize` UInt64.
    # A lenient parser silently discards the slack; a strict parser
    # (post-PR #TBD) rejects with "malformed ZIP64 extra field".
    return struct.pack(
        "<HHQQ", 0x0001, 16, P, 0xDEADBEEFCAFEBABE,
    )


def write_zip64_extra_oversized_fixture(path):
    lh = make_lh_zip64()
    lh_ex = make_zip64_extra_oversized()
    lhe = lh + NAME + lh_ex + PAYLOAD
    cd = make_cd_zip64()
    cd_ex = make_zip64_extra_oversized()
    cde = cd + NAME + cd_ex
    eocd = make_eocd(
        cd_size=len(cde), cd_offset=len(lhe),
        total_entries=1, entries_this_disk=1,
        this_disk=0, disk_cd=0,
    )
    with open(path, "wb") as f:
        f.write(lhe + cde + eocd)
    print(f"wrote {path} ({os.path.getsize(path)} bytes)")


write_zip64_extra_oversized_fixture(
    os.path.join(OUT_DIR, "zip64-extra-oversized-datasize.zip"),
)


def make_lh_extra_overrun(extra_len):
    # Plain (non-ZIP64) local header with an `extraLen` that matches the
    # length of the malformed extra-data sub-field header below.  The
    # outer length is *honest*; the inner sub-field header lies about its
    # payload length.
    return struct.pack(
        "<IHHHHHIIIHH",
        0x04034b50, 20, 0, 0, 0, 0,
        CRC, P, P, N, extra_len,
    )


def make_cd_extra_overrun(extra_len):
    # Plain CD header with an honest outer `extraLen` that matches the
    # length of the malformed extra-data below.
    return struct.pack(
        "<IHHHHHHIIIHHHHHII",
        0x02014b50, 20, 20, 0, 0, 0, 0,
        CRC, P, P, N, extra_len, 0, 0, 0, 0, 0,
    )


def make_overrun_extra():
    # APPNOTE §4.5: an extra-data sub-field is
    # `[headerId:UInt16][dataSize:UInt16][payload:dataSize bytes]`,
    # iterated until the extra-data is exhausted.  Here headerId=0x5455
    # (extended-timestamp — a plausible legitimate sub-field), but the
    # declared `dataSize=0xFF` (255 bytes) far exceeds the remaining
    # `extraLen - 4 = 4` bytes of payload buffer.  A strict parser
    # rejects the archive; the pre-PR lean-zip silently `break`s inside
    # `parseZip64Extra` — and since no ZIP64 sentinel is set the caller
    # does not even invoke `parseZip64Extra`, leaving the anomaly
    # entirely invisible.
    return struct.pack(
        "<HH4s", 0x5455, 0xFF, b"\x00\x00\x00\x00",
    )


def write_cd_extra_overrun_fixture(path):
    extra = make_overrun_extra()
    extra_len = len(extra)
    lh = make_lh_extra_overrun(extra_len)
    lhe = lh + NAME + extra + PAYLOAD
    cd = make_cd_extra_overrun(extra_len)
    cde = cd + NAME + extra
    eocd = make_eocd(
        cd_size=len(cde), cd_offset=len(lhe),
        total_entries=1, entries_this_disk=1,
        this_disk=0, disk_cd=0,
    )
    with open(path, "wb") as f:
        f.write(lhe + cde + eocd)
    print(f"wrote {path} ({os.path.getsize(path)} bytes)")


write_cd_extra_overrun_fixture(
    os.path.join(OUT_DIR, "cd-extra-overrun-datasize.zip"),
)


# === Duplicate-ZIP64-extra fixtures (issue #1781) =====================
#
# APPNOTE §4.5 forbids more than one instance of any registered extra-field
# header ID per entry's extra-data area.  Two ZIP64 (headerId `0x0001`)
# blocks with different sentinel-resolved sizes/offsets are a parser-
# differential smuggling vector: a "first-wins" reader (lean-zip pre-fix)
# and a "last-wins" reader disagree on the resolved values for the same
# bytes.  These fixtures emit single-entry archives whose `stdUncompSize`
# is the ZIP64 sentinel (`0xFFFFFFFF`) — exercising the duplicate-detect
# guard at the CD parse site (`cd-...`) and the LH read site (`lh-...`).


def make_lh_uncomp_sentinel(comp_size, extra_len):
    """Local header with `stdUncompSize = 0xFFFFFFFF` so the LH ZIP64
    parse path is reached.  `extra_len` is the byte length of the extra
    block that follows the name."""
    return struct.pack(
        "<IHHHHHIIIHH",
        0x04034b50, 45, 0, 0, 0, 0,
        CRC, comp_size, SENTINEL_32, N, extra_len,
    )


def make_cd_uncomp_sentinel(comp_size, extra_len):
    """CD entry with `stdUncompSize = 0xFFFFFFFF` so the CD ZIP64 parse
    path is reached.  `extra_len` is the byte length of the extra block
    that follows the name in the CD entry."""
    return struct.pack(
        "<IHHHHHHIIIHHHHHII",
        0x02014b50, (3 << 8) | 45, 45, 0, 0, 0, 0,
        CRC, comp_size, SENTINEL_32, N, extra_len, 0, 0, 0, 0, 0,
    )


def make_zip64_extra_uncomp_only(uncomp):
    """Single 0x0001 block carrying just the 8-byte uncompSize field —
    the layout `parseZip64Extra` expects when only `stdUncompSize` is at
    sentinel.  `dataSize = 8 = 8 * N` for N = 1."""
    return struct.pack("<HHQ", 0x0001, 8, uncomp)


def make_zip64_extra_duplicate_uncomp(uncomp1, uncomp2):
    """Two 0x0001 blocks, each carrying an 8-byte uncompSize.  APPNOTE
    §4.5 rejects this; lean-zip's `hasDuplicateZip64Extra` returns true."""
    return (
        struct.pack("<HHQ", 0x0001, 8, uncomp1)
        + struct.pack("<HHQ", 0x0001, 8, uncomp2)
    )


def write_dup_fixture(path, *, dup_in_cd, dup_in_lh):
    """Write a single-entry archive whose CD and/or LH extra-data carries
    duplicate 0x0001 blocks.  Either flag (or both) selects which parse
    site trips the new guard; the other side carries a single valid
    0x0001 so its parser-differential layer is well-formed."""
    cd_extra = (make_zip64_extra_duplicate_uncomp(P, P + 100)
                if dup_in_cd else make_zip64_extra_uncomp_only(P))
    lh_extra = (make_zip64_extra_duplicate_uncomp(P, P + 100)
                if dup_in_lh else make_zip64_extra_uncomp_only(P))
    lh = make_lh_uncomp_sentinel(P, len(lh_extra))
    lhe = lh + NAME + lh_extra + PAYLOAD
    cd = make_cd_uncomp_sentinel(P, len(cd_extra))
    cde = cd + NAME + cd_extra
    eocd = make_eocd(
        cd_size=len(cde), cd_offset=len(lhe),
        total_entries=1, entries_this_disk=1,
        this_disk=0, disk_cd=0,
    )
    with open(path, "wb") as f:
        f.write(lhe + cde + eocd)
    print(f"wrote {path} ({os.path.getsize(path)} bytes)")


# CD-side: CD has duplicate 0x0001; LH has a single valid 0x0001 so the
# error attributes the fault to the CD parse site (which fires first).
write_dup_fixture(
    os.path.join(OUT_DIR, "cd-zip64-extra-duplicate.zip"),
    dup_in_cd=True, dup_in_lh=False,
)
# LH-side: CD has a single valid 0x0001 so CD parse passes; LH has the
# duplicate so the LH read-site guard (with the `local extra` wording)
# fires.
write_dup_fixture(
    os.path.join(OUT_DIR, "lh-zip64-extra-duplicate.zip"),
    dup_in_cd=False, dup_in_lh=True,
)
