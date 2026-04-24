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


def make_eocd64(cd_size, cd_offset, record_size=44):
    # 56-byte EOCD64 record.  Stores real (non-sentinel) values for
    # all fields — we are forcing ZIP64 emission even though sizes fit
    # in 32 bits, so the reader's override branch fires.
    #
    # `record_size` is the APPNOTE §4.3.14 "size of zip64 end of central
    # directory record" field at bufPos+4.  Default `44` matches the v1
    # EOCD64 shape (56 bytes - 12 bytes for signature + size-field).
    # Override to forge a mismatch for the reader's record-size check.
    return struct.pack(
        "<IQHHIIQQQQ",
        0x06064b50,
        record_size,
        45, 45, 0, 0,  # versionMade, versionNeeded, thisDisk, diskCD
        1, 1,          # numEntriesThisDisk, totalEntries
        cd_size, cd_offset,
    )


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


def write_fixture(path, *, eocd64_record_size=44, **overrides):
    lh = make_lh()
    lhe = lh + NAME + PAYLOAD
    cd = make_cd()
    cde = cd + NAME
    cd_size = len(cde)
    cd_offset = len(lhe)
    eocd64 = make_eocd64(cd_size, cd_offset, record_size=eocd64_record_size)
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
# EOCD64 `size of this record` field (APPNOTE §4.3.14) carries the
# value `0` instead of the expected `44` for a v1 EOCD64.  Standard
# EOCD keeps the sentinel layout so the ZIP64-override sentinel check
# does not fire first — the record-size check must run on the EOCD64
# branch regardless of whether any override mismatch is present.
write_fixture(
    os.path.join(OUT_DIR, "zip64-eocd64-bad-recsize.zip"),
    eocd64_record_size=0,
)
