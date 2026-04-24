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
- testdata/zip/malformed/zip64-extra-oversized-datasize.zip
- testdata/zip/malformed/cd-extra-overrun-datasize.zip
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
