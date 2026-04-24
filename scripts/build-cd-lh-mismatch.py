"""Build CD/LH mismatch malformed-ZIP fixtures.

Each fixture wraps a single stored entry containing `b"hello\\n"`.  The
local header is mutated post-construction so that one field disagrees
with the central directory.  All fixtures are byte-stable (no
timestamps, no random padding).

The script also emits CD/EOCD consistency fixtures where the anomaly
lives in the EOCD record itself — `eocd-disknum-mismatch.zip` is one
such fixture, and the EOCD writer takes an optional `disk_start` kwarg
(default `0`, preserving byte-identity of the CD/LH fixtures above).

Outputs:
- testdata/zip/malformed/cd-lh-method-mismatch.zip
- testdata/zip/malformed/cd-lh-size-mismatch.zip
- testdata/zip/malformed/cd-lh-uncompsize-mismatch.zip
- testdata/zip/malformed/cd-lh-crc-mismatch.zip
- testdata/zip/malformed/cd-lh-version-mismatch.zip
- testdata/zip/malformed/eocd-disknum-mismatch.zip
"""
import os, struct, zlib

OUT_DIR = "testdata/zip/malformed"
PAYLOAD = b"hello\n"
NAME = b"hello.txt"
CRC = zlib.crc32(PAYLOAD) & 0xFFFFFFFF
N = len(NAME)
P = len(PAYLOAD)

def make_lh(method, comp_size, uncomp_size, crc=CRC, version=20):
    # PKZIP local file header (30 bytes).
    return struct.pack(
        "<IHHHHHIIIHH",
        0x04034b50,  # signature
        version,     # version needed
        0,           # flags
        method,      # compression method
        0,           # mod time
        0,           # mod date
        crc,
        comp_size,   # compressed size
        uncomp_size, # uncompressed size
        N,           # file name length
        0,           # extra field length
    )

def make_cd(method, comp_size, uncomp_size, version=20):
    # PKZIP central-directory file header (46 bytes).
    return struct.pack(
        "<IHHHHHHIIIHHHHHII",
        0x02014b50,  # signature
        20,          # version made by
        version,     # version needed
        0,           # flags
        method,      # compression method
        0,           # mod time
        0,           # mod date
        CRC,
        comp_size,
        uncomp_size,
        N,           # name length
        0,           # extra length
        0,           # comment length
        0,           # disk number start
        0,           # internal attrs
        0,           # external attrs
        0,           # local header offset
    )

def make_eocd(cd_size, cd_offset, *, disk_start=0, num_this_disk=0):
    # `disk_start` / `num_this_disk` default to 0 (single-disk).  The
    # defaults are load-bearing: they preserve byte-identity of the
    # CD/LH fixtures below, whose SHA-256s are recorded in progress
    # entries.  Only `eocd-disknum-mismatch.zip` exercises the
    # non-default branch.
    return struct.pack(
        "<IHHHHIIH",
        0x06054b50,  # signature
        num_this_disk,  # disk number (EOCD pos+4, UInt16)
        disk_start,     # disk where CD starts (EOCD pos+6, UInt16)
        1, 1,        # entries on disk, total entries
        cd_size,
        cd_offset,
        0,           # comment length
    )

def write(path, *, lh_method, cd_method, lh_comp, cd_comp,
          lh_uncomp=P, cd_uncomp=P, lh_crc=CRC,
          lh_version=20, cd_version=20,
          eocd_disk_start=0, eocd_num_this_disk=0):
    lh = make_lh(lh_method, lh_comp, lh_uncomp, crc=lh_crc, version=lh_version)
    lhe = lh + NAME + PAYLOAD
    cd = make_cd(cd_method, cd_comp, cd_uncomp, version=cd_version)
    cde = cd + NAME
    eocd = make_eocd(len(cde), len(lhe),
                     disk_start=eocd_disk_start,
                     num_this_disk=eocd_num_this_disk)
    with open(path, "wb") as f:
        f.write(lhe + cde + eocd)
    print(f"wrote {path} ({os.path.getsize(path)} bytes)")

os.makedirs(OUT_DIR, exist_ok=True)
# CD says method=8 (deflate); LH says method=0 (stored).
write(
    os.path.join(OUT_DIR, "cd-lh-method-mismatch.zip"),
    lh_method=0, cd_method=8, lh_comp=P, cd_comp=P,
)
# CD says compressedSize=6; LH says compressedSize=7.
# Both are stored (method=0); the strict CD/LH consistency check fires
# before the payload is actually read against the (CD-valued) span.
write(
    os.path.join(OUT_DIR, "cd-lh-size-mismatch.zip"),
    lh_method=0, cd_method=0, lh_comp=P + 1, cd_comp=P,
)
# CD says uncompressedSize=6; LH says uncompressedSize=7.
# Both stored (method=0); LH compressed size matches CD so the earlier
# `:607` compressedSize guard does not fire first.
write(
    os.path.join(OUT_DIR, "cd-lh-uncompsize-mismatch.zip"),
    lh_method=0, cd_method=0, lh_comp=P, cd_comp=P,
    lh_uncomp=P + 1, cd_uncomp=P,
)
# CD says crc32=CRC; LH says crc32=CRC ^ 0xFF.
# Both stored (method=0); sizes match on both sides so the earlier
# `:607` / `:610` guards don't fire first.
write(
    os.path.join(OUT_DIR, "cd-lh-crc-mismatch.zip"),
    lh_method=0, cd_method=0, lh_comp=P, cd_comp=P,
    lh_crc=CRC ^ 0xFF,
)
# CD says versionNeededToExtract=20; LH says versionNeededToExtract=45.
# Both stored (method=0); all other CD/LH fields match so the earlier
# method/flags guards don't fire first.  The check is one-sided —
# `LH > CD` is the attack direction (capability-smuggle: LH claims
# "ZIP64 features required" while CD feature-gates on `20`).  The
# converse (`CD=45, LH=20`) is legitimate per Go's `archive/zip` and
# CPython's `zipfile` when the LH sizes fit in 32 bits — tested by
# `testdata/zip/interop/go-zip64.zip` and is intentionally allowed.
write(
    os.path.join(OUT_DIR, "cd-lh-version-mismatch.zip"),
    lh_method=0, cd_method=0, lh_comp=P, cd_comp=P,
    lh_version=45, cd_version=20,
)
# EOCD disk-number anomaly: `diskWhereCDStarts=1` instead of `0`.  The
# CD/LH fields are otherwise consistent (stock hello.txt stored entry);
# `numberOfThisDisk` is left at `0` so only `diskWhereCDStarts` fires
# in the error message — deterministic attribution.  lean-zip only
# supports single-disk archives, so any nonzero disk-number field is
# rejected post-ZIP64-override (the fixture uses the standard EOCD,
# not ZIP64, so both widths of the check exercise the same branch).
write(
    os.path.join(OUT_DIR, "eocd-disknum-mismatch.zip"),
    lh_method=0, cd_method=0, lh_comp=P, cd_comp=P,
    eocd_disk_start=1,
)
