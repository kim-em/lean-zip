"""Build CD/LH mismatch malformed-ZIP fixtures.

Each fixture wraps a single stored entry containing `b"hello\\n"`.  The
local header is mutated post-construction so that one field disagrees
with the central directory.  All fixtures are byte-stable (no
timestamps, no random padding).

Outputs:
- testdata/zip/malformed/cd-lh-method-mismatch.zip
- testdata/zip/malformed/cd-lh-size-mismatch.zip
- testdata/zip/malformed/cd-lh-uncompsize-mismatch.zip
- testdata/zip/malformed/cd-lh-crc-mismatch.zip
- testdata/zip/malformed/cd-lh-version-mismatch.zip
- testdata/zip/malformed/eocd-comment-trailing-garbage.zip
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

def make_eocd(cd_size, cd_offset):
    return struct.pack(
        "<IHHHHIIH",
        0x06054b50,  # signature
        0, 0,        # disk number, disk with CD
        1, 1,        # entries on disk, total entries
        cd_size,
        cd_offset,
        0,           # comment length
    )

def write(path, *, lh_method, cd_method, lh_comp, cd_comp,
          lh_uncomp=P, cd_uncomp=P, lh_crc=CRC,
          lh_version=20, cd_version=20, trailing_bytes=b""):
    lh = make_lh(lh_method, lh_comp, lh_uncomp, crc=lh_crc, version=lh_version)
    lhe = lh + NAME + PAYLOAD
    cd = make_cd(cd_method, cd_comp, cd_uncomp, version=cd_version)
    cde = cd + NAME
    eocd = make_eocd(len(cde), len(lhe))
    with open(path, "wb") as f:
        f.write(lhe + cde + eocd + trailing_bytes)
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
# Otherwise-valid archive with 6 bytes of trailing garbage appended
# after the EOCD (which has commentLength=0).  The backward EOCD-scan
# still finds the signature at its natural position, but the strict
# `pos + 22 + commentLength == fileSize` postcondition in
# `findEndOfCentralDir`'s caller fires on the 6-byte surplus and
# rejects the archive as a polyglot / trailing-garbage smuggling
# attempt.  The six bytes `PK_INJ` are deliberately chosen to NOT
# contain another `PK\x05\x06` EOCD signature (`_` is 0x5F, not 0x05)
# so the backward scan cannot be redirected to a different candidate.
write(
    os.path.join(OUT_DIR, "eocd-comment-trailing-garbage.zip"),
    lh_method=0, cd_method=0, lh_comp=P, cd_comp=P,
    trailing_bytes=b"PK_INJ",
)
