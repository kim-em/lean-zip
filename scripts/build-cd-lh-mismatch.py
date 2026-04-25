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
- testdata/zip/malformed/eocd-numentries-thisdisk-mismatch.zip
- testdata/zip/malformed/cd-entry-disknum-mismatch.zip
- testdata/zip/malformed/cd-lh-modtime-mismatch.zip
- testdata/zip/malformed/cd-stored-size-mismatch.zip
- testdata/zip/malformed/cd-bad-method-early.zip
- testdata/zip/malformed/cd-entry-internal-attrs-reserved.zip
- testdata/zip/malformed/cd-patched-data-flag.zip
- testdata/zip/malformed/cd-nul-in-name.zip
- testdata/zip/malformed/cd-path-unsafe.zip
- testdata/zip/malformed/cd-deflate-zero-compsize.zip
- testdata/zip/malformed/cd-bad-lh-signature.zip
- testdata/zip/malformed/cd-entry-past-cdend.zip
"""
import os, struct, zlib

OUT_DIR = "testdata/zip/malformed"
PAYLOAD = b"hello\n"
NAME = b"hello.txt"
CRC = zlib.crc32(PAYLOAD) & 0xFFFFFFFF
N = len(NAME)
P = len(PAYLOAD)

def make_lh(method, comp_size, uncomp_size, crc=CRC, version=20,
            lh_mod_time=0, lh_mod_date=0, lh_flags=0,
            name_bytes=None, lh_signature=0x04034b50):
    # PKZIP local file header (30 bytes).
    # `lh_mod_time` / `lh_mod_date` default to `0` — preserving
    # byte-identity of fixtures produced before the modtime/date
    # kwargs were threaded through.  Only
    # `cd-lh-modtime-mismatch.zip` exercises the non-default branch.
    # `lh_flags` defaults to `0`; the default is load-bearing for every
    # fixture whose LH flag word is zero.  Only
    # `cd-patched-data-flag.zip` exercises the non-default branch
    # (mirroring `cd_flags` on both sides to isolate the new guard).
    # `name_bytes` defaults to `None`, meaning "derive from the module
    # constant `NAME`".  The default preserves byte-identity of every
    # existing fixture (only `cd-nul-in-name.zip` passes a custom value
    # with embedded NUL).  The derived length is written into the
    # `name length` UInt16 slot, so a caller-supplied `name_bytes` is
    # free to differ in length from `NAME`.
    # `lh_signature` defaults to `0x04034b50` (`sigLocal` per APPNOTE
    # §4.3.7).  The default is load-bearing for every existing fixture;
    # only `cd-bad-lh-signature.zip` exercises the non-default branch
    # (`0xCAFEBABE`) to trip the late LH-signature guard at
    # Zip/Archive.lean:1081.
    nb = NAME if name_bytes is None else name_bytes
    return struct.pack(
        "<IHHHHHIIIHH",
        lh_signature,  # signature
        version,     # version needed
        lh_flags,    # flags
        method,      # compression method
        lh_mod_time, # mod time
        lh_mod_date, # mod date
        crc,
        comp_size,   # compressed size
        uncomp_size, # uncompressed size
        len(nb),     # file name length
        0,           # extra field length
    )

def make_cd(method, comp_size, uncomp_size, version=20, disk_number_start=0,
            cd_mod_time=0, cd_mod_date=0, local_hdr_offset=0,
            internal_attrs=0, cd_flags=0, name_bytes=None, cd_crc=None,
            comment_length=0):
    # PKZIP central-directory file header (46 bytes).
    # `disk_number_start` defaults to 0 (single-disk).  The default is
    # load-bearing: it preserves byte-identity of the existing fixtures.
    # Only `cd-entry-disknum-mismatch.zip` exercises the non-default branch.
    # `cd_mod_time` / `cd_mod_date` default to `0` — see the parallel
    # defaults on `make_lh` above.  Only `cd-lh-modtime-mismatch.zip`
    # exercises the non-default branch.
    # `local_hdr_offset` defaults to `0` (legitimate LH-at-file-start
    # layout).  The default is load-bearing for every fixture whose LH
    # sits at file offset 0; only
    # `cd-entry-localoffset-past-cdstart.zip` exercises the non-default
    # branch.
    # `internal_attrs` defaults to `0` (APPNOTE §4.4.10 writer-zero
    # invariant, matching lean-zip's `Binary.zeros`-initialised CD
    # header).  The default is load-bearing: only
    # `cd-entry-internal-attrs-reserved.zip` exercises the non-default
    # branch (a reserved-bit value outside the bit-0 text-flag allowance).
    # `cd_flags` defaults to `0`; the default is load-bearing for every
    # fixture whose CD flag word is zero.  Only
    # `cd-patched-data-flag.zip` exercises the non-default branch.
    # `name_bytes` defaults to `None`, meaning "derive from the module
    # constant `NAME`".  Parallel to the same kwarg on `make_lh`:
    # preserves byte-identity of every existing fixture; only
    # `cd-nul-in-name.zip` passes a custom value with embedded NUL.
    # `cd_crc` defaults to `None`, meaning "use the module-level `CRC`
    # (the CRC32 of `PAYLOAD = b"hello\n"`)".  The default is
    # load-bearing: it preserves byte-identity of every existing
    # fixture whose CD `crc32` field carries the payload CRC.  Only
    # `cd-empty-entry-crc-nonzero.zip` exercises the non-default
    # branch (`cd_crc=0xDEADBEEF` alongside `cd_uncomp=0` — the
    # empty-entry CRC invariant violation).
    # `comment_length` defaults to `0` (APPNOTE §4.4.10 `file comment
    # length` matching the absent comment payload — lean-zip's writer
    # never emits a CD entry comment).  The default is load-bearing:
    # it preserves byte-identity of every existing fixture.  Only
    # `cd-entry-past-cdend.zip` exercises the non-default branch — a
    # crafted comment_length whose declared 16-byte size pushes
    # `46 + nameLen + extraLen + commentLen` past the EOCD-declared
    # `cdEnd` without any matching comment bytes physically present.
    nb = NAME if name_bytes is None else name_bytes
    cc = CRC if cd_crc is None else cd_crc
    return struct.pack(
        "<IHHHHHHIIIHHHHHII",
        0x02014b50,  # signature
        20,          # version made by
        version,     # version needed
        cd_flags,    # flags
        method,      # compression method
        cd_mod_time, # mod time
        cd_mod_date, # mod date
        cc,
        comp_size,
        uncomp_size,
        len(nb),     # name length
        0,           # extra length
        comment_length,  # comment length
        disk_number_start,  # disk number start (CD offset 34, UInt16)
        internal_attrs,     # internal attrs   (CD offset 36, UInt16)
        0,           # external attrs
        local_hdr_offset,  # local header offset (CD offset 42, UInt32)
    )

def make_eocd(cd_size, cd_offset, *, disk_start=0, num_this_disk=0,
              entries_this_disk=None, total_entries=1):
    # `disk_start` / `num_this_disk` default to 0 (single-disk).  The
    # defaults are load-bearing: they preserve byte-identity of the
    # CD/LH fixtures below, whose SHA-256s are recorded in progress
    # entries.  Only `eocd-disknum-mismatch.zip` exercises the
    # non-default branch.
    # `entries_this_disk` defaults to `total_entries` so the
    # `numEntriesThisDisk` field equals `totalEntries` for single-disk
    # archives — preserving byte-identity of the existing fixtures.
    # Only `eocd-numentries-thisdisk-mismatch.zip` exercises the
    # non-default branch.
    if entries_this_disk is None:
        entries_this_disk = total_entries
    return struct.pack(
        "<IHHHHIIH",
        0x06054b50,  # signature
        num_this_disk,  # disk number (EOCD pos+4, UInt16)
        disk_start,     # disk where CD starts (EOCD pos+6, UInt16)
        entries_this_disk,  # entries on disk (EOCD pos+8, UInt16)
        total_entries,      # total entries     (EOCD pos+10, UInt16)
        cd_size,
        cd_offset,
        0,           # comment length
    )

def write(path, *, lh_method, cd_method, lh_comp, cd_comp,
          lh_uncomp=P, cd_uncomp=P, lh_crc=CRC, cd_crc=None,
          lh_version=20, cd_version=20,
          lh_mod_time=0, lh_mod_date=0,
          cd_mod_time=0, cd_mod_date=0,
          cd_disk_number_start=0,
          cd_local_hdr_offset=0,
          cd_internal_attrs=0,
          lh_flags=0, cd_flags=0,
          name_bytes=None, payload=None,
          eocd_disk_start=0, eocd_num_this_disk=0,
          eocd_entries_this_disk=None, eocd_total_entries=1,
          lh_signature=0x04034b50,
          cd_comment_length=0):
    # `name_bytes` defaults to `None`, meaning "derive from the module
    # constant `NAME`".  The default preserves byte-identity of every
    # existing fixture (only `cd-nul-in-name.zip` exercises the non-default
    # branch with `b"a\x00b.txt"`).  Both the LH and CD use the same
    # `name_bytes`, keeping the CD/LH name-bytes consistency invariant
    # intact when issue #1722's guard lands.
    # `payload` defaults to `None`, meaning "derive from the module
    # constant `PAYLOAD = b"hello\n"`".  The default preserves
    # byte-identity of every existing fixture; only
    # `cd-empty-entry-crc-nonzero.zip` passes `payload=b""` (together
    # with `lh_comp=cd_comp=lh_uncomp=cd_uncomp=0`) to exercise the
    # empty-entry CRC invariant.
    # `cd_crc` defaults to `None` (→ module-level `CRC`).  Plumbed to
    # `make_cd` for the empty-entry CRC invariant; see the `make_cd`
    # docstring.
    nb = NAME if name_bytes is None else name_bytes
    pl = PAYLOAD if payload is None else payload
    lh = make_lh(lh_method, lh_comp, lh_uncomp, crc=lh_crc, version=lh_version,
                 lh_mod_time=lh_mod_time, lh_mod_date=lh_mod_date,
                 lh_flags=lh_flags, name_bytes=name_bytes,
                 lh_signature=lh_signature)
    lhe = lh + nb + pl
    cd = make_cd(cd_method, cd_comp, cd_uncomp, version=cd_version,
                 disk_number_start=cd_disk_number_start,
                 cd_mod_time=cd_mod_time, cd_mod_date=cd_mod_date,
                 local_hdr_offset=cd_local_hdr_offset,
                 internal_attrs=cd_internal_attrs,
                 cd_flags=cd_flags, name_bytes=name_bytes, cd_crc=cd_crc,
                 comment_length=cd_comment_length)
    cde = cd + nb
    eocd = make_eocd(len(cde), len(lhe),
                     disk_start=eocd_disk_start,
                     num_this_disk=eocd_num_this_disk,
                     entries_this_disk=eocd_entries_this_disk,
                     total_entries=eocd_total_entries)
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
# EOCD entry-count anomaly: `numEntriesThisDisk=2` while `totalEntries=1`.
# Single-disk archives must have both fields equal (writer-side at
# Zip/Archive.lean:146-147, :160-161).  The CD itself contains one
# entry, so the `totalEntries` check would pass (1 == 1); only the
# `numEntriesThisDisk` sibling disagrees.  Companion to
# `eocd-numentries-mismatch.zip` (which fires the `totalEntries` check).
write(
    os.path.join(OUT_DIR, "eocd-numentries-thisdisk-mismatch.zip"),
    lh_method=0, cd_method=0, lh_comp=P, cd_comp=P,
    eocd_entries_this_disk=2, eocd_total_entries=1,
)
# CD-entry disk-number anomaly: the per-entry `diskNumberStart` field at
# CD offset +34 is set to `7` (any non-zero value works; `7` is a
# deterministic non-zero that's clearly not a sentinel).  Single-disk
# archives — the only shape lean-zip supports — must have this field at
# `0` per APPNOTE §4.4.11.  Companion to `eocd-disknum-mismatch.zip`,
# which exercises the archive-level EOCD disk-number fields.  Together
# they close the full disk-number smuggling dimension.
write(
    os.path.join(OUT_DIR, "cd-entry-disknum-mismatch.zip"),
    lh_method=0, cd_method=0, lh_comp=P, cd_comp=P,
    cd_disk_number_start=7,
)
# CD/LH lastModTime anomaly: LH mod-time `0x1234` while CD mod-time
# remains `0` (writer-side default).  Single-dimension mismatch — only
# the time field disagrees, so error attribution is unambiguous.  The
# check fires regardless of bit 3 (data descriptor) because APPNOTE
# §4.4.6 gates bit 3 on crc/compSize/uncompSize only; the timestamp
# fields are always carried in the LH.
write(
    os.path.join(OUT_DIR, "cd-lh-modtime-mismatch.zip"),
    lh_method=0, cd_method=0, lh_comp=P, cd_comp=P,
    lh_mod_time=0x1234,
)
# Stored-method (method=0) size-invariant anomaly: both CD and LH
# advertise `compressedSize=6, uncompressedSize=7` with method=0.  Both
# sides agree, so the CD/LH `uncompressedSize` consistency check
# (`cd-lh-uncompsize-mismatch.zip`) does *not* fire.  APPNOTE §4.4.5
# defines method 0 as "no compression", so `compSize == uncompSize` is
# tautological — `parseCentralDir` rejects this with a
# `stored-method size mismatch` error, before any LH read.  Companion to
# `cd-lh-uncompsize-mismatch.zip`: that fixture has a CD-vs-LH divergence
# on `uncompSize`; this fixture has no CD-vs-LH divergence but violates
# the stored-method equality tautology.  Together they close the
# stored-method size-invariant dimension from both angles (CD/LH skew
# and intra-CD invariant violation).
write(
    os.path.join(OUT_DIR, "cd-stored-size-mismatch.zip"),
    lh_method=0, cd_method=0, lh_comp=P, cd_comp=P,
    lh_uncomp=P + 1, cd_uncomp=P + 1,
)
# CD-parse method allowlist anomaly: both CD and LH advertise
# `method=6` (imploded — deprecated in PKZIP 2.0, 1993).  lean-zip's
# allowlist is `{0, 8}`; any other value is rejected at CD parse time
# with `"unsupported compression method"`.  Companion to
# `bad-method.zip` (LH/CD method=14, LZMA): both fixtures trip the
# same CD-parse guard, but the distinct method values let the
# paired-review distinguish which fixture fired.  The payload bytes
# are the literal `b"hello\n"` regardless of the method field —
# the guard rejects before any payload decode is attempted, so the
# bytes are never interpreted as imploded data.
write(
    os.path.join(OUT_DIR, "cd-bad-method-early.zip"),
    lh_method=6, cd_method=6, lh_comp=P, cd_comp=P,
)
# CD-parse per-entry `versionNeededToExtract` upper-bound anomaly: both
# CD and LH advertise `versionNeededToExtract=51` (AES per APPNOTE
# §4.4.3.2).  lean-zip handles only `20` (stored/deflate) and `45`
# (ZIP64); any higher value signals an unsupported feature (Deflate64
# `21`, BZIP2 `46`, AES `51`, LZMA/PPMd/XZ `63`).  `parseCentralDir`
# rejects at CD parse time with
# `"unsupported versionNeededToExtract"` before the one-sided CD/LH
# downgrade check (`"LH versionNeededToExtract exceeds CD"`) — that
# check only catches LH > CD, so CD=LH=51 would otherwise pass it.
# Complements the allowlist/stored-method/version-downgrade family:
# `cd-bad-method-early.zip` (method allowlist), `cd-stored-size-mismatch.zip`
# (method=0 size invariant), `cd-lh-version-mismatch.zip` (LH>CD
# downgrade), and now this fixture close the per-entry CD-parse
# smuggling surface.
write(
    os.path.join(OUT_DIR, "cd-version-needed-too-high.zip"),
    lh_method=0, cd_method=0, lh_comp=P, cd_comp=P,
    lh_version=51, cd_version=51,
)
# CD-parse per-entry `localOffset + 30 <= cdOffset` archive-layout
# anomaly.  The LH+data sits at file offset 0 (length 45 = 30-byte
# header + 9-byte name + 6-byte payload).  The CD starts at file offset
# 45 (cdOffset=45).  The CD entry's `localOffset` field (CD +42, UInt32)
# is crafted to 50 — strictly greater than `cdOffset - 30 = 15`, so the
# new check `localOff + 30 <= cdOffset` (50+30=80 > 45) fires.  The
# late `assertSpanInFile` guard in `readEntryData` would accept it
# (50+30=80 <= fileSize=122), so the new CD-parse check is the
# only gate that catches this construction on the `Archive.list` path
# and is what attributes the fault to CD parse on the extract path.
# All other CD/LH fields are internally consistent (stock hello.txt
# stored entry, versionNeeded=20, method=0, no ZIP64) so no sibling
# guard fires first.  Companion to the archive-level sibling fixture
# `cd-extends-past-eocd.zip` (cdOffset + cdSize past EOCD): together
# they close the full archive-layout invariant surface — macro
# (CD fits before EOCD) and micro (LH fits before CD).
write(
    os.path.join(OUT_DIR, "cd-entry-localoffset-past-cdstart.zip"),
    lh_method=0, cd_method=0, lh_comp=P, cd_comp=P,
    cd_local_hdr_offset=50,
)
# Late LH-signature guard regression fixture: a stock single-entry stored
# `hello.txt` archive (LH at file offset 0, CD at offset 45, EOCD at offset
# 100; total 122 B) where the LH's first 4 bytes are overwritten with
# `0xCAFEBABE` (LE: `BE BA FE CA`) instead of the APPNOTE §4.3.7
# `sigLocal = 0x04034b50`.  All CD-parse guards pass (CD itself is
# byte-identical to the stock `hello.txt` baseline; `localOffset = 0`,
# `localOffset + 30 = 30 ≤ cdOffset = 45`, `entryEnd = 45 ≤ cdEnd = 100`,
# method ∈ {0, 8}, `compSize == uncompSize` for stored, etc.) and
# `assertSpanInFile` / `readBoundedSpanFromHandle` clear the LH span
# (30 B at offset 0 ≤ fileSize 122).  The 4-byte mismatch trips the late
# guard at Zip/Archive.lean:1081 — *"bad local header signature for {label}"*
# — which is `Archive.extract`'s defense-in-depth catch for archives that
# slip past every CD-parse and span guard.  `Archive.list` never reads
# the LH and lists the fixture cleanly; only `Archive.extract` throws,
# pinning the precedence story.  Sibling of
# `cd-entry-localoffset-past-cdstart.zip` (PR #1813, fires the per-entry
# `localOffset + 30 ≤ cdOffset` CD-parse guard before the LH read) and
# `cd-entry-past-cdend.zip` (in-flight issue #1885, fires the `entryEnd > cdEnd`
# CD-parse guard before the LH read): together the trio pins all three
# precedence levels of the local-offset → local-header validation chain
# at CD-parse + late-extract, ensuring future refactors of
# `Archive.extract` cannot silently drop the late LH-signature guard.
# The non-default `lh_signature=0xCAFEBABE` is the only deviation from
# the baseline; choice of `0xCAFEBABE` is canonical "obviously crafted"
# UInt32 — any 4-byte sequence ≠ `50 4b 03 04` fires the same guard.
write(
    os.path.join(OUT_DIR, "cd-bad-lh-signature.zip"),
    lh_method=0, cd_method=0, lh_comp=P, cd_comp=P,
    lh_signature=0xCAFEBABE,
)
# CD-entry `internalFileAttributes` reserved-bits anomaly (APPNOTE §4.4.10):
# the CD entry's internal-attrs field at CD +36 (UInt16) carries `0x0080`
# — bit 7 set, reserved for PKWARE per APPNOTE §4.4.10 which defines only
# bit 0 ("apparent ASCII/text data") and leaves bits 1-15 as
# reserved/unused in version 1.0.  lean-zip's writer emits zero here
# (writer-zero invariant: the 46-byte CD header is `Binary.zeros`-
# initialised and `pos + 36` is never overwritten), and Info-ZIP/Go/
# Python interop fixtures use only `0x0000` or `0x0001` (text-flag).
# `parseCentralDir` rejects with `"internalAttrs reserved bits set"`
# early in the iteration loop (after `diskNumberStart`, before
# `entryEnd`).  Companion to `cd-entry-disknum-mismatch.zip` (CD +34
# writer-zero field) and the archive-level `eocd-numentries-thisdisk-
# mismatch.zip` (EOCD writer-invariant); together they extend the
# "writer-zero single-field at CD+offset" early-reject lineage.  LH
# mirrors the CD (no LH `internalAttrs` field exists; APPNOTE §4.3.7).
write(
    os.path.join(OUT_DIR, "cd-entry-internal-attrs-reserved.zip"),
    lh_method=0, cd_method=0, lh_comp=P, cd_comp=P,
    cd_internal_attrs=0x0080,
)
# CD-parse general-purpose flag bit-5 (compressed patched data) anomaly:
# both CD and LH advertise `flags = 0x0020` (bit 5 only).  APPNOTE §4.4.4
# bit 5 means "file is compressed patched data" — PKWARE's proprietary
# binary-delta layout (§4.6).  lean-zip implements neither creation nor
# extraction of patched-data files; the writer emits `flags = 0x0800`
# (bit 11 UTF-8 names) only.  A crafted archive with bit 5 set is
# currently silently accepted as if the payload were plain Deflate/stored
# data — a parser-differential smuggling vector.  `parseCentralDir`
# rejects at CD parse time with
# `"patched-data flag bit 5 set"`, before any payload decode.  Mirroring
# `lh_flags = cd_flags = 0x0020` is load-bearing so the CD-vs-LH
# bit-3-masked flags check (PR #1715) does not fire first
# (`0x0020 &&& 0xFFF7 = 0x0020` on both sides).  Sibling of the
# encryption-related bit 0/6/13 family (issue #1762, in-flight PR #1771)
# and the other CD-parse flag-field guards; together they close the
# unimplemented-feature flag-bit dimension at the CD-parse layer.
write(
    os.path.join(OUT_DIR, "cd-patched-data-flag.zip"),
    lh_method=0, cd_method=0, lh_comp=P, cd_comp=P,
    lh_flags=0x0020, cd_flags=0x0020,
)
# CD-parse entry-name NUL-byte anomaly: both CD and LH carry the raw name
# bytes `b"a\x00b.txt"` (7 bytes, NUL at index 1).  APPNOTE §4.4.17
# defines the filename field but says nothing about permissible byte
# values; a NUL byte in the name is a classic parser-differential /
# filesystem-truncation smuggling vector — POSIX `open`/`stat` and many
# runtime layers treat `evil.txt\x00.zip` as `evil.txt`, while
# `Archive.list` callers and strict peer readers see the full
# NUL-embedded string.  lean-zip's pre-fix behaviour was: `Archive.list`
# returned an `Entry` with the NUL-containing `path` verbatim (the
# decoded `String` preserves U+0000 via both `String.fromUTF8?` and
# `Binary.fromLatin1`), and `Archive.extract` with the default
# `Binary.isPathSafe` passed the NUL-containing path into
# `IO.FS.writeBinFile` where the POSIX `open` layer truncates at NUL —
# depositing the extracted file at the short-form prefix, not the
# smuggled full form.  `parseCentralDir` now rejects at CD parse time
# with `"CD entry name contains NUL byte"` — guarding on the raw
# `ByteArray` before UTF-8 decode so the error message never
# re-introduces NUL into logs, and so both the UTF-8 and Latin-1
# decode branches are closed uniformly.  LH and CD name bytes match
# byte-for-byte, keeping the CD/LH name-bytes consistency invariant
# (issue #1722) intact.  The short 7-byte name minimises fixture size
# while still being plausibly path-like (`a`, NUL, `b.txt`).
write(
    os.path.join(OUT_DIR, "cd-nul-in-name.zip"),
    lh_method=0, cd_method=0, lh_comp=P, cd_comp=P,
    name_bytes=b"a\x00b.txt",
)
# CD-parse entry-name path-unsafe anomaly: both CD and LH carry the raw name
# bytes `b"../evil.txt"` (11 bytes — a classic `..`-traversal archive-slip
# smuggle).  `Binary.isPathSafe` (shared with the Tar extractor and the ZIP
# extract-time check) rejects `..` as a component.  Pre-PR, `Archive.list`
# returned the `Entry` with the unsafe `path = "../evil.txt"` verbatim
# (the decoded `String` preserves the component structure), exposing the
# full smuggled form to callers who routed on `entry.path` before any
# filesystem I/O — the extract-time `Binary.isPathSafe` calls in
# `Archive.extract` at Zip/Archive.lean:1070 / :1074 caught only the
# extract path.  `parseCentralDir` now rejects at CD parse time with
# `"CD entry has unsafe path"`, closing both `Archive.list` and
# `Archive.extract` dimensions simultaneously.  The 11-byte name is 2
# bytes longer than the default `b"hello.txt"` (9 bytes) so the file
# shifts by +4 from the baseline 118-byte fixture (+2 for each of CD
# name bytes and LH name bytes); no other fixture depends on
# byte-identity with this fixture.  LH and CD name bytes match
# byte-for-byte, keeping the CD/LH name-bytes consistency invariant
# (issue #1722) intact.  Sibling of `cd-nul-in-name.zip` (PR #1831): the
# NUL-byte fixture closes the byte-content dimension of filename
# smuggling; this fixture closes the path-shape dimension.  The choice
# of `..` over `/abs/path`, `a\evil.txt`, or `C:/Windows/...` is
# arbitrary among the five `isPathSafe`-rejected shapes — `..` is the
# canonical archive-slip vector cited by APPNOTE-era security
# literature and by the tar-side `tar-slip.tar` companion fixture.
write(
    os.path.join(OUT_DIR, "cd-path-unsafe.zip"),
    lh_method=0, cd_method=0, lh_comp=P, cd_comp=P,
    name_bytes=b"../evil.txt",
)
# CD-parse entry-name empty-filename anomaly: both CD and LH carry
# `name_bytes=b""` (length 0), so the `name length` UInt16 at CD +28
# and LH +26 is `0`.  APPNOTE §4.4.10 defines the filename-length
# field; every legitimate ZIP entry — file or directory — has at
# least one byte of name, so `nameLen == 0` is structurally
# pathological and a parser-differential smuggling vector (lenient
# readers emit `entry.path = ""` — an `Entry` with no useful identity;
# strict readers reject).  `parseCentralDir` now rejects at CD parse
# time with `"CD entry has empty filename"` immediately after the
# `nameLen` read at CD +28, before the `entryEnd > cdEnd` overrun
# check and before the sibling path-safety / NUL-byte filename
# guards so the failure attribution pins to the structural anomaly
# rather than the path-safety predicate (which would otherwise catch
# the empty string via its empty-component rejection, but only if
# the decode succeeds).  LH and CD `name_bytes` match byte-for-byte
# (both empty), keeping the CD/LH name-bytes consistency invariant
# (issue #1722) intact — both sides agree so the LH `nameLen` overrun
# guard at line 540 and any CD/LH name-bytes-mismatch check do not
# fire first.  The 9-byte savings on each side (vs. the 9-byte
# default `NAME = b"hello.txt"`) shift the file length by -18 from
# the 122-byte baseline to 104 bytes.  Sibling of `cd-nul-in-name.zip`
# (PR #1831, byte-content dimension) and `cd-path-unsafe.zip`
# (PR #1840, path-shape dimension): together they close the
# smuggled-name attack class (zero-length, NUL-embedded, and
# path-traversal forms all rejected at CD parse).
write(
    os.path.join(OUT_DIR, "cd-empty-name.zip"),
    lh_method=0, cd_method=0, lh_comp=P, cd_comp=P,
    name_bytes=b"",
)
# CD-parse empty-entry CRC invariant anomaly: CD and LH both advertise a
# zero-byte stored entry (`method=0, compSize=0, uncompSize=0`) but the
# CRC field is patched to `0xDEADBEEF`.  APPNOTE §4.4.7 defines the
# CRC32 field as the ANSI-CRC-32 of the uncompressed payload; the empty
# byte string has CRC32 `0x00000000` (start state `0xFFFFFFFF`; no data
# to process; final complement returns `0x00000000`), so
# `uncompSize == 0 → crc == 0` is a universal mathematical invariant.
# Every correct writer (Info-ZIP, Go `archive/zip`, CPython `zipfile`,
# 7-Zip, lean-zip's own `create`) obeys it.  `parseCentralDir` now
# rejects at CD parse time, post-ZIP64-resolution, after the
# stored-method size invariant — the empty-file premise pins
# attribution to the invariant rather than a generic CRC check.  LH
# and CD carry the same crafted CRC so the earlier CD/LH `crc32`
# consistency check (`cd-lh-crc-mismatch.zip` family) does not fire
# first.  Payload is empty (`payload=b""`) because `compSize = 0` —
# the 9-byte name bytes follow the LH immediately, then the CD.  The
# stored-method `compSize == uncompSize` invariant holds (both `0`)
# so that guard does not fire first.  File layout:
#   LH (30 B) + name (9 B) = 39 B; CD (46 B) + name (9 B) = 55 B;
#   EOCD (22 B); total 116 B.  Sentinel value `0xDEADBEEF` chosen as
# a canonical "obviously crafted" non-zero UInt32 — any nonzero value
# fires the same guard.  Pre-PR, `Archive.list` propagated the crafted
# CRC into `Entry.crc32` verbatim (callers routing on `entry.crc32`
# saw the smuggled value) and `Archive.extract` caught the mismatch
# only post-extraction via the `"CRC32 mismatch"` guard at
# Zip/Archive.lean:1088 — after any I/O work had been performed.
write(
    os.path.join(OUT_DIR, "cd-empty-entry-crc-nonzero.zip"),
    lh_method=0, cd_method=0,
    lh_comp=0, cd_comp=0, lh_uncomp=0, cd_uncomp=0,
    lh_crc=0xDEADBEEF, cd_crc=0xDEADBEEF,
    payload=b"",
)
# CD-parse deflate-method zero-compSize/nonzero-uncompSize math invariant
# anomaly: CD and LH both advertise `method=8` (deflate) with
# `compressedSize=0` and `uncompressedSize=42`.  APPNOTE §4.4.8 / §4.4.9
# define these fields; every ZIP compression method produces at least one
# compressed byte from non-empty uncompressed input (method 0 has
# `compSize == uncompSize`; method 8 has a 2-byte minimum block-header
# encoding per RFC 1951 — the `03 00` empty-stored-block marker).  So
# `compSize == 0 ∧ uncompSize > 0` is structurally impossible regardless
# of method — a universal mathematical invariant every correct writer
# obeys.  The sibling `cd-stored-size-mismatch.zip` catches this shape
# only when `method == 0` (via the equality mismatch); the sibling
# `cd-empty-entry-crc-nonzero.zip` covers `uncompSize == 0` entries.
# This fixture closes the method=8 residual at CD parse — pre-PR,
# `Archive.list` returned an `Entry` with the smuggled values verbatim
# and `Archive.extract` failed only later inside the inflate backend
# with an undescriptive decompression error whose attribution did not
# pin the structural anomaly.  `parseCentralDir` now rejects at CD
# parse time, post-ZIP64-resolution, after the stored-method size
# invariant and the empty-entry CRC invariant — the three math-invariant
# columns sit as a contiguous block.  CRC is `0` so the empty-entry
# guard (which only fires on `uncompSize == 0`) does not interact; the
# stored-method guard (which only fires on `method == 0`) is also
# silent.  Payload is empty (`payload=b""`) because `compSize=0` — the
# 9-byte name bytes follow the LH immediately, then the CD.  LH and
# CD fields match byte-for-byte, keeping the CD/LH consistency
# invariants (method / sizes / crc / version / flags) intact so no
# sibling CD/LH skew guard fires first.  File layout:
#   LH (30 B) + name (9 B) = 39 B; CD (46 B) + name (9 B) = 55 B;
#   EOCD (22 B); total 116 B.  Uncompressed-size value `42` chosen as
# a canonical "obviously crafted" non-zero UInt32 — any positive value
# fires the same guard.
write(
    os.path.join(OUT_DIR, "cd-deflate-zero-compsize.zip"),
    lh_method=8, cd_method=8,
    lh_comp=0, cd_comp=0, lh_uncomp=42, cd_uncomp=42,
    lh_crc=0, cd_crc=0,
    payload=b"",
)
# CD-parse per-entry footprint-overrun anomaly: the CD entry's declared
# `commentLen` field at CD +32 (UInt16) is set to `16` while the physical
# CD bytes carry no comment payload — the EOCD's `cdSize` is the natural
# `len(cde) = 46 + 9 = 55` (header + name only).  At CD parse time
# `entryEnd = pos + 46 + nameLen + extraLen + commentLen
#            = 45 + 46 + 9 + 0 + 16 = 116` — strictly past
# `cdEnd = cdOffset + cdSize = 45 + 55 = 100`.  `parseCentralDir`
# rejects with `"central directory entry extends past end of central
# directory"` at [Zip/Archive.lean:615](/home/kim/lean-zip/Zip/Archive.lean:615) —
# the per-entry footprint guard.  All earlier CD-parse guards pass: the
# loop entry condition `pos + 46 ≤ cdEnd` (91 ≤ 100) holds, the CD
# signature matches, `nameLen=9 > 0`, `diskNumberStart=0`,
# `internalAttrs=0`, so the :615 guard is the first one that fires
# — deterministic attribution.  All other CD/LH fields are internally
# consistent (stock hello.txt stored entry, versionNeeded=20, method=0,
# no ZIP64); LH and CD match byte-for-byte on every cross-checked field.
# The fixture is regression coverage for an existing guard (no new code
# in `parseCentralDir` lands with this fixture).  Companion to the
# in-flight `cd-trailing-garbage.zip` (PR #1777, trailing bytes AFTER
# the last entry inside `[lastEntryEnd, cdEnd)`) and
# `cd-extends-past-eocd.zip` (PR #1809, archive-level
# `cdOffset + cdSize ≤ eocdPos`): the trio closes the three CD-region
# overrun shapes — per-entry footprint past `cdEnd`, trailing garbage
# inside the declared region, and macro `cdSize` past EOCD.  Pre-PR
# (and absent the :615 guard), `Archive.list` would attempt to read
# the `nameBytes` slice at `[pos + 46, pos + 46 + nameLen)` which
# remains inside the buffer (45+46+9=100 ≤ 100), but with crafted
# field-length combinations a lenient parser could overread into
# the EOCD bytes — a parser-differential smuggling vector closed by
# the existing :615 fence.  File layout:
#   LH (30 B) + name (9 B) + payload (6 B) = 45 B;
#   CD (46 B) + name (9 B) = 55 B;
#   EOCD (22 B); total 122 B.
# Sentinel `commentLen=16` chosen as a canonical "obviously crafted"
# overrun — any positive value satisfying
# `46 + nameLen + extraLen + commentLen > cdSize` fires the same guard.
write(
    os.path.join(OUT_DIR, "cd-entry-past-cdend.zip"),
    lh_method=0, cd_method=0, lh_comp=P, cd_comp=P,
    cd_comment_length=16,
)
