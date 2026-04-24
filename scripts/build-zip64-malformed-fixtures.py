"""Build malformed ZIP64 fixtures.

Each fixture starts from `testdata/zip/interop/go-zip64.zip` — the
project's canonical single-entry ZIP64 interop archive — and mutates
exactly one field to create a malformed reproducer.  Patching in place
(rather than synthesizing from scratch) keeps fixtures minimal, makes
the diff easy to audit, and avoids duplicating the ZIP64 record-layout
machinery the production writer already exercises.

Fixtures produced:
- `testdata/zip/malformed/zip64-locator-multidisk.zip` — ZIP64 EOCD
  Locator's `totalDisks` field (APPNOTE §4.3.15) flipped from `1` to
  `2`.  Regression for the single-disk-claim smuggling vector at the
  locator (distinct from the standard-EOCD disk-number fields already
  covered by `eocd-disknum-mismatch.zip`).  The locator sits at
  `EOCD - 20`; `totalDisks` is the last 4 bytes of that locator, i.e.
  `EOCD - 4`.  For go-zip64.zip (242 bytes, EOCD at 220), that is
  offset 216.
"""
import os

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SOURCE = os.path.join(ROOT, "testdata/zip/interop/go-zip64.zip")
OUT_DIR = os.path.join(ROOT, "testdata/zip/malformed")


def patch_locator_multidisk() -> None:
    data = bytearray(open(SOURCE, "rb").read())
    # Locate the standard EOCD signature scanning from the tail.
    eocd_sig = b"PK\x05\x06"
    eocd_pos = data.rfind(eocd_sig)
    assert eocd_pos >= 0, "source archive is missing a standard EOCD record"
    # `totalDisks` (UInt32 LE) is the last 4 bytes of the ZIP64 Locator,
    # which itself sits immediately before the standard EOCD.
    total_disks_off = eocd_pos - 4
    assert data[total_disks_off : total_disks_off + 4] == b"\x01\x00\x00\x00", (
        f"unexpected totalDisks bytes at offset {total_disks_off}: "
        f"{data[total_disks_off:total_disks_off + 4].hex()}"
    )
    # Flip totalDisks from 1 to 2 — a minimal single-byte change.
    data[total_disks_off] = 0x02
    out = os.path.join(OUT_DIR, "zip64-locator-multidisk.zip")
    with open(out, "wb") as f:
        f.write(data)
    print(f"wrote {out} ({os.path.getsize(out)} bytes)")


if __name__ == "__main__":
    os.makedirs(OUT_DIR, exist_ok=True)
    patch_locator_multidisk()
