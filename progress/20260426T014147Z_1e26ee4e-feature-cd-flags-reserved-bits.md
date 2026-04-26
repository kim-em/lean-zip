# Feature session — issue #1822 (cd-flags-reserved-bits)

- Date: 2026-04-26 01:41 UTC
- Session UUID prefix: `1e26ee4e`
- Branch: `agent/1e26ee4e`
- Issue: #1822 — Track E: reject CD entries with APPNOTE-reserved/unused
  general-purpose flag bits 7-10, 12, 14, 15 at CD parse +
  `cd-flags-reserved-bits.zip` fixture
- PR (predicted): #2237

## Accomplished

Landed the reserved-bits guard in `parseCentralDir` and the matching
`cd-flags-reserved-bits.zip` regression fixture, plus all five
deliverables called for in the issue body.

1. **Guard in `parseCentralDir`**:
   `Zip/Archive.lean:736` — `unless flags &&& 0xD780 == 0 do throw …`
   placed immediately after the method allowlist
   (`Zip/Archive.lean:711`) and before the bit-5 patched-data check
   (`Zip/Archive.lean:748`).  Mask `0xD780` =
   `0b1101_0111_1000_0000` covers APPNOTE §4.4.4 bits 7, 8, 9, 10
   ("Currently unused"), bit 12 ("Reserved by PKWARE for enhanced
   compression"), and bits 14, 15 ("Reserved by PKWARE").  Comment
   block enumerates all seven bits, references the writer-side
   `0x0800` invariant at `Zip/Archive.lean:91` (LH) and `:118` (CD),
   explicitly rules bits 1-2 out of scope (Info-ZIP / 7-Zip
   compression-option), and notes mask-disjointness with `0x2071`.
   Throw site at `Zip/Archive.lean:738`, error substring
   `"flags reserved bits set"`, message includes `flags` value
   (decimal) and CD offset `pos`.

2. **Fixture `cd-flags-reserved-bits.zip`** (122 B): both CD and LH
   advertise `flags = 0x0880` — bit 11 (UTF-8 names) plus bit 7
   reserved-bit smuggle.  Pairing bit 7 with bit 11 keeps the
   UTF-8-name guard at `Zip/Archive.lean:634` happy so the new
   reserved-bits guard is unambiguously the one that fires.  Both LH
   and CD flag words match (`flag_bits_override = 0x0880` sets both
   sides) so the CD-vs-LH bit-3-masked flags consistency check
   (PR #1715, `Zip/Archive.lean:1147`) does not fire first.

3. **Script extension**: `scripts/build-cd-lh-mismatch.py` gains a
   new `flag_bits_override : int | None = None` kwarg on `write`.
   When set, overrides both `lh_flags` and `cd_flags` to the same
   value — convenience for fixtures whose attack surface requires
   LH/CD flag-word agreement.  Default `None` preserves byte-identity
   of every existing `cd-*.zip` / `lh-*.zip` fixture (verified via
   `sha256sum` compare — only `cd-flags-reserved-bits.zip` is new;
   all other 25 fixtures match pre-change SHA256s).

4. **Test assertion** in `ZipTest/ZipFixtures.lean` slotted
   alphabetically among the `cd-*` fixtures (between
   `cd-entry-internal-attrs-reserved` and `cd-nul-in-name`), with
   substring match on `"flags reserved bits set"`.  Cleanup-array
   filename and extract-dir entries added.

5. **`SECURITY_INVENTORY.md` update**:
   - One *Recent wins* bullet under *ZIP Archive Reader/Extractor*
     citing PR #2237, the `0xD780` mask, the seven bit indices, the
     writer-side `0x0800` invariant, the Info-ZIP interop evidence,
     and the sibling framing with PR #1819 (`internalAttrs`
     `0xFFFE` mask) plus the complementary mask `0x2071` on the
     unsupported-feature side.
   - New row in the *Minimized Reproducer Corpus* table at
     `SECURITY_INVENTORY.md:1473`, slotted alphabetically between
     `cd-extra-overrun-datasize.zip` and `cd-lh-crc-mismatch.zip`.
     Defence-exercised cite at `Zip/Archive.lean:738`, related
     class `other (flag-bit validation)`, *executed past-tense
     one-liner* phrasing, no `#TBD` / `this PR` placeholders.

6. **Error-wording-catalogue entry** in
   `.claude/skills/error-wording-catalogue/SKILL.md` adds a new row
   for `"flags reserved bits set"` and updates the existing bit-5
   row to cite the new precedence.  Distinguishability documented
   against `"patched-data flag bit 5 set"`, `"encryption-related
   flag bit"`, and `"flags mismatch between CD and local header"`.

## Verification

- `lake -R build` — succeeds, all 191 jobs.
- `lake exe test` — `All tests passed!` (includes the new
  `assertThrows` on `cd-flags-reserved-bits.zip`).
- `bash scripts/check-inventory-links.sh` — `errors=0,
  warnings=46` post-change vs `errors=0, warnings=46` pre-change
  (no new warnings introduced; all existing warnings are
  pre-existing drift from upstream cite shifts being addressed by
  separate inventory-refresh PRs).
- Two back-to-back `python3 scripts/build-cd-lh-mismatch.py` runs
  produce byte-identical `cd-flags-reserved-bits.zip` (via
  `cp /tmp/run1 …; rerun; diff /tmp/run1 …` — output `DETERMINISTIC`).
- `sha256sum testdata/zip/malformed/{cd,lh}-*.zip` pre-/post-change
  byte-identity check — only `cd-flags-reserved-bits.zip` is new
  (24 existing fixtures match pre-change SHA256s; one new line
  added to the post-change set).
- Substring uniqueness:
  `grep -rn "flags reserved bits set" Zip/ ZipTest/` shows the
  guard at `Zip/Archive.lean:738`, the assertion at
  `ZipTest/ZipFixtures.lean:528` — exactly two occurrences, no
  collision with the existing CD-vs-LH `"flags mismatch"`
  substring at `Zip/Archive.lean:1147`.

## Interop pre-flight (run before landing)

Re-ran the issue body's Python sweep:

```python
import os, zipfile
hits = 0
for d in ("testdata/zip/interop", "testdata/zip/malformed"):
    if not os.path.isdir(d):
        continue
    for f in sorted(os.listdir(d)):
        if not f.endswith(".zip"): continue
        try:
            with zipfile.ZipFile(os.path.join(d, f)) as z:
                for info in z.infolist():
                    if info.flag_bits & 0xD780:
                        print(f"HIT {d}/{f}: flags=0x{info.flag_bits:04x}")
                        hits += 1
        except Exception as e:
            pass
print(f"DONE: {hits} hits")
```

Output: `DONE: 0 hits`.  No legitimate archive in
`testdata/zip/{interop,malformed}/` sets any of the seven
reserved/unused bits — the guard never fires on existing corpus
content, only on the new `cd-flags-reserved-bits.zip` and
intentionally crafted future malformed inputs.

## Pre-/post-change SHA256 diff

```
$ diff /tmp/cd-lh-fixtures-pre.sha /tmp/cd-lh-fixtures-post.sha
10a11
> fa9d49ce152ce13acc5b2fae290d12b19e297ee3c32c880d5863a54fda02da66  testdata/zip/malformed/cd-flags-reserved-bits.zip
```

Only the new fixture is added; all 24 other `cd-*.zip` / `lh-*.zip`
fixture SHA256s match byte-for-byte across the
`flag_bits_override` kwarg landing.

## Quality metric

`grep -rc sorry Zip/ || true` — no change (PR adds no proofs).

## Notes / decisions

- **Placement**: chose to place the new guard immediately after the
  method allowlist and before the bit-5 patched-data check, matching
  the issue body's recommended precedence
  (`method allowlist → reserved flag bits → bit 5 → ...`).  Since
  `0xD780` and `0x0020` are disjoint masks, the relative order has
  no security impact, but the chosen order keeps the
  reserved-vs-unsupported-feature distinction grep-discoverable.
- **`flag_bits_override` placement**: added on `write` only (not on
  `make_cd` / `make_lh` separately), since the convenience is
  meaningful only when LH and CD flag-words must agree — for
  per-side independent control, the existing `lh_flags` / `cd_flags`
  kwargs remain available.  This is a minor deviation from the
  issue body's suggestion of "on make_cd / make_lh / write" but
  avoids redundant API surface; the existing `cd-patched-data-flag`
  fixture's `lh_flags=0x0020, cd_flags=0x0020` style remains
  supported.
- **PR-number prediction**: predicted `#2237` (next number after
  the most-recent issue/PR `#2236`).  If concurrent sessions create
  intervening issues/PRs before this branch's PR is opened, a
  follow-up commit can re-anchor the three `#2237` occurrences in
  `SECURITY_INVENTORY.md` (Recent wins bullet + Minimized
  Reproducer Corpus row) and `.claude/skills/error-wording-catalogue/SKILL.md`
  (one row).
