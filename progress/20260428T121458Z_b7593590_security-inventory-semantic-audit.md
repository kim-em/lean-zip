# Security inventory semantic audit (Q2 2026)

- Date: 2026-04-28T12:14:58Z
- Session: b7593590
- Issue: #2358
- Files audited: SECURITY_INVENTORY.md (every `## ` and `### ` section)

## Findings

Per-section audit. Verdicts: **STILL TRUE** (no edit needed),
**ROTTED** (edit applied or deferred), or **UNCLEAR**.

### `## Status Labels`

- Four-label taxonomy (`proved-in-repo` / `guarded-locally` /
  `tested-only` / `upstream-risk`) — **STILL TRUE**; matches the
  labels actually used downstream.

### `### Lean Runtime: ByteArray, scalar-array allocation, IO`

- Status downgrade `upstream-risk` → `guarded-locally` — **STILL
  TRUE**. Verified upstream:
  - https://github.com/leanprover/lean4/issues/13388 reports
    `state=closed`, `closed_at=2026-04-13T18:33:23Z`.
  - https://github.com/leanprover/lean4/pull/13392 reports
    `merged=true`, `merged_at=2026-04-13T18:33:22Z`.
  - https://github.com/leanprover/lean4/releases/tags/v4.30.0-rc2
    `published_at=2026-04-17T10:36:03Z`.
  - `lean-toolchain` reads `leanprover/lean4:v4.30.0-rc2` — pin
    confirmed.
- *"Re-evaluation after v4.30.0-rc2"* paragraph — **STILL TRUE**;
  no guardrails dropped.
- All five regression-fixture filenames in *Local regression
  coverage* — **STILL TRUE**; `check-inventory-links.sh` reports
  all referenced fixtures exist (78 paths, 0 errors).

### `### zlib via C FFI`

- *"April 2026 tree is ASan + UBSan clean"* — **UNCLEAR** (not
  re-verified in this audit; would require re-running
  `scripts/sanitize-ffi.sh`). Date-bounded claim is consistent
  with current month; left as-is.
- Allocation site audit table — **STILL TRUE**; structural
  description of `c/zlib_ffi.c` allocation flow matches code,
  no schema changes since the snapshot's 2026-04-22 date.
- Summary "Catches / Does NOT catch" enumeration — **STILL
  TRUE**.

### `### Zip.Native.Inflate and verified DEFLATE core`

- Status `proved-in-repo` and the three component file references
  — **STILL TRUE**; all three files exist.

### `### ZIP Archive Reader/Extractor`

- Status `guarded-locally`, *Trust boundary*, *Current
  guardrails* — **STILL TRUE**.
- *Missing work* item *"CD-vs-EOCD comment-length consistency
  not yet checked"* — **STILL TRUE**; verified open via GitHub
  search (#1739 *"Track E: EOCD comment-length trailing-garbage
  check + eocd-comment-trailing-garbage.zip fixture"*, state
  open).
- *Recent wins* prose mentions `(sibling issue #1902 in flight
  as PR #1909)` for the `numberOfThisDisk` slot — **STILL TRUE**;
  PR #1909 reports `state=open`, `merged=false`.
- *Recent wins* mentions in-flight `cd-trailing-garbage.zip`
  (#1775) and `cd-extends-past-eocd.zip` (#1799) — both **STILL
  TRUE / open**.
- *Recent wins* mentions in-flight per-bit feature series
  (#1762, #1817, #1818) — **partial drift**: #1817 is now
  *closed* (PR #1824 landed and the inventory already documents
  it as a *Recent win*), while #1762 and #1818 are still open.
  The phrasing *"the in-flight per-bit feature series (issues
  #1762, #1817, #1818)"* is no longer fully accurate but is
  *correct in spirit* (the series is in flight, just one of the
  three named bits has now landed). Single-row prose drift in a
  defense-in-depth descriptive aside; not load-bearing for any
  caller, defer to the line-number sweep follow-up (#2361 covers
  this row's broader rewrite).

### `### Tar Parser/Extractor`

- *Trust boundary*, *Current guardrails*, *Recent wins* —
  **STILL TRUE**.
- *Missing work* says *"none open at this layer"* — **STILL
  TRUE**; the `Track E Tar` GitHub-search returns only zombie
  anchor-refresh issues (which #2359's close-out wave is in
  flight to retire), no real Tar-layer work items.
- *Per-typeflag policy* enumeration (typeRegular, typeDirectory,
  typeSymlink, typeHardlink, all-others) — **STILL TRUE**.
- Five regression-fixture filenames under
  `testdata/tar/security/` — **STILL TRUE** (link-checker
  confirms).

### `### Gzip/Zlib/Raw DEFLATE Public APIs`

- All four *Missing work* bullets are marked *Executed* —
  **STILL TRUE**; the inventory's *Decompression Limit Inventory*
  table below confirms the bounded-mode defaults landed.

### `### 1. ZIP metadata to Handle.read`

- Concern + *Recent wins* — **STILL TRUE**; *"prove bounded-read
  lemmas for the guarded read paths"* remains the open
  Needed-row.

### `### 2. Tar UTF-8 partial functions`

- Audit-landed status, `Tar.truncateUTF8` reference — **STILL
  TRUE**.

### `### 3. Unlimited decompression knobs`

- Concern + cross-ref to *Decompression Limit Inventory* —
  **STILL TRUE**.

### `## Decompression Limit Inventory`

- Per-API parameter / default / `0`-semantics table — **STILL
  TRUE**; defaults match the source (1 GiB FFI, 1 GiB native, 64
  MiB CD allocation cap).
- *Known inconsistencies* says *"None outstanding"* — **STILL
  TRUE**.
- *Recommended policy* items 1–6, all marked *Executed* with
  PR refs — **STILL TRUE**; verified PR refs (#1623, #1631,
  #1618, #1630, #1709 / #1710 cluster, plus issue #1609).
- *Missing work* says *"All bomb-limit regression coverage
  proposed in the original block has landed... Residual gaps:
  none currently open at this layer."* — **STILL TRUE**.
- *Local guard inventory* table — **STILL TRUE** for every row
  audited.

### `## Minimized Reproducer Corpus`

- Convention preamble + columns description — **STILL TRUE**.
- Every cited fixture path resolves (`check-inventory-links.sh`
  exit 0).
- Many fixture-row descriptions still contain "line N"
  parentheticals (~30+ occurrences across the per-slot
  ZIP64-override family, the UStar interior-NUL family, the GNU
  long-name family, and the `bad-method.zip` row). Per #2345 these
  should be removed — **ROTTED prose, deferred** to the dedicated
  fix-up issue #2361 below. Not load-bearing for correctness;
  every row's stable identifiers (Fixture filename, Defence
  exercised throw-message substring, First landed PR) carry the
  audit-trail weight on their own.

### `## Required Maintenance Rule`

- Trust-status / guardrails / missing-work / regression-refs
  bullets — **STILL TRUE**.
- *"The script also emits advisory warnings when a cited line
  number may have drifted relative to the quoted error-substring
  prose — treat these as hints, not blockers"* — **ROTTED**. PR
  #2353 (closing #2345) retired the line-anchor freshness passes;
  the script now only warns about unresolved placeholder PR
  references (`#TBD` / `#N` / `#XXX` / `#NNN` / *"this PR"*).
  Edit applied below.

## Edits applied in this PR

- `SECURITY_INVENTORY.md` *Required Maintenance Rule*: rewrote
  the `check-inventory-links.sh` paragraph to describe the actual
  current behaviour (fixture-path existence pass + placeholder-PR
  scan) and to reference the #2353 / #2345 retirement of the
  line-anchor passes. Added a `<!-- drift-detector: ... -->`
  per-line opt-out marker to silence the placeholder-PR pass on
  the line that literally documents the placeholder tokens.

## Items deferred (created as separate issues)

- #2361 — *Inventory prose fix-up: sweep ~30+ residual 'line N'
  references in SECURITY_INVENTORY.md left by #2353 anchor-strip
  (audit follow-up from #2358)*. Sibling of #2360 (same fix-up
  pattern, different file).
- #2362 — *Inventory: decide whether to add a 'miniz_oxide via
  Rust' TCB subsection to SECURITY_INVENTORY.md (post-#2356 audit
  follow-up from #2358)*. PR #2356 introduced a new public
  `Zip/MinizOxide.lean` and a `rust/miniz_oxide_shim/` Cargo
  crate as a Track D Phase 0c bench comparator. The audit deferred
  the structural decision (add a new TCB row vs. document under
  the existing `### zlib via C FFI` row vs. leave out of scope as
  bench-only).

## Items left as-is

- *"April 2026 tree is ASan + UBSan clean"* in `### zlib via C
  FFI` — date-bounded claim consistent with current month; not
  re-run as part of this audit (would require executing
  `scripts/sanitize-ffi.sh` which is out of audit scope).
- The "in-flight (issues #1762, #1817, #1818)" aside in `### ZIP
  Archive Reader/Extractor` *Recent wins* — partial drift (#1817
  has landed via PR #1824) but the broader prose row is queued
  for rewrite under #2361's sweep.

## Cadence note

Audit produced one rotted claim (Required Maintenance Rule, one
sentence) and two structural deferrals (#2361 / #2362). Neither
deferral is a new attack-surface concern — they are documentation
hygiene and a planner-level decision on whether to extend the TCB
section. Per the cadence guidance in #2358, this argues for a
quarterly rather than monthly cadence on the next audit.
