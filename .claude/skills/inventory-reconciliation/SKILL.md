---
name: inventory-reconciliation
description: Use when landing a PR that closes a numbered item in `SECURITY_INVENTORY.md` *Recommended policy* or *Missing work*, or when threading a new parameter through public APIs with a deferred default flip. Covers the one-PR-per-bullet cadence, the *Executed past-tense one-liner* phrasing, and when to use the half-closed two-step.
allowed-tools: Read, Bash, Grep
---

# Inventory Reconciliation (lean-zip)

Patterns for executing `SECURITY_INVENTORY.md` *Recommended
policy* and *Missing work* bullets as individual PRs.

## One PR per bullet

**Rule**: each numbered *Recommended policy* item (and each
bulleted *Missing work* item) lands as its own PR. Do not
batch two items into one PR.

**Cost of violation**: `scripts/check-inventory-links.sh`
warnings cannot be attributed to a single executing PR, and the
post-merge line-anchor drift compounds. Plus the planner loses
the bullet-to-PR-number 1:1 mapping in PROGRESS.md.

**Precedent**: Rec. 1/2/3/4/5 landed as five PRs in the
2026-04-22 audit-completion wave (#1617, #1618, #1623, #1630,
#1631). The prior wave's P2.4 docstring split (#1573, #1586,
#1594) is the earlier analogue.

## The *Executed — …* past-tense one-liner

When a PR closes a numbered bullet, rewrite that bullet (in
the same PR) from future-tense to past-tense:

- **Before**: `- [ ] Recommend raising native-side default to
  1 GiB to match FFI whole-buffer (Rec. 5).`
- **After**: `- [x] **Rec. 5 executed**: native-side default
  raised to 1 GiB in #1617; see that PR for caller impact.`

Keep the `- [x]` checkbox (for `scripts/check-inventory-links.sh`
compatibility). Keep the rec. number (`**Rec. 5 executed**`) so
the planner can cross-reference. One sentence on caller impact
with a PR-number link.

## Half-closed two-step

Use a *two-step* (parameter-add PR + default-flip PR) when:

- The parameter is *new to a public API* but the existing
  callers are numerous.
- The default flip needs independent caller-impact analysis.
- The param-add touches multiple subsystems but the flip is
  localised.

Use a *one-step* when:

- The parameter has no existing callers (no backwards-compat
  burden).
- The flip's caller impact is trivially bounded.

**Between-step discipline**: during the half-closed window,
the bullet is re-phrased as *"half-closed by #N (parameter
added, default still 0). Flip tracked as #M."* — the
`#M` is the follow-up issue, filed at the same time as the
param-add PR goes up.

**Precedent**: #1610 (half-closed, default `0`) → #1631
(default-flip) was the 2026-04-22 Rec. 2 execution. #1630 is
the counter-example (new param, no callers, one-step).

## Line-anchor drift

Every inventory-touching PR should run
`scripts/check-inventory-links.sh` before PR creation. If the
warning count increases, cite the new warnings in the PR body
(they may be legitimate — e.g., if the PR moves an `IO.userError`
emission site).

The drift detector's warning baseline is *"non-zero and
growing slowly"*. Do not block on it unless the warnings point
to a genuine `grep`-to-line mismatch.

## Single author per wave

If two inventory-reconciliation bullets are claimed
concurrently, the second-to-merge pays rebase cost on
`SECURITY_INVENTORY.md`. Planner should throttle to ≤ 2
*edits-inventory* concurrent (per the #1600 meditate's §7
heuristic) and prefer *sequential* bullets over parallel ones.

## Terminal-closure tightening cadence

When a *Recent wins* bullet covers a per-slot fixture family with a
shared guard (e.g. the post-#1928 UStar interior-NUL family — five
slots `name`/`linkname`/`prefix`/`uname`/`gname`, all under the
same `containsNul` reject), each per-slot landing **rewrites the
same bullet's residual-coverage carve-out**, shrinking the
residual-statement by exactly one slot. The carve-out is the
written record of "what's left"; tightening it on every land keeps
the bullet honest as the family closes.

**Per-step shape**: each PR in the wave touches exactly one bullet
in `SECURITY_INVENTORY.md` *Recent wins* — the bullet for the
shared guard. The PR's `SECURITY_INVENTORY.md` diff is one
carve-out paragraph rewrite (no new bullet, no row reorder), with
the carve-out's slot list shrinking by one entry. The new entry
in *Recent wins* (the per-slot fixture itself) goes elsewhere in
the file (typically the per-format inventory rows), not as a new
bullet — the bullet is the *family* anchor, not the per-slot
anchor.

**Closure-of-sub-arm vs terminal-closure-of-family**: the cadence
distinguishes two carve-out endings.

- **Closure of a sub-arm** leaves the bullet's carve-out paragraph
  in *partial* form, naming the still-open arm. Example phrasing:
  *"… filesystem-reaching arm fully closed (3/3); defense-in-depth
  arm pending (uname/gname)."* The bullet still acknowledges
  residual work.
- **Terminal closure of the whole family** rewrites the carve-out
  to a *terminal-closure form*: *"fully closed N/N — no more
  sibling per-slot fixtures expected"* (or equivalent). The
  bullet stops promising future tightenings. After terminal
  closure, future per-slot work on the same guard would be a
  *different family* (different guard, different bullet), not a
  6th tightening of this one.

**5-step precedent (post-#1928 UStar interior-NUL wave, terminal)**:

1. [#1880](https://github.com/kim-em/lean-zip/pull/1880) — slot
   `name`; carve-out introduced ("4 of 5 slots remain to land as
   sibling per-slot fixtures").
2. [#1934](https://github.com/kim-em/lean-zip/pull/1934) — slot
   `linkname`; carve-out shrunk to "3 of 5 remain
   (prefix/uname/gname)".
3. [#1937](https://github.com/kim-em/lean-zip/pull/1937) — slot
   `prefix`; carve-out shrunk to "filesystem-reaching arm fully
   closed (3/3); defense-in-depth arm pending (uname/gname)".
4. [#1944](https://github.com/kim-em/lean-zip/pull/1944) — slot
   `uname`; carve-out shrunk to "4/5; gname remaining" (sub-arm
   not fully closed yet).
5. [#1957](https://github.com/kim-em/lean-zip/pull/1957) — slot
   `gname`; carve-out **rewritten to terminal-closure form**
   ("fully closed 5/5 — no more sibling per-slot fixtures
   expected").

Step 3 is a *closure of a sub-arm* (filesystem-reaching arm); step
5 is the *terminal closure of the family*. The two phrasings are
not interchangeable — using terminal-closure phrasing at step 3
would mis-promise that no defense-in-depth siblings are coming;
using sub-arm phrasing at step 5 would falsely keep the bullet
open.

**When the cadence is appropriate**:

- The bullet covers a **per-slot fixture family with a shared
  guard** (all slots throw the same error wording family,
  differing only in slot-name suffix), and
- The fixture wave proceeds **one slot per PR** (per the
  *one-PR-per-bullet* cadence above), and
- The **slot count is known up front** (so terminal closure has a
  well-defined endpoint).

**When it is not**:

- One-shot bookkeeping PRs (placeholder substitutions, line-anchor
  re-anchoring, PR-number sweeps) — these touch the inventory but
  do not tighten a carve-out.
- Paired-review entries — these record observations on a landed
  PR; they do not modify the carve-out.
- Defense-in-depth extensions to a *different* guard family — a
  new family gets its own bullet, not a 6th tightening of the
  closed one.

## Per-slot fixture-naming asymmetry

Per-slot fixtures in a family with a shared guard come in two
flavours, distinguished by **whether the slot smuggles into its
own field or into the path slot**. The fixture-name suffix
encodes the distinction.

**Filesystem-reaching arm — single-`name` suffix**: the slot's
value transforms into the path before the guard fires (e.g. the
UStar `prefix` slot is concatenated with `name` by `splitPath`
before the path-validation guard runs). The fixture name uses a
**single** `name` suffix because the smuggled NUL byte ultimately
lands in the *path* slot:

    ustar-<slot>-nul-in-name.tar

The slot identifier names the writer-side smuggle vector; the
`-in-name` half names the post-transform smuggle target.

**Defense-in-depth arm — doubled-`SLOT` suffix**: the slot's value
is written verbatim to its own header field with no path
transform (e.g. UStar `uname` and `gname` are owner-metadata
fields that never reach the filesystem path). The fixture name
uses a **doubled** slot suffix because the smuggled NUL byte
lands directly in the slot's own field:

    ustar-<slot>-nul-in-<slot>.tar

The slot identifier names *both* the writer-side smuggle vector
and the smuggle target — they are the same field.

**5-slot precedent (post-#1928 UStar interior-NUL family)**:

| Slot       | Arm                  | Fixture filename                  |
|------------|----------------------|-----------------------------------|
| `name`     | filesystem-reaching  | `ustar-name-nul-in-name.tar`      |
| `linkname` | filesystem-reaching  | `ustar-linkname-nul-in-name.tar`  |
| `prefix`   | filesystem-reaching  | `ustar-prefix-nul-in-name.tar`    |
| `uname`    | defense-in-depth     | `ustar-uname-nul-in-uname.tar`    |
| `gname`    | defense-in-depth     | `ustar-gname-nul-in-gname.tar`    |

The `name` slot is the degenerate filesystem-reaching case where
slot and target collide — the fixture is `ustar-name-nul-in-name.tar`
because both the writer-side vector and the smuggle target are
literally the `name` field, but the *arm* is filesystem-reaching
(the field reaches the filesystem path).

**Smuggle-target invariant**: the suffix encodes the field that
**actually receives** the smuggled NUL byte in the on-disk
header, which is exactly the field a legitimate end-user archive
writer would target if they were trying to hide content in this
slot. The convention keeps the fixture filename diagnostic of the
attack surface, not just the slot name.

Cross-reference: `malformed-fixture-builder` covers the
*builder-script* side of the same asymmetry — the
`pathOverride` hook (filesystem-reaching arm) versus the
verbatim-write pattern with no override (defense-in-depth arm).
The two skills document the same per-slot wave from
complementary angles: this skill is for the *inventory-row
companion* of the naming choice; `malformed-fixture-builder` is
for the *builder script structure* that produces the fixture.

Origin: paired-review #1963 §E.8.e and §E.8.f
([progress/20260425T072229Z_3a21da69-paired-review-1957.md:782-810](/home/kim/lean-zip/progress/20260425T072229Z_3a21da69-paired-review-1957.md))
flagged both observations after the post-#1928 wave's terminal
closure.

## Scope — what this skill does not cover

- Does not cover *new* top-level inventory sections (that's a
  planner-design call, not a reconciliation shape).
- Does not cover the prose of the docstring changes themselves —
  those follow the #1573 template, documented in
  `error-wording-catalogue`.
