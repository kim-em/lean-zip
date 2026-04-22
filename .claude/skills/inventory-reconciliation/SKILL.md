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

## Scope — what this skill does not cover

- Does not cover *new* top-level inventory sections (that's a
  planner-design call, not a reconciliation shape).
- Does not cover the prose of the docstring changes themselves —
  those follow the #1573 template, documented in
  `error-wording-catalogue`.
