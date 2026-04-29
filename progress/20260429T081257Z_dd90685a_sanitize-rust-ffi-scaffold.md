# Session 20260429T081257Z (UUID prefix dd90685a) — feature

## Summary

Scaffolded `scripts/sanitize-rust-ffi.sh` and the sibling
*Sanitizer recipe* paragraph in `SECURITY_INVENTORY.md` *miniz_oxide
via Rust* TCB subsection. Closes the **scaffolding** half of
Missing-work bullet 1 of that subsection (originally added by
PR #2371). The recipe body itself is deferred to a follow-up issue
gated on a Linux + nightly-Rust worker host; the draft body for that
follow-up is left as a comment on PR #2383 for the next planner.

Closes issue #2379 via PR #2383.

## What landed

- **`scripts/sanitize-rust-ffi.sh`** (new, executable, 144 lines).
  Mirrors `scripts/sanitize-ffi.sh` in shape:
  - Header comment block describing scope (`c/miniz_oxide_ffi.c` +
    `libminiz_oxide_shim.a` only — explicitly excludes
    `c/zlib_ffi.c` which is `sanitize-ffi.sh`'s job, and excludes
    the Lean runtime which has no analogue).
  - `usage()` block describing the intended ASan recipe shape:
    `cargo +nightly build --release` of `rust/miniz_oxide_shim/`
    with `RUSTFLAGS="-Zsanitizer=address"`, surface the
    instrumented `libminiz_oxide_shim.a` via
    `MINIZ_OXIDE_LDFLAGS`, `lake -R clean && lake -R build`, run
    a small Lean driver against the smoke-test inputs from
    `ZipTest/MinizOxide.lean`. UBSan support explicitly noted as
    *future*.
  - Environment guard at top of `main()` (mirrors
    `sanitize-ffi.sh`'s `cc -print-file-name=libasan.so` absolute-
    path check): two-step check for `cargo` on `PATH` then
    `cargo +nightly --version` exit 0. Either failure exits 2
    with a clear "environment requirements not met" message.
  - TODO body: a single block that exits 1 with a clear
    "skeleton" message so callers cannot mistake an unfilled-
    recipe run for a clean ASan pass.
  - `set -euo pipefail`, `usage()`, `--help`, lakefile.lean
    root-check — same conventions as `sanitize-ffi.sh`.
- **`SECURITY_INVENTORY.md`** (`miniz_oxide via Rust` subsection,
  `+19 -5`):
  - *Current local guardrails* gains a new *Sanitizer recipe
    scaffolded but not yet executed* bullet pointing at
    `scripts/sanitize-rust-ffi.sh` and recording the deferred body.
  - *Missing work* bullet 1 — the *"Sketch: build the Rust crate
    under `RUSTFLAGS=...`"* sentence — replaced with a
    *"Scaffolded as `scripts/sanitize-rust-ffi.sh` in PR #2383;
    the recipe body is TODO, deferred to a sibling follow-up
    issue when a Linux + nightly-Rust worker host is available"*
    phrasing. Bullet stays open (body not executed) but now
    records the half-step.
- **`progress/<this-file>.md`** — this entry.

## What did NOT land (and why)

- **The actual ASan recipe body**. Out of scope for this issue per
  the issue body's *"Scope of this issue: scaffolding only, NOT
  actual ASan running"* preamble. The body requires nightly Rust
  on the build host plus a non-trivial `lakefile.lean` change to
  support two Cargo profiles, and is deferred to a follow-up
  issue gated on a Linux + nightly-Rust worker host.
- **The Missing-work bullet 1 *flip* to past-tense**. The bullet
  is half-closed: the *"Scaffolded as …"* phrasing replaces the
  *"Sketch:"* sentence, but the bullet itself stays open because
  the recipe body has not yet executed. The flip lands with the
  follow-up issue. (Mirrors the *half-closed two-step* pattern
  from `.claude/skills/inventory-reconciliation/SKILL.md`.)

## Decisions

1. **Two-step env guard** (`command -v cargo` then
   `cargo +nightly --version`). Single check via just
   `cargo +nightly --version` would fire the same exit 2 in both
   "no cargo" and "no nightly toolchain" cases, but the diagnostic
   would be misleading on hosts without rustup at all. Splitting
   the check produces a more accurate diagnostic per case.
2. **Skeleton body exits 1, not 0**. The issue's verification
   bullet says *"NOT exit 0 — the env-guard must be load-bearing"*
   for the env-guard case. The TODO body (post-env-guard) is
   logically a different failure mode: env is fine, but the
   recipe is unimplemented. Exit 1 here mirrors *"sanitizer report
   or test failure"* in `sanitize-ffi.sh`'s exit-code semantics.
   Documented in the script's `usage()` block exit-codes section.
3. **`#TBD-VERIFY-PR` placeholder swap pattern**. Used the
   pattern from PR #2364: commit with the `#TBD-VERIFY-PR`
   placeholder, push, run `coordination create-pr` to learn the
   real PR number, then commit a one-line substitution and push.
   `bash scripts/check-inventory-links.sh` confirms `errors=0`
   and the only remaining placeholder warning is the
   pre-existing one at line 293 from PR #2382 (out of scope here).
4. **Follow-up issue body drafted as a PR comment, not minted**.
   Per the issue body's Deliverable 3, minting the follow-up is a
   planner action; drafting the body inline keeps the planner's
   next replan-triage cycle one copy-paste away.

## Verification

- `test -x scripts/sanitize-rust-ffi.sh` — passes.
- `bash scripts/sanitize-rust-ffi.sh --help` — exits 0 with the
  full usage block.
- `bash scripts/sanitize-rust-ffi.sh` (no args, on macOS host
  without nightly Rust) — exits 2 with the *"nightly Rust
  toolchain not available"* env-guard diagnostic.
- `bash scripts/sanitize-rust-ffi.sh --bogus` — exits 2 with a
  *"unknown argument"* usage error.
- `bash scripts/check-inventory-links.sh` — `errors=0,
  warnings=1` (the 1 remaining warning is the pre-existing
  `#TBD-VERIFY-PR` at line 293 from PR #2382, out of scope here).
- `lake build` — 199 / 199 jobs OK.
- `lake exe test` — *"All tests passed!"*.

## Quality metrics

- `sorry` count: unchanged (this PR adds shell + Markdown only;
  no Lean source touched).

## What remains (sibling work)

- **Follow-up issue (gated on Linux + nightly-Rust host)**:
  fill in the recipe body, run it, flip Missing-work bullet 1 to
  past-tense, and update the *Sanitizer recipe* paragraph to
  *Executed by PR #TBD-VERIFY-PR*. Draft body for the next
  planner is left as a comment on PR #2383.
- **Third sibling issue (deferred)**: link the ASan-instrumented
  `libminiz_oxide_shim.a` into `scripts/fuzz-inflate.sh` (the
  *"extended"* shape of the inventory bullet). Out of scope here.
- **UBSan support** for the Rust recipe (deferred per the
  precedent set by `sanitize-ffi.sh`'s ASan-first ramp).
- **Pre-existing `#TBD-VERIFY-PR` placeholder at
  `SECURITY_INVENTORY.md:293`** (under *Recent wins* — Cargo.lock
  paragraph, from PR #2382): out of scope here, but visible to
  the next planner sweep via `bash scripts/check-inventory-links.sh`.
