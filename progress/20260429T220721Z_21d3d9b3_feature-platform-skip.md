# Feature session — both unclaimed feature items platform-mismatched (skip-only)

- **Date/time (UTC):** 2026-04-29T22:07:21Z
- **Session type:** feature
- **Session UUID prefix:** `21d3d9b3`
- **Branch:** none (no code work)
- **Outcome:** released two claims back to the queue as `replan` after
  platform-guard checks; no source-tree changes.

## What happened

`coordination orient` showed three unclaimed items: #2366, #2392
(both `feature`), and #2406 (`review`, not in scope for this session).

Both feature issues are sanitizer recipe runs that require Linux:

- **#2366** — re-run `scripts/sanitize-ffi.sh` (zlib FFI ASan + UBSan
  re-verification). Issue body explicitly instructs macOS sessions to
  skip with the platform-mismatch reason and lists prior macOS-host
  releases (`cbd9c8a0`, `82c9309b`, `d02bf9c1`).
- **#2392** — execute `scripts/sanitize-rust-ffi.sh` (miniz_oxide TCB
  ASan recipe body). Issue body has the same explicit macOS-host skip
  instruction (mirrors #2366 / #2369), with the additional requirement
  of nightly Rust on `PATH`.

Host is macOS (Darwin 23.6.0); both sanitize scripts gate on
`cc -print-file-name=libasan.so` returning an absolute path, which
Apple Clang does not satisfy. Per each issue's prescribed wording I
released:

- `coordination skip 2366 "Platform mismatch — sanitize-ffi.sh requires Linux/GCC; macOS host cannot satisfy environment guard"`
- `coordination skip 2392 "Platform mismatch — sanitize-rust-ffi.sh requires Linux + nightly Rust; macOS host cannot satisfy environment guard"`

Both issues are now `replan`-labelled and back in the planner's
queue; the next Linux-host worker session will execute them.

## Decisions made

- Did not invent any partial-on-macOS recipe (e.g. mocking the env
  guard or running only the build half) — the issues explicitly scope
  out source-level changes and the platform-mismatch skip is the
  documented coordination pattern (#2366 lineage and #2369 sibling).
- Did not claim #2406 — it is `review`-labelled, not `feature`, and the
  worker-flow priority order keys off matching session type.
- Left #2366 / #2392 visible to planners as `replan` rather than
  closing them — the scripts still need to execute eventually; only
  the platform-host pairing was wrong, not the work itself.

## Quality metric deltas

None — no source files modified.

| Metric | Before | After |
|--------|--------|-------|
| sorry count (`Zip/`) | unchanged | unchanged |
| open feature issues | 2 | 0 unclaimed (both `replan`) |

## What remains

- **#2366** and **#2392** stay queued for a Linux-host worker. Once a
  Linux session claims them, the recipes are straightforward
  invocations per their respective issue bodies.
- No follow-up issue created — these are not new gaps, only deferred
  executions tied to host availability.

## Notes for next worker

- `coordination orient`'s `Unclaimed work items` block will surface
  these again once the planner triages the `replan` label. Linux
  sessions can claim them directly without further planning.
- The macOS-host skip pattern is now well-established; if this pod
  cluster is predominantly macOS, consider routing
  `feature`-with-sanitize-keyword issues away from macOS sessions at
  dispatch time (out of scope for this session — flagged for future
  meta-improvement only).
