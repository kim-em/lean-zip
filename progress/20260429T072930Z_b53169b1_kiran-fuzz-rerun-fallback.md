# 2026-04-29T07:29Z — feature session b53169b1

Session type: `/feature` (worker).
Issues touched: #2366 (claimed → skipped), #2369 (claimed → fallback
path executed), #2380 (created — sibling follow-up for in-repo
`Handle.read` regression harness).

## Summary

Closed #2369 via the issue's documented **Fallback path**: the
verbatim re-run of Kiran's original AFL++-driven fuzz harness from
[the blog post](https://kirancodes.me/posts/log-who-watches-the-watchers.html)
is not feasible from a single agent session on the project's current
host environment, for two structural reasons documented below. As
specified by the issue body's *Fallback path*:

- the *Missing work* bullet under
  [`SECURITY_INVENTORY.md`](../SECURITY_INVENTORY.md) `### Lean
  Runtime` is left **unchanged** — no Executed flip without a real
  run;
- a sibling follow-up issue has been opened (#2380) for an in-repo
  deterministic regression-harness reconstruction targeting
  `Handle.read` / `Stream.read` directly, modelled after
  [`ZipTest/FuzzInflate.lean`](../ZipTest/FuzzInflate.lean) /
  [`scripts/fuzz-inflate.sh`](../scripts/fuzz-inflate.sh) /
  [`ZipFuzzInflate.lean`](../ZipFuzzInflate.lean);
- this progress entry captures the URLs reached, the
  dependency-resolution friction, and the timestamps, so a future
  session can reconstruct the decision without re-doing the
  reachability check.

## Issue ledger

- **#2366** — sanitize-ffi.sh re-run + April 2026 ASan + UBSan claim
  refresh: claimed and immediately skipped per the issue body's
  *"Platform requirement: Linux only"* preamble. Apple Clang's
  `cc -print-file-name=libasan.so` is not an absolute path on this
  host (Darwin / arm64-apple-darwin23.6.0), so
  `scripts/sanitize-ffi.sh`'s environment guard exits 2 before any
  build runs. Released back to the queue with the standard
  platform-mismatch reason; this is the fifth release on that
  issue and the third specifically for this reason (preceding
  releases by `cbd9c8a0`, `82c9309b`, `d02bf9c1`, `b73ca1b0`).
- **#2369** — re-run Kiran's original fuzz harness on
  `v4.30.0-rc2`: claimed, executed via Fallback path. See
  *Fallback decision rationale* below.
- **#2380** — Track E (Lean Runtime): in-repo deterministic
  `Handle.read` / `Stream.read` regression harness. Created in
  this session as the sibling follow-up specified by #2369's
  *Fallback path* §3.

## Fallback decision rationale

Two structural reasons combine to make the verbatim re-run a
multi-session task that does not fit a single feature session on
this worktree's host environment:

### Reason 1: harness fundamentally targets the kiranandcode fork's CLI, not `kim-em/lean-zip` master

The harness in
[kiranandcode/lean-zip](https://github.com/kiranandcode/lean-zip)
`fuzz/README.md` invokes:

```
afl-fuzz -i fuzz/corpus/zip -o fuzz/output -t 10000 -m none \
    -- .lake/build/bin/lean-zip extract @@ -d /tmp/fuzz-out
```

— i.e. it consumes `.lake/build/bin/lean-zip`, the **CLI binary
defined in the fork's `ZipCli.lean` (5 099 bytes)**. That CLI does
not exist in `kim-em/lean-zip` master:

```
$ grep -n "lean_exe\|lean_lib\|exe " lakefile.lean | head -5
122:lean_lib Zip
163:lean_lib ZipTest where
167:lean_exe test where
170:lean_exe bench where
173:lean_exe fuzz_inflate where
```

— `test`, `bench`, `fuzz_inflate` only. No `lean-zip` CLI binary.

The fork's `Zip/` directory is also dramatically smaller than
current master:

| `kim-em/lean-zip` master `Zip/` | `kiranandcode/lean-zip` `Zip/` |
| --- | --- |
| `Archive.lean` | `Archive.lean` |
| `Basic.lean` | — |
| `Checksum.lean` | — |
| `Gzip.lean` | — |
| `MinizOxide.lean` | — |
| `Native/` | `Native/` |
| `RawDeflate.lean` | — |
| `Spec/` | `Spec/` |
| `Tar.lean` | `Tar.lean` |

Verified via:

```
$ ls Zip
Archive.lean  Basic.lean  Checksum.lean  Gzip.lean  MinizOxide.lean
Native        RawDeflate.lean  Spec        Tar.lean
$ gh api repos/kiranandcode/lean-zip/contents/Zip --jq '.[].name'
Archive.lean
Native
Spec
Tar.lean
```

The fork's `lean-toolchain` is also pinned to the **older**
`leanprover/lean4:v4.29.0-rc4` (verified via raw GitHub fetch on
2026-04-29T07:29Z), so a verbatim re-run targets the pre-fix
runtime — **not** the `v4.30.0-rc2` runtime whose closure we are
trying to confirm.

To make the harness exercise current `kim-em/lean-zip` master on
`v4.30.0-rc2` would require:

1. Cloning the fork to `/tmp` per the project's *"clone fresh to
   /tmp"* rule (free / fast — would have happened in this session
   if the rest of the chain were tractable),
2. Bumping the fork's `lean-toolchain` to `v4.30.0-rc2` and
   re-resolving its lake dependencies under elan (modest setup
   cost),
3. Either porting the fork's `ZipCli.lean` surface
   (`extract` / `gunzip` / `inflate` / `untar` / `create`) onto
   current master's API, **or** swapping the fork's `Zip/`
   directory for current master's `Zip/` (which then breaks
   `ZipCli.lean` until ported, since the fork's stripped-down API
   diverges substantially from current master's).

That is the substantial-scope porting work that #2380 takes on as
an *in-repo* harness — sidestepping the AFL++ external dependency
entirely.

### Reason 2: AFL++ on macOS is not installable / runnable in a single-session budget

```
$ which afl-fuzz afl-clang-fast 2>&1
afl-fuzz not found
afl-clang-fast not found
$ brew info afl++ 2>&1 | head -5
==> afl++: stable 4.35c (bottled)
American Fuzzy Lop++
https://aflplus.plus/
Not installed
==> Dependencies
Required (2): llvm, python@3.14
```

`afl++` requires the full LLVM toolchain as a Homebrew dependency
(multi-GB download, 10-20+ minutes of setup on a cold cache). Even
if installed, AFL++ on macOS has known performance and
panic-detection limitations relative to Linux (the original blog
post implicitly assumed Linux-style fork-server semantics; macOS's
`fork(2)` interaction with the Lean runtime under
`afl-clang-fast`'s instrumentation is not a recipe this project
has audited).

A meaningful afl-fuzz run is hours-to-days of wall-clock time at
minimum; the original blog post's findings emerged from an
extended sweep, not a 5-minute session-budget run. Even setting up
the chain to the point of a single iteration is incompatible with
the *"reasonable time"* qualifier in #2369's Fallback-trigger
clause.

### Combined effect

These two reasons compound: even if AFL++ were already installed
locally, the harness would still not test current master without
the porting in *Reason 1*. And even if the porting were already
done, it would still not run in a single-session time budget on
this host. Hence the Fallback path.

## What changed (#2369 — fallback path)

### `SECURITY_INVENTORY.md`

**Unchanged**, per #2369's Fallback path §3 — *"leave the
Missing-work bullet's text unchanged (no Executed flip without a
real run)"*:

```
$ git diff origin/master -- SECURITY_INVENTORY.md
```

(empty — no inventory edits in this session).

The *"re-run the original fuzz harness from
https://kirancodes.me/posts/log-who-watches-the-watchers.html
against current master on v4.30.0-rc2 to confirm closure of the
runtime buffer-overflow class"* bullet remains in the *Missing
work* sub-list of `### Lean Runtime`. It will be flipped only when
the in-repo replacement (#2380) lands and supersedes it.

### `progress/20260429T072930Z_b53169b1_kiran-fuzz-rerun-fallback.md`

This file. Records what was attempted, the friction points, the
sibling follow-up, and the cross-links so #2369 can be closed via
the PR's `closes #2369` mechanism without ambiguity about whether
the inventory bullet was supposed to flip.

## Verification

- `lake build` — full project build succeeds (199/199 jobs, no
  source changes in this session). Confirmed before progress entry
  was committed.
- `lake exe test` — full test suite passes (no source changes;
  re-run as a smoke check after the worktree reset).
- `bash scripts/check-inventory-links.sh` — `errors=0, warnings=0`
  (no inventory edits; the warning surface present in the previous
  session for the `#TBD-VERIFY-PR` placeholder pattern in PR #2378
  has since been resolved by that PR's merge as `a5f10a7`, the
  starting commit for this session).
- `git diff origin/master..HEAD --stat` — single new file
  (`progress/20260429T072930Z_b53169b1_kiran-fuzz-rerun-fallback.md`),
  no other surface area touched.
- Sorry count unchanged (0).

## Decisions

- **Fallback path, not partial-PR.** #2369's deliverables explicitly
  enumerate the Fallback path as a complete outcome (verification
  clause: *"If the Fallback path was taken, `git diff master --
  SECURITY_INVENTORY.md` is empty; the new follow-up issue number
  is cited in this issue's closing comment"*). A `--partial` PR is
  the wrong shape here — there is no half-finished inventory edit;
  the Fallback path is the complete deliverable.
- **In-repo harness, not AFL++ in-repo.** #2380's deliverables
  deliberately avoid AFL++ as an external dependency, mirroring
  `FuzzInflate`'s deterministic-xorshift / wall-clock-budgeted
  pattern. Coverage-guided fuzzing is a separate infrastructure
  question (and would re-introduce the same AFL+++/Linux/macOS
  questions that ruled out the verbatim re-run here).
- **Sibling follow-up created at issue level, not PR level.**
  #2380 is created independently so that the next planner /
  feature session can claim it without depending on this PR's
  merge (the in-repo harness is the forward-looking regression
  artefact and should not block on Fallback-path bookkeeping).

## What remains (this row only)

The *Missing work* bullet under `### Lean Runtime` remains open
after this PR lands. #2380 supersedes it: when #2380's PR lands, it
flips the bullet to a Recent-wins one-liner citing the in-repo
harness (per #2380's deliverable §4 — *"Inventory bullet flip"*).

## Cross-links

- Closes #2369 (Fallback path).
- Releases #2366 back to the queue with platform-mismatch reason
  (5th release on that issue; 3rd specifically platform).
- Sibling follow-up: #2380.
- Parent inventory bullet:
  [`SECURITY_INVENTORY.md`](../SECURITY_INVENTORY.md) `### Lean
  Runtime` *Missing work* — *"re-run the original fuzz harness …"*
  (citation by stable identifier per #2345 / PR #2353).
- Original harness reference:
  [kiranandcode/lean-zip](https://github.com/kiranandcode/lean-zip)
  `fuzz/` (kept as the historical reference for the
  pathological-input families).
- Upstream fix:
  [leanprover/lean4#13388](https://github.com/leanprover/lean4/issues/13388)
  / [PR #13392](https://github.com/leanprover/lean4/pull/13392) —
  the `lean_io_prim_handle_read` buffer-overflow fix consumed via
  PR #2352's toolchain bump.
- Sibling post-bump verification (different surface; macOS-blocked
  in this session): #2366.

## Host context (for forensic reconstruction)

```
$ uname -a
Darwin carica 23.6.0 Darwin Kernel Version 23.6.0: Mon Jul 29 21:13:04 PDT 2024; root:xnu-10063.141.2~1/RELEASE_ARM64_T6020 arm64
$ sw_vers
ProductName:    macOS
ProductVersion: 14.6.1
BuildVersion:   23G93
$ cc --version | head -1
Apple clang version 15.0.0 (clang-1500.3.9.4)
$ cat lean-toolchain
leanprover/lean4:v4.30.0-rc2
```

Starting commit: `a5f10a76990c235a8661be49d73ae56acec67257` — *feat:
clamp MinizOxide.compress level argument to 0–9 (closes #2374)
(#2378)*. Branch: `agent/b53169b1`.

🤖 Progress entry prepared with Claude Code
