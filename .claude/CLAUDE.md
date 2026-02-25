# lean-zip

Lean 4 compression library: zlib/zstd via C FFI, plus pure-Lean tar and ZIP archives.
Toolchain: see `lean-toolchain`. Build system: Lake.

## Build and Test

    lake build          # build library + test executable
    lake exe test       # run all tests

Run from the project root. Tests require `testdata/` directory.

### NixOS / nix-shell

On NixOS, the project's `shell.nix` provides zlib/zstd/pkg-config.
If direnv is set up, the environment activates automatically on `cd`.
Otherwise, prefix commands with `nix-shell --run`:

    nix-shell --run "lake build && lake exe test"

**Important:** Lake caches `run_io` results (like `moreLinkArgs`) in
`.lake/`. If you switch between nix-shell and bare shell, or the nix
environment changes, you may need `rm -rf .lake` before building — a
plain `lake clean` is not sufficient to clear the cached link flags.

On systems where zlib and zstd are available system-wide (e.g. Ubuntu
with `libz-dev` and `libzstd-dev`), no nix-shell wrapper is needed.

## Autonomous Work Cycle

Agents are launched by `pod` (a Python TUI/CLI in the repo root), which
manages multiple concurrent agents. Each agent is an independent background
process. The dispatch strategy (configurable in `.pod/config.toml`)
assigns each session a worker type — **planner** (`/plan`) or one of the
worker types (`/feature`, `/review`, `/summarize`, `/meditate`), determined
by queue depth and label-aware dispatch.

**Planners** create one well-scoped work item as a GitHub issue, then
exit. They do the expensive orientation work (reading progress history,
understanding project state) and distill it into a self-contained issue
body so workers don't have to repeat it.

**Workers** claim an issue from the queue and execute it. They read the
issue body as their plan and do codebase orientation (reading the actual
files they'll modify) but skip historical orientation.

Each agent runs in its own git worktree on its own branch, coordinating
via GitHub issues, labels, and PRs.

**Non-interactive sessions**: These sessions run via `pod` with
`claude -p` — there is no human to answer questions. Never ask for
confirmation, approval, or "should I apply this?" — just do it.
If you find dead code, remove it. If a refactor improves the codebase,
commit it. The reflect step at the end is for recording what you did,
not for asking permission.

**Off-limits files**: Agents must not modify `.claude/CLAUDE.md` or
`PLAN.md`. Enforcement is at the `coordination create-pr` level —
PRs touching these files are rejected. Update skills in `.claude/skills/`
and commands in `.claude/commands/` instead.

### Planner sessions (`/plan`)

See `.claude/commands/plan.md` for the full prompt. Summary:

1. **Orient**: fetch, `coordination orient`,
   read last 5 progress entries, PLAN.md, sorry count
2. **Read all open issues**: full bodies, not just titles — understand
   what's already planned at the deliverable level
3. **Decide issue type**: `feature` / `review` / `summarize` / `meditate`,
   based on balance of recent sessions and summarize/meditate triggers
4. **Write self-contained plans** as GitHub issues with the appropriate label.
   Plans must NOT overlap with existing issues. Issues must be small enough
   to complete without context compaction. Target: max 3 deliverables,
   max 2 substantive files, ~200 lines of new code. See plan.md for sizing.
5. **Overlap guard**: re-fetch issues before posting to catch races
6. **Exit** — do not execute any code changes

### Worker sessions

Workers claim issues filtered by their type:
- `/feature` — implementation; reads `.claude/commands/feature.md`
- `/review` — proof quality; reads `.claude/commands/review.md`
- `/summarize` — PROGRESS.md analysis; reads `.claude/commands/summarize.md`
- `/meditate` — self-improvement; reads `.claude/commands/meditate.md`

Each worker reads `.claude/skills/agent-worker-flow/SKILL.md` for the standard
claim → branch → execute → verify → publish cycle.

## Coordination Reference

The `coordination` script handles all GitHub-based multi-agent coordination.
Session UUID is available as `$LEAN_ZIP_SESSION_ID` (exported by `pod`).

| Command | What it does |
|---------|-------------|
| `coordination orient` | List unclaimed/claimed issues, open PRs, PRs needing attention |
| `coordination plan [--label L] "title"` | Create GitHub issue with agent-plan + optional label; body from stdin |
| `coordination create-pr N [--partial] ["title"]` | Push branch, create PR closing issue #N (custom title optional), enable auto-merge, swap `claimed` → `has-pr`. With `--partial`: uses "Partial progress on #N", adds `replan` label. Rejects PRs touching `.claude/CLAUDE.md` or `PLAN.md`. |
| `coordination claim-fix N` | Comment on failing PR #N claiming fix (30min cooldown) |
| `coordination close-pr N "reason"` | Comment reason and close PR #N |
| `coordination list-unclaimed [--label L]` | List unclaimed agent-plan issues (FIFO order); optional label filter |
| `coordination queue-depth [L]` | Count of unclaimed issues; optional label for per-type count |
| `coordination claim N` | Claim issue #N — adds `claimed` label + comment, detects races |
| `coordination skip N "reason"` | Mark claimed issue as needing replan — removes `claimed`, adds `replan` label |
| `coordination add-dep N M` | Add `depends-on: #M` to issue #N's body; adds `blocked` label if #M is open. Use this (not raw `gh issue edit`) whenever a new dependency is discovered on an existing issue |
| `coordination check-blocked` | Unblock issues whose `depends-on` dependencies are all closed |
| `coordination release-stale-claims [SECS]` | Release claimed issues with no PR after SECS seconds (default 4h); **manual use only** — for claims from sessions on other machines that `pod` can't detect locally |
| `coordination lock-planner` | Acquire advisory planner lock (20min TTL, issue #8) |
| `coordination unlock-planner` | Release planner lock early |

**Issue lifecycle**: planner creates issue (label: `agent-plan`) →
worker claims it (adds label: `claimed`) → worker creates PR closing it
(label swaps to `has-pr`) → auto-merge squash-merges.
Issues marked `replan` (by skip or partial completion) are handled by the next planner.
Issues with `has-pr` appear in orient under "Issues with open PRs" and
are excluded from `list-unclaimed` and `queue-depth`.
**Partial completion**: worker uses `--partial` → label swaps to
`replan` (excluded from `list-unclaimed`). A planner creates a
new issue for remaining work, then closes the `replan` issue with
a link to the new one. This preserves full history.

**Dependencies**: Issues can declare `depends-on: #N` in their body.
`coordination plan` auto-adds the `blocked` label if any dependency is
open. `check-blocked` (run by `pod` each loop) removes `blocked` when
all dependencies close. Blocked issues are excluded from
`list-unclaimed` and `queue-depth`. Use this to split "write theorem
statements" from "prove theorems" — downstream work can reference the
statements (via `sorry`) before proofs are ready.

**Branch naming**: `agent/<first-8-chars-of-UUID>`
**Plan files**: `plans/<UUID-prefix>.md`
**Progress files**: `progress/<UTC-timestamp>_<UUID-prefix>.md`
(Pre-JSONL sessions use synthetic `0000NN` prefixes.)

## Code Organization

### Source layout

Survey `Zip/`, `ZipTest/`, and `ZipForStd/` directly. Every source file has a
module-level `/-! ... -/` docstring describing its purpose. Run `ls Zip/**/*.lean`
to orient. Key directories:
- `Zip/` — FFI wrappers and pure-Lean implementations
- `Zip/Native/` — Native Lean implementations (no FFI)
- `Zip/Spec/` — Formal specifications and correctness proofs
- `ZipForStd/` — Missing standard library lemmas (candidates for upstreaming)
- `ZipTest/` — Per-module tests

### Key documents
    PLAN.md              — Phased roadmap and development cycle (do not modify)
    PROGRESS.md          — Global milestones (updated by summarize agents)
    progress/            — Per-session progress entries (one file per session)
    plans/               — Per-session plan files (one file per active session)
    coordination         — Multi-agent coordination script (uses gh CLI)
    .claude/skills/      — Project-local skill files (proof patterns, workflow)

## Quality Standards

### Development cycle (from PLAN.md)
1. Type signature with `:= sorry`
2. Specification theorems with `:= by sorry`
3. Implementation
4. Auto-solve pass: run `try?` on each `sorry`. If `try?` succeeds, it
   generates info messages with replacement tactics — prefer the suggested
   replacement, but if it looks brittle (e.g. depends on nonlocal simp
   lemmas), use a simpler alternative and note why. Never leave `try?` in
   committed code. Use `bv_decide` when the goal involves `BitVec`.
5. Conformance tests (native vs FFI)
6. Manual proofs for goals that resist automation

### Native implementations
- Place in `Zip/Native/` (e.g. `Zip/Native/Crc32.lean`)
- Formal specs in `Zip/Spec/` (e.g. `Zip/Spec/Crc32.lean`)
- Keep FFI implementations intact as the fast path
- Start simple, optimize later with equivalence proofs

### Specifications

There are three levels of specification quality. Know which you're
writing and be honest about it:

1. **Tautological**: restates the implementation (`f x = fImpl x`).
   Proves nothing useful. Avoid.
2. **Characterizing properties**: mathematical properties independent
   of how the function is computed — algebraic identities
   (e.g. `crc32 (a ++ b) = combine (crc32 a) (crc32 b)`), structural
   invariants (prefix-freeness, Kraft inequality), or invertibility
   theorems (e.g. `decode (encode x) = x`). This is the gold standard.
3. **Algorithmic correspondence**: two implementations of the same
   algorithm agree (e.g. native decoder = reference decoder). Useful
   when the algorithm IS the spec (e.g. RFC pseudocode), but be
   explicit that this is translation validation — it catches bugs in
   the translation between data structures, not logical errors shared
   by both implementations.

When a function's "specification" is an algorithm (RFC pseudocode),
transcribing it into proof-friendly style and proving correspondence
IS the right approach. But characterize the mathematical building
blocks independently where possible. Don't pretend algorithmic
correspondence is characterization. See PLAN.md Phases B3–B4
for how this applies to DEFLATE.

- For optimized versions, specs are equivalence with the simple version.
- Do NOT modify theorem statements just to make proofs easier. If a spec
  is genuinely wrong or too strong, it can be changed — but document the
  rationale in PLAN.md

### Proofs
- Do NOT remove a working proof — refactoring a proof (same statement,
  better proof) is fine and encouraged; deleting a theorem is not
- Do NOT write multi-line tactic blocks without checking intermediate state
- Do NOT try the same approach more than 3 times — each retry must be
  fundamentally different (different tactic family, decomposition, or lemma)
- Do NOT use `native_decide` — it is forbidden in this codebase. When
  tempted to use it (e.g. for decidable propositions over large finite
  types), try `decide_cbv` instead, which uses kernel-level evaluation
  without native code generation
- Prefer `omega`, `decide`, `simp`, `grind` over manual arithmetic
- After getting a proof to work, refactor it immediately:
  combine steps, find minimal proof, extract reusable lemmas
- Think about generally useful constructions that could be upstreamed

### Tests
- Every new feature needs tests in `ZipTest/`
- Register new test modules in `ZipTest.lean`
- Include edge cases: empty input, single byte, large input
- Conformance: native compress + FFI decompress = original (and vice versa)

### Commits
- Conventional prefixes: `feat:`, `fix:`, `refactor:`, `test:`, `doc:`, `chore:`
- Each commit must compile and pass tests
- One logical change per commit
- `sorry` policy: intermediate commits with `sorry` are acceptable during
  multi-session development. Mark such commits clearly (e.g.
  `feat: add Adler32 spec (proofs WIP)`). Track remaining `sorry`s in
  `PLAN.md` for the next session.

### C FFI changes
- Match style in existing `c/*.c` files
- Check allocation failures, use overflow guards

## Failure Handling

- If `lake build` or `lake exe test` fails on a pre-existing issue (not
  your changes), log the failure in your progress entry and work around
  it or end the session. Do not loop retrying the same failure.
- If a proof is stuck after 3 fundamentally different attempts, leave it
  as `sorry`, document what was tried in your plan file (so future
  sessions don't repeat failed approaches), and move on.
- Implementation sessions: 3 consecutive iterations with no commits → end
  the session and document blockers in your progress entry. (This rule
  does not apply to review or self-improvement sessions, which may not
  produce commits.)
- If `/second-opinion` or `/reflect` is unavailable, skip and note in
  your progress entry.
- If conversation compaction has occurred: finish the current sub-task,
  commit, and wrap up with `--partial`. Do not start new deliverables
  after compaction — context quality degrades and the risk of introducing
  bugs or inconsistencies increases.

## Proof Strategies

Proof patterns are in `.claude/skills/`. The skills auto-trigger when relevant:
- `lean-monad-proofs` — Option/Except monad, do-notation, guard patterns
- `lean-uint-bitvec` — UInt8/16/32/BitVec conversions, bv_decide
- `lean-array-list` — ByteArray/Array/List indexing, length, take/drop
- `lean-dependent-types` — "motive not type correct", List.ofFn, visibility
- `lean-fuel-induction` — fuel independence, loop invariants, forIn avoidance
- `lean-simp-tactics` — simp only failures, Bool vs Prop, let bindings
- `lean-no-mathlib` — Mathlib tactic unavailable? Use grind/omega instead

The following apply everywhere and are worth keeping here:

- **No Mathlib**: Use `grind` for algebraic goals (subsumes `ring`). Use
  `by_cases + exfalso` for contradiction (no `by_contra`). See skill for full list.
