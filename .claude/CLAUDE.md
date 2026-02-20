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

When told to "start work" (or `/start`), follow this cycle. The cycle
balances three activities: **new work**, **review**, and **self-improvement**.
Check `PROGRESS.md` to dynamically adjust the balance — if reviews are
consistently finding nothing, do fewer; if they're finding problems, do more.
Default to alternating: implementation session, then review session.

**Anti-rationalization check**: A common failure mode is to identify the
correct session type from the balance, then override it by framing
implementation work as "blocking" or "urgent." Sorries, incomplete
proofs, and unfinished features are almost never true blockers — other
session types can proceed with sorries in place. If you find yourself
writing "should do X, but Y is more important" — do X. The only genuine
exception is a broken build that prevents all other work.

### Step 1: Orient

Record the starting commit: `git rev-parse HEAD`. Check `git status` — if
the repo is dirty with someone else's uncommitted work, document it in
`PROGRESS.md` and work carefully to avoid mixing changes.

Read these files to understand current state:
- `SESSION.md` — current working state (sorry locations, failed approaches)
- `PROGRESS.md` — what previous sessions accomplished and found
- `PLAN.md` — any unfinished plan from last session
- `VERIFICATION.md` — the phased roadmap and development cycle

Record the current `sorry` count: `grep -rc sorry Zip/ || true`

Decide whether this should be an **implementation session**, a **review
session**, or a **self-improvement session** based on the balance.

### Step 2: Plan

Write a concrete plan to `PLAN.md` with deliverables scoped to one session
(aim for a few hundred lines of changes — small enough to review and verify).
If `PLAN.md` has unfinished items, continue from there.

For implementation sessions, priority order:
1. Unfinished items in `PLAN.md`
2. Next deliverable from the current VERIFICATION.md phase

For new native implementations, follow the development cycle in
VERIFICATION.md: type signature → spec theorems → implementation →
conformance tests → proofs.

### Step 3: Execute

**Implementation sessions:**
- Execute the plan, running `lake build` after each coherent chunk of changes.
  Use targeted builds when possible (e.g. `lake build Zip.Native.Crc32`)
  for faster iteration; do a full `lake build` before committing
- Run `lake exe test` periodically to verify tests pass
- Commit with conventional prefixes (`feat:`, `fix:`, `refactor:`, `test:`, `doc:`)

**Review sessions** — each session should pick **one or two** focus
areas and go deep, rather than superficially covering everything.
Rotate through the areas across sessions so they all get attention
over time. Focus areas:
- **Refactoring and proof improvement**: This is the top review priority.
  Are proofs minimal? Can steps be combined? Would extracting a lemma
  improve readability or enable reuse? Are there generally useful lemmas
  that should be factored out? Record lemmas that might be worth
  upstreaming to Lean's standard library in PLAN.md.
- **Slop detection**: dead code, duplicated logic, verbose comments,
  unused imports, other signs of AI-generated bloat
- **Security**: check for new issues in recent code, verify past fixes
- **Lean idioms**: newer APIs, `grind`, `omega`, `mvcgen`, idiomatic style.
  Also look for opportunities to replace `partial` or fuel-based
  implementations with definitions that have proper termination proofs —
  this pays off later with easier verification. Look for `xs[i]!`
  runtime bounds checks that could be replaced with proven-bounds access
  `xs[i]` when the information to prove the bound is already in scope.
  Remember that in `if` and `for` you need `h :` syntax to capture the
  relevant hypothesis (e.g. `if h : i < xs.size then xs[i] ...`).
- **Toolchain**: check if a newer stable Lean release is available; if so,
  upgrade `lean-toolchain`, fix breakage, and revert if tests can't be
  made to pass. Only attempt toolchain upgrades when all tests pass first
- **Prompting and skills**: is `.claude/CLAUDE.md` still accurate? Are
  commands and skills in `.claude/` still useful? Trim stale guidance,
  add missing guidance. Consider writing new skills for recurring
  patterns (profiling, proof techniques, etc.)

As the project grows, also focus reviews on particular modules rather
than reviewing everything at once.

**Self-improvement sessions** (require at least one tangible output):
- Write new skills in `.claude/skills/` for recurring patterns
- Research best practices (Lean proof style, performance tuning, etc.)
- Improve the harness based on accumulated experience

### Step 4: Verify

After implementation:
- Run `lake build && lake exe test` one final time
- Check `sorry` count: `grep -rc sorry Zip/ || true`. If it increased vs
  session start, investigate — this may indicate a proof regression
- Review changes: `git diff <starting-commit>..HEAD`
- Use `/second-opinion` to get Codex review of the changes (if unavailable,
  skip and note in PROGRESS.md)
- Small issues: fix immediately. Substantial issues: add to `PLAN.md`

### Step 5: Document

Update `SESSION.md` with current working state:
- `sorry` count and locations (file:line)
- For incomplete proofs: approaches tried, what failed, what to try next
- Any in-progress proof goal states
- Known good commit (last commit where `lake build && lake exe test` passed)
- Next action: what the next session should do first

Add a session entry to the top of `PROGRESS.md` with:
date, session type, what was accomplished, decisions made, what remains.

### Step 6: Reflect

End every session by running `/reflect`. If it suggests improvements to
`.claude/CLAUDE.md`, commands, or skills, make those changes and commit.

## Code Organization

### Source layout
    Zip/Basic.lean       — Zlib compress/decompress (@[extern])
    Zip/Gzip.lean        — Gzip + streaming + file helpers
    Zip/Checksum.lean    — CRC32, Adler32 (@[extern])
    Zip/RawDeflate.lean  — Raw deflate + streaming
    Zip/Zstd.lean        — Zstandard + streaming + file helpers
    Zip/Binary.lean      — Byte packing: LE integers, octal, strings
    Zip/Tar.lean         — Tar create/extract/list, .tar.gz streaming
    Zip/Archive.lean     — ZIP create/extract/list (with ZIP64)
    Zip/Handle.lean      — IO.FS.Handle shims (seek, fileSize, symlink)
    Zip/Native/Adler32.lean  — Native Adler-32
    Zip/Native/Crc32.lean    — Native CRC-32 (table-driven)
    Zip/Native/BitReader.lean — LSB-first bit-level reader for DEFLATE
    Zip/Native/Inflate.lean  — Native DEFLATE decompressor (RFC 1951)
    Zip/Native/Gzip.lean     — Native gzip/zlib decompression (RFC 1952/1950)
    Zip/Spec/            — Formal specifications to prove against
    Zip.lean             — Re-exports all modules
    ZipForStd/           — Missing std library lemmas (candidates for upstreaming)
    ZipForStd.lean       — Root import for ZipForStd

### Test layout
    ZipTest.lean         — Test runner entry point
    ZipTest/Helpers.lean — Shared test utilities
    ZipTest/*.lean       — Per-module tests
    testdata/            — Binary fixtures

### Key documents
    ARCHITECTURE.md      — Technical architecture
    VERIFICATION.md      — Phased roadmap and development cycle (do not modify)
    PROGRESS.md          — Session-by-session progress log
    PLAN.md              — Current session working plan
    SESSION.md           — Current working state (overwritten each session)

## Quality Standards

### Development cycle (from VERIFICATION.md)
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
- **Avoid tautological specs.** A specification that merely restates the
  implementation (e.g. `crc32 x = crc32Impl x`) proves nothing useful.
  Aim for logical characterisations that pin down the *meaning* of a
  function independently of how it is computed — algebraic properties
  (e.g. `crc32 (a ++ b) = combine (crc32 a) (crc32 b)`), equivalence
  with a reference definition, or key invariants. When a full
  characterisation is hard, state useful properties instead.
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
  your changes), log the failure in `PROGRESS.md` and work around it or
  end the session. Do not loop retrying the same failure.
- If a proof is stuck after 3 fundamentally different attempts, leave it
  as `sorry`, document what was tried in PLAN.md (so future sessions
  don't repeat failed approaches), and move on.
- Implementation sessions: 3 consecutive iterations with no commits → end
  the session and document blockers in PLAN.md and SESSION.md. (This rule
  does not apply to review or self-improvement sessions, which may not
  produce commits.)
- If `/second-opinion` or `/reflect` is unavailable, skip and note in
  `PROGRESS.md`.

## Proof Strategies

This section accumulates proof patterns discovered during development.
Update it during review and reflect sessions.

- **No Mathlib — unavailable tactics and names**: This project uses only
  Lean 4 core + std. The following are NOT available:
  - Tactics: `ring`, `set`, `push_neg`, `by_contra`, `field_simp`, `positivity`,
    `polyrith`, `norm_num` (the Mathlib version), `rcases`/`obtain`
  - Names: `le_refl` (use `Nat.le.refl` or `by omega`),
    `Nat.gt_of_not_le` (use `by omega`), `congr_arg` (use `congrArg`)
  - For contradiction proofs, use `by_cases` + `exfalso` instead of `by_contra`
  For algebraic goals (commutativity, associativity, distributivity),
  use `grind` — it fully subsumes Mathlib's `ring` tactic.
  When in doubt, prefer `omega`, `simp`, `grind`, `by_cases`, `exact`
  over anything that might be Mathlib-only.
- **Build missing API, don't work around it**: If a proof is blocked by
  missing lemmas for standard types (ByteArray, Array, List, UInt32, etc.),
  add the missing lemma to `ZipForStd/` in the appropriate namespace.
  For example, if `ByteArray.foldl_toList` is missing, add it in
  `ZipForStd/ByteArray.lean` in the `ByteArray` namespace. These lemmas
  are candidates for upstreaming to Lean's standard library — write them
  as if they belonged there. Don't use workarounds like going through
  `.data.data.foldl` when the right fix is a proper API lemma.
- **bv_decide for UInt32/BitVec**: Effective for bitvector reasoning.
  Proved CRC linearity (`crcBit_xor_high`) and the 8-fold split
  (`crcBits8_split`) each in one line. Caveat: fails when expressions
  contain `UInt32.ofNat x.toNat` (abstracted as opaque).
- **UInt8→UInt32 conversion for bv_decide**: When `bv_decide` fails on
  `UInt32.ofNat byte.toNat`, rewrite it to `⟨byte.toBitVec.setWidth 32⟩`
  using `BitVec.ofNat_toNat`. Then use `show` + `congr 1` to expose the
  inner `BitVec` for `bv_decide`. Pattern:
  ```lean
  rw [UInt32_ofNat_UInt8_toNat]  -- rewrites via BitVec.ofNat_toNat
  show UInt32.ofBitVec (... bitvec expr ...) = UInt32.ofBitVec (...)
  congr 1; bv_decide
  ```
- **Avoid `for`/`while` in spec functions**: In `Option`/`Except` monads,
  `return` inside a `for` loop exits the loop (producing `some`), not the
  function. Use explicit recursive helper functions instead — they're also
  easier to reason about in proofs. Reserve `for`/`while` for `IO` code.

## Current State Summary

Updated by agent at the end of each session.

- **Toolchain**: leanprover/lean4:v4.29.0-rc1
- **Phase**: Phase 3 (verified decompressor) — in progress
- **Sorry count**: 4 (all in InflateCorrect.lean — staged theorem statements)
- **Last session**: 2026-02-20 (impl: resolveLZ77 properties + readBit_toBits proof)
- **Last review**: 2026-02-20 (Huffman proofs deep, dead code removal, Codex review)
