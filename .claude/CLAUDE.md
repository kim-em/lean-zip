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

Agents are launched by `./go`, which assigns each session a mode:
**planner** (`/plan`) or **worker** (`/work`). The mode is determined
by queue depth — if fewer than 3 unclaimed work items exist, the session
is a planner; otherwise a worker. (We may later move this decision into
the Claude session itself if more context-aware dispatch proves valuable.)

**Planners** create one well-scoped work item as a GitHub issue, then
exit. They do the expensive orientation work (reading progress history,
understanding project state) and distill it into a self-contained issue
body so workers don't have to repeat it.

**Workers** claim an issue from the queue and execute it. They read the
issue body as their plan and do codebase orientation (reading the actual
files they'll modify) but skip historical orientation.

Each agent runs in its own git worktree on its own branch, coordinating
via GitHub issues, labels, and PRs.

**Non-interactive sessions**: These sessions run via `./go` with
`claude -p` — there is no human to answer questions. Never ask for
confirmation, approval, or "should I apply this?" — just do it. If you
propose a `./.claude/CLAUDE.md` change for the current project, apply it.
If you find dead code, remove it. If a refactor improves the codebase,
commit it. The reflect step at the end is for recording what you did,
not for asking permission.

**Anti-rationalization check**: A common failure mode is to identify the
correct session type from the balance, then override it by framing
implementation work as "blocking" or "urgent." Sorries, incomplete
proofs, and unfinished features are almost never true blockers — other
session types can proceed with sorries in place. If you find yourself
writing "should do X, but Y is more important" — do X. The only genuine
exception is a broken build that prevents all other work.

### Planner sessions (`/plan`)

See `.claude/commands/plan.md` for the full prompt. Summary:

1. **Orient**: fetch, `coordination orient`,
   read last 5 progress entries, VERIFICATION.md, sorry count
2. **Read all open issues**: full bodies, not just titles — understand
   what's already planned at the deliverable level
3. **Decide session type**: implementation / review / self-improvement,
   based on balance of recent sessions
4. **Write self-contained plans** as GitHub issues — one per atomic
   concern. Each must include: current state, specific files,
   deliverables, "done" criteria, verification steps. If orientation
   reveals multiple orthogonal pieces, create multiple issues rather
   than bundling them. Plans must NOT overlap with existing issues.
5. **Overlap guard**: re-fetch issues before posting to catch races
6. **Exit** — do not execute any code changes

### Worker sessions (`/work`)

See `.claude/commands/work.md` for the full prompt. Summary:

1. **Claim**: `coordination list-unclaimed`, pick oldest,
   `coordination claim N`
2. **Set up**: create branch, record starting commit + sorry count
3. **Codebase orientation**: read the specific files in the plan,
   understand current code state
4. **Verify assumptions**: sorry count, files exist, plan not stale.
   If stale: `coordination skip N "reason"`, try next issue
5. **Execute**: follow the plan's deliverables (see session types below)
6. **Verify**: `lake build && lake exe test`, sorry count delta,
   `git diff`, `/second-opinion`
7. **Publish**: progress entry, push, `coordination create-pr N`
   (auto-merge handles the rest)
8. **Reflect**: `/reflect`, update `.claude/` if needed

### Session types (for both planners and workers)

The cycle balances three activities: **new work**, **review**, and
**self-improvement**. Read recent `progress/` entries to dynamically
adjust the balance — if reviews are consistently finding nothing, do
fewer; if they're finding problems, do more. Default to alternating:
implementation session, then review session.

**Implementation sessions** — priority order:
1. PRs needing attention (merge conflicts, failing CI) — rebase, resolve
   conflicts, and get the PR green again
2. Next deliverable from the current VERIFICATION.md phase

For new native implementations, follow the development cycle in
VERIFICATION.md: type signature → spec theorems → implementation →
conformance tests → proofs.

Execute by running `lake build` after each coherent chunk of changes.
Use targeted builds when possible (e.g. `lake build Zip.Native.Crc32`)
for faster iteration; do a full `lake build` before committing.
Run `lake exe test` periodically.
Commit with conventional prefixes (`feat:`, `fix:`, `refactor:`, `test:`, `doc:`).

**Review sessions** — each session should pick **one or two** focus
areas and go deep, rather than superficially covering everything.
Rotate through the areas across sessions so they all get attention
over time. Focus areas:
- **Refactoring and proof improvement**: This is the top review priority.
  Are proofs minimal? Can steps be combined? Would extracting a lemma
  improve readability or enable reuse? Are there generally useful lemmas
  that should be factored out? Record lemmas that might be worth
  upstreaming to Lean's standard library in the plan file.
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
- **File size and organization**: Files over 500 lines are candidates
  for splitting; never let a file grow past 1000 lines. Check with
  `wc -l Zip/**/*.lean`. Split along natural boundaries (e.g. separate
  types/definitions from proofs, or split by sub-topic). Don't hesitate
  to restructure existing files if definitions feel out of place — move
  them to where they logically belong, even if that means creating new
  files. Update the source layout table in this file when splitting.

As the project grows, also focus reviews on particular modules rather
than reviewing everything at once.

**Self-improvement sessions** (require at least one tangible output):
- Write new skills in `.claude/skills/` for recurring patterns
- Research best practices (Lean proof style, performance tuning, etc.)
- Improve the harness based on accumulated experience

## Coordination Reference

The `coordination` script handles all GitHub-based multi-agent coordination.
Session UUID is available as `$LEAN_ZIP_SESSION_ID` (exported by `./go`).

| Command | What it does |
|---------|-------------|
| `coordination orient` | List unclaimed/claimed issues, open PRs, PRs needing attention |
| `coordination plan "title"` | Create GitHub issue with agent-plan label; body from stdin |
| `coordination create-pr N` | Push branch, create PR closing issue #N, enable auto-merge, swap `claimed` → `has-pr` |
| `coordination claim-fix N` | Comment on failing PR #N claiming fix (30min cooldown) |
| `coordination close-pr N "reason"` | Comment reason and close PR #N |
| `coordination list-unclaimed` | List unclaimed agent-plan issues (FIFO order) |
| `coordination queue-depth` | Count of unclaimed issues (used by `./go` for dispatch) |
| `coordination claim N` | Claim issue #N — adds `claimed` label + comment, detects races |
| `coordination skip N "reason"` | Mark claimed issue as skipped — removes `claimed`, adds `skip` label |
| `coordination check-blocked` | Unblock issues whose `depends-on` dependencies are all closed |
| `coordination lock-planner` | Acquire advisory planner lock (10min TTL, issue #8) |
| `coordination unlock-planner` | Release planner lock early |

**Issue lifecycle**: planner creates issue (label: `agent-plan`) →
worker claims it (adds label: `claimed`) → worker creates PR closing it
(label swaps to `has-pr`) → auto-merge squash-merges.
Skipped issues (label: `skip`) can be revised by the next planner.
Issues with `has-pr` appear in orient under "Issues with open PRs" and
are excluded from `list-unclaimed` and `queue-depth`.

**Dependencies**: Issues can declare `depends-on: #N` in their body.
`coordination plan` auto-adds the `blocked` label if any dependency is
open. `check-blocked` (run by `./go` each loop) removes `blocked` when
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
    Zip/Native/Deflate.lean  — Native DEFLATE compressor (stored + fixed Huffman)
    Zip/Native/Gzip.lean     — Native gzip/zlib compression + decompression (RFC 1952/1950)
    Zip/Spec/Huffman.lean    — Canonical Huffman code spec (allCodes, prefix-free)
    Zip/Spec/Deflate.lean    — DEFLATE bitstream spec (RFC 1951)
    Zip/Spec/BitstreamCorrect.lean — BitReader ↔ bytesToBits correspondence
    Zip/Spec/HuffmanCorrect.lean   — HuffTree ↔ Huffman.Spec correspondence
    Zip/Spec/DecodeCorrect.lean    — Block-level decode correctness
    Zip/Spec/DynamicTreesCorrect.lean — Dynamic Huffman tree decode correctness
    Zip/Spec/InflateCorrect.lean   — Stream-level inflate correctness theorem
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
    PROGRESS.md          — Global milestones (updated rarely)
    progress/            — Per-session progress entries (one file per session)
    plans/               — Per-session plan files (one file per active session)
    coordination         — Multi-agent coordination script (uses gh CLI)

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
correspondence is characterization. See VERIFICATION.md Phases 3–4
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
- **ByteArray/Array/List indexing**: `data.data[pos] = data[pos]` (where
  `data : ByteArray`) is `rfl`. But `data.data.toList[pos] = data[pos]`
  needs `simp [Array.getElem_toList]; rfl` — the `simp` handles the
  `List.getElem → Array.getElem` step, and the `rfl` handles the
  definitional `Array.getElem data.data pos = ByteArray.getElem data pos`.
- **UInt32 bit operations → Nat.testBit**: To prove
  `(byte.toUInt32 >>> off.toUInt32) &&& 1 = if byte.toNat.testBit off then 1 else 0`,
  use `UInt32.toNat_inj.mp` to reduce to Nat, then
  `UInt32.toNat_and`/`UInt32.toNat_shiftRight`/`UInt8.toNat_toUInt32`,
  then `Nat.testBit` unfolds to `1 &&& m >>> n != 0` — use `Nat.and_comm`
  + `Nat.one_and_eq_mod_two` + `split <;> omega`.
- **UInt32 shift mod 32**: `UInt32.shiftLeft` reduces the shift amount
  mod 32 — for `bit <<< shift.toUInt32` with `shift ≥ 32`, the bit is
  placed at position `shift % 32`, not `shift`. Any theorem about
  `readBits` (which accumulates via `bit <<< shift`) needs `n ≤ 32`.
- **`protected` not `private` for cross-file access**: When a definition
  or lemma in one file is needed by another, use `protected` visibility.
  `private` makes it inaccessible from other files. This applies to both
  lemmas (e.g. `byteToBits_length` used in BitstreamCorrect and
  InflateCorrect) AND definitions referenced in proof hypotheses (e.g.
  native table constants like `lengthBase`, `distExtra` in Inflate.lean
  that appear in `decodeHuffman.go` — if they're `private`, proofs in
  InflateCorrect.lean can't name them in `cases` or `simp` arguments).
  **Caveat**: `protected` requires fully-qualified names even within the
  same namespace (`Inflate.lengthBase` instead of `lengthBase`). For
  definitions used unqualified within their own namespace AND needed
  cross-file, use public (no modifier) instead.
- **Avoid `▸` with UInt32/BitVec goals**: The `▸` (subst rewrite) tactic
  triggers full `whnf` reduction, which can deterministic-timeout on goals
  involving UInt32 or BitVec operations. Use `obtain ⟨rfl, _⟩ := h` +
  `rw [...]` + `exact ...` instead. The `rw` tactic is much more targeted
  and avoids the expensive reduction.
- **Avoid `for`/`while` in spec functions**: In `Option`/`Except` monads,
  `return` inside a `for` loop exits the loop (producing `some`), not the
  function. Use explicit recursive helper functions instead — they're also
  easier to reason about in proofs. Reserve `for`/`while` for `IO` code.
- **Unfolding do-notation with `Except.bind`**: When a hypothesis `h`
  contains a `do` block (`let x ← f; g x`), use `cases hrd : f` to
  split on the result BEFORE simplifying `h`. Then
  `simp only [..., hrd, bind, Except.bind] at h` substitutes the
  known result. This is cleaner than `simp [...] at h; split at h;
  rename_i ...` which produces fragile unnamed hypotheses.
- **do-notation guards (`if ... then throw`)**: Guards like
  `if cond then throw err` in `Except` do-notation expand to
  `match (if cond then Except.error err else pure PUnit.unit) with
  | Except.error e => ... | Except.ok _ => ...`. After splitting the
  outer condition with `split at h`, the `pure` branch leaves a stuck
  `match`. Use `simp only [pure, Except.pure] at h` to reduce it, then
  continue with the next `cases`/`split`.
- **Closing `Except.error = Except.ok` contradictions**: `simp only`
  does NOT know that `Except.error ≠ Except.ok` — it lacks the
  discriminator lemmas. Use `simp at h` (without `only`) which includes
  them, or explicitly `exact absurd h (by simp)`. Don't try `nofun h`
  or `exact Except.noConfusion h` — neither works directly.
- **Nested `cases` parsing**: Nested `cases ... with | ... | ...`
  blocks cause Lean to misparse the inner `| some =>` as belonging to
  the outer `cases`. Use `match` for the inner case split instead:
  ```lean
  cases hdb : f x with
  | none =>
    match hdec : g y with   -- NOT `cases hdec : g y with`
    | none => ...
    | some p => ...
  | some p => ...
  ```
- **Block-level correspondence proof pattern**: For theorems like
  `decodeStored_correct` that connect native imperative decoders (using
  `Except` monad with `do`-notation) to spec decoders (using `Option`
  monad with `bind`):
  1. `simp only [NativeFunc, bind, Except.bind] at h` to unfold the native
  2. `cases hx : operation` + `simp [hx] at h` for each `Except` operation
  3. Build spec-level hypotheses by chaining correspondence lemmas
  4. Close with `simp only [SpecFunc, bind, Option.bind, hyp₁, hyp₂, ...]`
     + `rfl` to evaluate the spec function
  Key: prepare all intermediate spec hypotheses in unified form
  (substituting `← hrest` to align bit positions) before the final `simp`.
- **UInt16 comparison and conversion**: In v4.29.0-rc1, UInt16 is
  BitVec-based. `sym < 256` (UInt16 lt) directly proves
  `sym.toNat < 256` via `exact hsym`. Negation `¬(sym < 256)` gives
  `sym.toNat ≥ 256` via `Nat.le_of_not_lt hge`. For equality,
  `sym.toNat = 256` proves `sym = 256` via
  `UInt16.toNat_inj.mp (by simp; exact heq)`. `sym.toUInt8` equals
  `sym.toNat.toUInt8` by `rfl` (UInt16.toUInt8 is defined as
  `fun a => a.toNat.toUInt8`). `omega` CANNOT directly bridge
  UInt16 comparisons to Nat — extract hypotheses first.
- **Option `pure` vs `some`**: After `simp only` with `↓reduceIte` on
  spec functions, goals may have `pure (...) = some (...)`. Add `pure`
  to the simp arguments to unfold it.
- **Namespace scoping for new definitions**: `def Foo.Bar.baz` inside
  `namespace Quux` creates `Quux.Foo.Bar.baz`, NOT `Foo.Bar.baz`.
  To define in a different namespace, either close the current namespace
  first, or use a local name (e.g. `def decodeBits` instead of
  `def Zip.Native.HuffTree.decodeBits`).
- **`getElem?_pos`/`getElem!_pos` for Array lookups**: To prove
  `arr[i]? = some arr[i]!`, use the two-step pattern:
  `rw [getElem!_pos arr i h]; exact getElem?_pos arr i h`. The first
  rewrites `arr[i]!` to `arr[i]` (bounds-checked), the second proves
  `arr[i]? = some arr[i]`. `getElem?_pos` needs the explicit container
  argument (not `_`) to avoid `GetElem?` type class synthesis failures.
- **Fin coercion mismatch in omega**: When a lemma over `Fin n`
  is applied as `lemma ⟨k, hk⟩`, omega treats
  `arr[(⟨k, hk⟩ : Fin n).val]!` and `arr[k]!` as different variables.
  Fix by annotating the result type:
  `have : arr[k]! ≥ 1 := lemma ⟨k, hk⟩`.
- **Nat beq false**: To prove `(n == m) = false` for Nat with `n ≠ m`,
  use `cases heq : n == m <;> simp_all [beq_iff_eq]`. Direct `omega`
  and `rw [beq_iff_eq]` don't work because `omega` doesn't understand
  `BEq` and `beq_iff_eq` is about `= true`, not `= false`.
- **List/Array/ByteArray length conversions**: `Array.length_toList`
  gives `arr.toList.length = arr.size`. `ByteArray.size_data` gives
  `ba.data.size = ba.size`. Chain them for `ba.data.toList.length`.
- **Avoid `forIn` on `Range` in proofs**: `forIn [:n]` uses
  `Std.Legacy.Range.forIn'` with a well-founded recursion `loop✝` that
  CANNOT be unfolded by name. `with_unfolding_all rfl` only works for
  concrete values (`:= [:0]`, `[:1]`) not symbolic `n`. If you need to
  prove properties of a `for i in [:n]` loop, replace it with explicit
  recursion (see `copyLoop` in `Inflate.lean`).
- **Loop invariant proof pattern**: For recursive functions like
  `copyLoop buf start distance k length`, prove a generalized invariant
  by well-founded induction carrying the full buffer state:
  1. State the invariant relating `buf` to the original `output`
  2. Base case: `k = length`, `copyLoop` returns `buf`, use hypothesis
  3. Inductive step: show `buf.push x` satisfies the invariant for `k+1`
  4. Key lemmas: `push_getElem_lt` (push preserves earlier elements),
     `push_data_toList` (`(buf.push b).data.toList = buf.data.toList ++ [b]`),
     `List.ofFn_succ_last` (snoc decomposition of `List.ofFn`)
- **`congr` max recursion on nested Prod in Option**: `congr 1; congr 1`
  on `some (a, b, c) = some (x, y, z)` hits max recursion depth. Use
  `congrArg some (Prod.ext ?_ (Prod.ext ?_ rfl))` instead — gives clean
  sub-goals without recursion issues. Note: `congrArg` not `congr_arg`.
- **take/drop ↔ Array.extract**: To bridge `List.take`/`List.drop` (from
  spec) with `Array.extract` (from native), use:
  `simp only [Array.toList_extract, List.extract, Nat.sub_zero, List.drop_zero]`
  then `← List.map_drop` + `List.drop_take` for drop-inside-map-take.
- **`readBitsLSB_bound` for omega**: `readBitsLSB n bits = some (val, rest)`
  implies `val < 2^n`. Essential for bounding UInt values (e.g.,
  `hlit_v.toNat < 32`) before omega can prove `≤ UInt16.size`.
- **`Pure.pure` not `Option.pure`**: The constant `Option.pure` doesn't
  exist. Use `pure, Pure.pure` in simp arguments to unfold monadic
  `return` in Option specs.
- **`List.getElem_of_eq` for extracting from list equality**: When
  `hih : l1 = l2` and you need `l1[i] = l2[i]`, use
  `List.getElem_of_eq hih hbound` where `hbound : i < l1.length`.
  This avoids dependent-type rewriting issues that arise when trying
  `rw [hih]` directly on getElem expressions.
- **`Nat.mod_eq_sub_mod` for inductive mod proofs**: When proving
  `(n - k) % k = 0` from `n % k = 0` and `n ≥ k`, use
  `← Nat.mod_eq_sub_mod hge` to rewrite `(n - k) % k` to `n % k`.
  `omega` cannot reason about `%` directly.
- **`set` is Mathlib-only**: The `set` tactic is not available in this
  project. Use `have` or `let` instead.

## Current State

See `PROGRESS.md` for global milestones and current phase.
