# lean-zip

Lean 4 compression library: zlib/zstd via C FFI, plus pure-Lean tar and ZIP archives.
Toolchain: see `lean-toolchain`. Build system: Lake.

## Build and Test

    lake build          # build library + test executable
    lake exe test       # run all tests

Run from the project root. Tests require `testdata/` directory.

**Quality metric**: sorry count — `grep -rc sorry Zip/ || true`

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
    .claude/skills/      — Project-local skill files (proof patterns)

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
