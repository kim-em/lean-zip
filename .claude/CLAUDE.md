# lean-zip

Formally verified DEFLATE (zlib/gzip containers, CRC-32/Adler-32) in pure
Lean 4. Build system: Lake; toolchain per `lean-toolchain`.

## Build and Test

    lake build                  # library + tests (kernel re-checks every proof)
    lake test                   # native test suite
    lake -d conformance build   # native↔zlib conformance suite (needs system zlib)
    lake -d conformance test

Run from the project root. The main library needs no system C libraries;
only `conformance/` needs zlib + pkg-config (NixOS: `nix-shell`).
Lake caches `run_io` config (link flags) in `.lake/`; after environment
changes use `lake -R build` or `rm -rf .lake conformance/.lake`.

**Quality metric**: sorry count — `grep -rc sorry Zip/ || true` (must be 0 on master).

## Layout

- `Zip/Native/` — the pure-Lean implementation
- `Zip/Spec/` — formal specifications and correctness proofs
- `ZipTest/` — native unit tests (register new modules in `ZipTest.lean`)
- `conformance/` — dev-only sub-package: native vs zlib (via lean-zlib),
  RFC interop, fuzz harness
- `c/` — four stopgap `@[extern]` primitives, each with a Lean reference
  body and a correspondence proof
- Shared utilities (Binary, Handle, BitReader) come from
  [lean-zip-common](https://github.com/kim-em/lean-zip-common)

## Quality Standards

### Iterate in place on verified code
A verified implementation is the start, not the finish: make it faster or
tighter while the proof obligation holds at every commit, proving the
optimized version equal to the simple one. Proof churn from this is expected
and welcome. Do not route a performance change around the proofs, and do not
treat "it perturbs delicate proofs" as a reason not to try. The proofs are a
ratchet that makes aggressive iteration safe.

### Specifications
Three quality levels — know which you're writing and be honest about it:
1. **Tautological** (`f x = fImpl x`): avoid.
2. **Characterizing properties** (algebraic identities, structural
   invariants, invertibility theorems): the gold standard.
3. **Algorithmic correspondence** (two implementations agree): fine when the
   algorithm IS the spec (RFC pseudocode), but it's translation validation,
   not characterization.

For optimized variants, the spec is equivalence with the simple version.
Do NOT weaken a theorem statement just to make a proof easier.

### Proofs
- Do NOT remove a working theorem; refactoring its proof is encouraged
- Do NOT write multi-line tactic blocks without checking intermediate state
- Do NOT try the same approach more than 3 times — each retry must be
  fundamentally different
- `native_decide` is forbidden; prefer `decide_cbv` for kernel-level
  evaluation
- Prefer `omega`, `decide`, `simp`, `grind` over manual arithmetic
- Loop constructs from `while` / `for ... in [:n]` produce opaque `loop✝`
  functions that cannot be unfolded in proofs — use well-founded recursion
  with `termination_by` when you need to prove through a loop

### Tests
- Every new feature needs tests in `ZipTest/` (native-only) or
  `conformance/Conformance/` (needs zlib comparison)
- Include edge cases: empty input, single byte, large input

### Commits
- Conventional prefixes: `feat:`, `fix:`, `refactor:`, `test:`, `doc:`,
  `chore:`, `perf:`
- Each commit must compile and pass tests; no `sorry` on master
- One logical change per commit
