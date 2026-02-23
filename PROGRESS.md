# lean-zip Progress

Global milestones — updated only on phase transitions and major events.
Per-session details are in `progress/`.

## Current State

- **Phase**: Phase 3 complete (zero sorries), Phase 4 not yet started
- **Toolchain**: leanprover/lean4:v4.29.0-rc1

## Milestones

### Phase 1: Checksums (complete)
Native CRC32 and Adler32 with equivalence proofs against FFI implementations.

### Phase 2: DEFLATE Decompressor (complete)
Pure Lean DEFLATE inflate implementation (RFC 1951). Conformance tests
pass against FFI zlib.

### Phase 3: Verified Decompressor (complete)
Correctness proofs for the DEFLATE decompressor. Canonical Huffman
correspondence, bitstream reader correctness, block-level decode
correctness, and stream-level inflate theorem. Zero sorries.

### Phase 4: DEFLATE Compressor (not started)
Next phase: native compression + full roundtrip theorem.

### Infrastructure
- Multi-agent coordination via `./go` with worktree-per-session isolation
- GitHub-based coordination (agent-plan issues, auto-merge PRs)
