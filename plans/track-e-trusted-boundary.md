# Track E: Trusted Boundary, Parser Hardening, and Adversarial Assurance

## Purpose

Track E exists to close the gap between:

- theorems about the codec core, and
- the actual attack surface exposed by parsers, `IO`, FFI, allocation,
  and the Lean runtime.

This track is not optional polish. It is part of "done" for every
boundary-facing subsystem.

## Scope

Track E covers any code path that:

- consumes attacker-controlled bytes, sizes, offsets, counts, or paths
- performs `Handle.read`, `Stream.read`, `readBinFile`, `seek`, or allocation
- crosses the Lean/C boundary
- depends on runtime behavior outside the proved core
- can fail via panic, out-of-memory, unchecked overflow, or excessive
  resource consumption

## Deliverables

### 1. Trusted Boundary Inventory

Maintain a living inventory of:

- Lean runtime functions relied on by `ByteArray`, `IO.FS.Handle`, streams,
  and allocation
- C FFI shims in `c/`
- external libraries such as zlib
- parser and archive modules that are tested but not fully verified

For each component, track:

- trust status
- current guardrails
- known bugs or upstream references
- missing work

Primary artifact: `SECURITY_INVENTORY.md`.

### 2. Boundary Contract Ledger

For every public entry point that accepts untrusted input, document:

- attacker-controlled fields
- validation performed before read/seek/allocation
- explicit size/resource limits
- failure behavior on malformed input

This can live inline in the inventory at first, then split out if it grows.

### 3. Hardening Queue

Maintain a prioritized queue of parser and FFI hardening tasks:

- unchecked size/offset to allocation paths
- short-read/truncation handling
- zip-bomb / decompression-bomb limits
- malformed metadata combinations
- path traversal, link traversal, and archive extraction edge cases

Primary artifact: `plans/track-e-current-audit-checklist.md`.

### 4. Adversarial Validation

Every boundary-facing subsystem must eventually have:

- malformed fixture coverage
- differential tests where applicable
- sanitizer runs for native/FFI paths
- fuzz targets and saved regression corpus

Required tooling:

- ASan
- UBSan
- Valgrind or equivalent memory checker
- corpus minimization for crashing inputs

### 5. Upstream Bug Workflow

If Track E finds a bug in Lean runtime or another dependency, the same
wave of work must produce:

- a minimized reproducer
- an upstream issue or PR
- a local guardrail or workaround if feasible
- a permanent regression note in `SECURITY_INVENTORY.md`

## Exit Criteria

No boundary-facing subsystem is complete until all of the following hold:

- happy-path tests pass
- malformed-input tests pass
- relevant size and offset guards exist
- resource limits are explicit
- the subsystem has an entry in `SECURITY_INVENTORY.md`
- the remaining trusted or unverified portion is named explicitly

For high-risk surfaces, add:

- sanitizer-clean runs
- meaningful fuzzing coverage
- minimized regression fixtures for previously discovered bugs

## Current Priority Order

### Priority 0: Allocation-from-header paths

Anything that converts attacker-controlled metadata into `Nat`, `USize`,
or allocation requests must be audited first.

Current hotspots:

- `Zip/Archive.lean` `readExact`, `listFromHandle`, `readEntryData`
- `Zip/Tar.lean` `readExact`, `readEntryData`, `extractTarGzNative`
- `c/zlib_ffi.c` whole-buffer and streaming inflate helpers

### Priority 1: Archive parser bounds proofs and guards

The ZIP and tar parsers need clear pre-read validation:

- claimed sizes and offsets must be checked against actual file bounds
- compressed sizes must not be passed unchecked into `Handle.read`
- archive extraction must enforce entry and total-output limits

### Priority 2: Adversarial harnesses

Add or extend:

- ZIP central-directory fuzzing
- ZIP local-header / size-mismatch fuzzing
- tar header and PAX fuzzing
- gzip/zlib/deflate malformed corpus coverage
- FFI whole-buffer decompression harnesses

### Priority 3: Trusted boundary shrinkage

Where feasible:

- move guards into Lean before runtime/FFI calls
- prove helper lemmas for bounded reads and seeks
- reduce unchecked calls into runtime allocation APIs

## Orchestrator Scheduling Rules

If an agent orchestrator is running the repo, it must:

1. Always keep at least one Track E task active once A2/A3 exists.
2. Open a Track E task automatically for every new parser, stream API,
   extraction path, or FFI entry point.
3. Treat sanitizer/fuzzer findings as mainline work, not side work.
4. Require a regression artifact before closing a Track E bug.
5. Prefer shrinking trust boundaries over merely documenting them.
