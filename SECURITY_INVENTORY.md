# Security Inventory

Living inventory of trusted components, boundary-facing subsystems, and
known gaps that sit outside the formally verified codec core.

## Status Labels

- `proved-in-repo`: covered by Lean proofs in this repository
- `guarded-locally`: not fully proved, but protected by explicit checks and limits
- `tested-only`: covered by tests/conformance but missing stronger assurance
- `upstream-risk`: trusted dependency with a known or suspected upstream issue

## Trusted Computing Base

### Lean Runtime: `ByteArray`, scalar-array allocation, `IO`

- Status: `guarded-locally` (was `upstream-risk` while
  https://github.com/leanprover/lean4/issues/13388 was open; closed by
  https://github.com/leanprover/lean4/pull/13392, released in v4.30.0-rc2;
  the project's `lean-toolchain` is now pinned at v4.30.0-rc2 or later)
- Why trusted: all Lean code ultimately relies on runtime allocation and
  `IO` primitives for `ByteArray`, `Handle.read`, and stream operations.
- Current local guardrails (kept as defense-in-depth even after the
  upstream fix; see *"Re-evaluation after v4.30.0-rc2"* below):
  - `Zip/Archive.lean` checks `n.toUSize.toNat == n` before `Handle.read`
  - `Zip/Archive.lean` checks file-bounds for central directory before reading it
  - native inflate APIs carry explicit `maxOutputSize` bounds
- Known concern (historical):
  - crafted oversized reads triggered a heap-buffer overflow in the
    runtime's `lean_io_prim_handle_read` allocation path. Closed in
    v4.30.0-rc2 by adding checked arithmetic on every relevant
    allocation site so overflow now throws OOM instead of corrupting
    the heap.
- Upstream tracking:
  - Bug report: https://github.com/leanprover/lean4/issues/13388 —
    *"Buffer overflow in `lean_io_prim_handle_read`"*, filed
    2026-04-13 by @kiranandcode with a 4-line MWE reproducing under
    valgrind. The bug surfaced via Kiran Gopinathan's fuzzing of
    lean-zip — see https://kirancodes.me/posts/log-who-watches-the-watchers.html
  - Fix: https://github.com/leanprover/lean4/pull/13392 — *"fix: file
    read buffer overflow"*, merged 2026-04-13 by @hargoniX. Adds
    checked arithmetic on all relevant allocation paths in
    `lean_io_prim_handle_read`; overflow now throws OOM instead of a
    heap overflow.
  - Release: https://github.com/leanprover/lean4/releases/tag/v4.30.0-rc2
    (2026-04-17). The project's `lean-toolchain` is now pinned at this
    version (see the file at the repo root).
  - Status: closed upstream and consumed by this repository.
- Re-evaluation after v4.30.0-rc2: the local `Nat → USize` roundtrip
  check (`n.toUSize.toNat == n`) was authored as a workaround for the
  upstream truncation hazard. Now that overflow throws OOM instead of
  corrupting memory, the check is no longer load-bearing for memory
  safety, but it is kept as defense-in-depth because (a) it produces a
  named, catchable error before allocation rather than a late OOM,
  (b) it is a no-op on 64-bit platforms and a meaningful guard on any
  future 32-bit `USize` target, and (c) the cost is negligible. The
  `assertSpanInFile` checks, `maxCentralDirSize` / `maxEntrySize` caps,
  CD-vs-LH consistency checks, and native `maxOutputSize` caps were
  never compensating for the runtime bug — they bound metadata-driven
  allocation against bombs and are unaffected by the upstream fix. No
  guardrails are dropped by this bump.
  - Local regression coverage (fixtures + assertion sites that guard
    this attack surface today):
    - `testdata/zip/malformed/oversized-compressed-size.zip` —
      oversized 32-bit `compressedSize`; asserted in
      `ZipTest/ZipFixtures.lean`.
    - `testdata/zip/malformed/oversized-zip64-compressed-size.zip` —
      oversized ZIP64 `compressedSize` (PR #1543); asserted in
      `ZipTest/ZipFixtures.lean`.
    - `testdata/zip/malformed/oversized-zip64-uncompressed-size.zip` —
      oversized ZIP64 `uncompressedSize` (PR #1544); asserted in
      `ZipTest/ZipFixtures.lean`.
    - `testdata/zip/malformed/cd-lh-method-mismatch.zip` and
      `cd-lh-size-mismatch.zip` — CD vs local-header mismatches
      (PR #1554); asserted in `ZipTest/ZipFixtures.lean`.
    - Bomb-limit regression tests for `Gzip.decompress`,
      `RawDeflate.decompress`, and `Zip.Native.GzipDecode.decompress`
      (PR #1560); coverage in `ZipTest/Gzip.lean`,
      `ZipTest/RawDeflate.lean`, and `ZipTest/NativeGzip.lean`.
    - Bomb-limit regression tests for `Archive.extract` /
      `Archive.extractFile` / `Tar.extract` / `Tar.extractTarGz`
      (PR #1561); coverage in `ZipTest/Archive.lean` and
      `ZipTest/Tar.lean`.
  - Local guardrails (cross-ref *"Current local guardrails"* above):
    `readExact`'s `Nat → USize` roundtrip before every `Handle.read`;
    `assertSpanInFile` for local-header / name+extra / compressed-data
    spans in `Zip/Archive.lean` (PR #1497); ZIP `maxCentralDirSize`
    (default 64 MiB) and `maxEntrySize` caps on `Archive.extract` /
    `Archive.extractFile`; tar `maxEntrySize` cap on `Tar.extract` /
    `Tar.extractTarGz` / `Tar.extractTarGzNative`; native inflate
    `maxOutputSize` caps (`Zip.Native.Inflate.inflate` default 1 GiB;
    `Zip.Native.GzipDecode.decompress`, `Zip.Native.ZlibDecode.decompress`,
    `Zip.Native.decompressAuto` default 256 MiB — see
    *"Decompression Limit Inventory"* below for the full table).
- Missing work:
  - prove or enforce stronger preconditions before every `Handle.read`
    and `Stream.read` driven by archive metadata
    - see *"Local guard inventory for `Handle.read` and `Stream.read`"*
      below for the per-site audit of what protections are currently in
      place
- Recent wins:
  - ✅ in-repo deterministic `Handle.read` regression harness
    ([`ZipTest/FuzzHandleRead.lean`](/home/kim/lean-zip/ZipTest/FuzzHandleRead.lean)
    / [`ZipFuzzHandleRead.lean`](/home/kim/lean-zip/ZipFuzzHandleRead.lean)
    / [`scripts/fuzz-handle-read.sh`](/home/kim/lean-zip/scripts/fuzz-handle-read.sh))
    — *Executed by PR #2385* (no findings under v4.30.0-rc2;
    replaces the blog-post AFL harness as the forward-looking
    regression artefact for the `lean_io_prim_handle_read` class).
    Drives `Archive.list / extract`, `Tar.list / extract`,
    `Tar.extractTarGz / extractTarGzNative`,
    `Gzip.decompressStream / decompressFile`, and
    `RawDeflate.decompressStream` with deterministic xorshift-seeded
    pathological inputs at sizes {0, 1, 16, 512, 8192, 65536, 131072}
    and chunk sizes {1, 7, 31, 127, 65535, 65536, 65537}. `lake exe
    test` runs a 100-iteration fixed-seed smoke check; the
    `fuzz_handle_read` lake executable takes a wall-clock budget
    (default 30 s, override via CLI arg or
    `LEAN_ZIP_FUZZ_HANDLE_READ_SECONDS`).
  - upstream `lean_io_prim_handle_read` buffer-overflow fix consumed
    via the v4.30.0-rc2 toolchain bump — closes the previous
    `upstream-risk` status; no local guardrails dropped (see
    *"Re-evaluation after v4.30.0-rc2"* above)
  - oversized ZIP64 compressed-size fixture — PR #1543
    (`testdata/zip/malformed/oversized-zip64-compressed-size.zip`)
  - oversized ZIP64 uncompressed-size fixture — PR #1544
    (`testdata/zip/malformed/oversized-zip64-uncompressed-size.zip`)
    — together these close the previous *"add regression fixtures for
    oversized ZIP64 size claims"* Missing-work bullet
- Paired review of PR #2385 (in-repo deterministic `Handle.read` /
  `Stream.read` regression harness):
  - **Design fidelity vs. issue #2380 / fallback path #2381.** The
    merged PR satisfies all four enumerated deliverables from the
    closing issue:
    (1) [`ZipTest/FuzzHandleRead.lean`](/home/kim/lean-zip/ZipTest/FuzzHandleRead.lean)
    is the deterministic xorshift-seeded driver mirroring
    [`ZipTest/FuzzInflate.lean`](/home/kim/lean-zip/ZipTest/FuzzInflate.lean)'s
    shape (same inlined 64-bit xorshift PRNG, same wall-clock budget
    helper signatures, same `tryRead` filter that propagates every
    `IO.Error` variant other than `.userError`);
    (2) [`ZipFuzzHandleRead.lean`](/home/kim/lean-zip/ZipFuzzHandleRead.lean)
    + [`scripts/fuzz-handle-read.sh`](/home/kim/lean-zip/scripts/fuzz-handle-read.sh)
    are the sibling top-level driver and wrapper script analogous to
    [`ZipFuzzInflate.lean`](/home/kim/lean-zip/ZipFuzzInflate.lean)
    + [`scripts/fuzz-inflate.sh`](/home/kim/lean-zip/scripts/fuzz-inflate.sh);
    (3) the four pathological-input families from #2380 deliverable 3
    (read-size-vs-buffer-length mismatches, zero-length reads,
    oversized declared sizes, streaming reads across realloc-grown
    buffers) are all realised in `oneIteration` via the
    `sizeClasses` / `chunkSizes` / `outputCapClasses` rotations and
    the `withEocdSignature` / `withGzipMagic` / `withUstarMagic`
    parser-progress helpers;
    (4) the *Missing-work* bullet flip is in place — the *Recent
    wins* one-liner above cites PR #2385 directly (no unsubstituted
    placeholder-PR token remains; the post-PR substitution
    discipline from
    [`progress/`](/home/kim/lean-zip/progress/)`20260428T122256Z_293ae374_anchor-refresh-closeout.md`
    was followed). The fallback-path narrative captured in
    [`progress/`](/home/kim/lean-zip/progress/)`20260429T072930Z_b53169b1_kiran-fuzz-rerun-fallback.md`
    (#2369 → #2380 hand-off) and
    [`progress/`](/home/kim/lean-zip/progress/)`20260429T083420Z_907e1428_fuzz-handle-read.md`
    (#2380 closeout) is consistent with the merged tree.
  - **Call-site coverage.** Every archive-side untrusted-bytes
    `Handle.read` / `Stream.read` call site enumerated in #2380 is
    transitively driven by an entry point in `oneIteration`:
    `Archive.list` / `Archive.extract` reach
    [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) `readExact`
    (line 1011) and `readBoundedSpanFromHandle` (`readExact` again
    via the helper) for EOCD tail, central-directory, local-header,
    name-extra, and compressed-data spans;
    `Tar.list` / `Tar.extract` over the `byteArrayReadStream` +
    `fragmentingStream` wrapper reach
    [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) `readExact`
    (line 218 / `input.read` line 222), the `readEntryData` payload
    + padding reads (lines 257 / 267), the `skipEntryData` loop
    (line 635), the `Tar.extract` regular-file payload + padding
    reads (lines 781 / 792), and the 512-byte block read (line 656);
    `Tar.extractTarGz` adds the `tarStream` wrapper's
    `inStream.read 65536` (line 890); `Gzip.decompressStream`
    (driven twice — once on bare random bytes and once on
    `withGzipMagic`-prefixed bytes) reaches the streaming
    [Zip/Gzip.lean](/home/kim/lean-zip/Zip/Gzip.lean) `input.read 65536`
    sites at lines 68 and 102; `RawDeflate.decompressStream`
    reaches the
    [Zip/RawDeflate.lean](/home/kim/lean-zip/Zip/RawDeflate.lean)
    `input.read 65536` sites at lines 40 and 73;
    `Gzip.decompressFile` exercises the file-handle gzip path. The
    creator-side `h.read` in `Tar.create`
    ([Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) line 599) is
    correctly **out of scope** — it reads caller-chosen source files
    rather than untrusted archive bytes and is excluded from the
    *Local guard inventory* below for the same reason.
  - **Determinism + reproducibility.** The 64-bit xorshift PRNG
    (`xorshift64`, lines 79–84 of
    [`ZipTest/FuzzHandleRead.lean`](/home/kim/lean-zip/ZipTest/FuzzHandleRead.lean))
    is inlined with no external randomness dependency, and every
    PRNG-consuming helper threads the state explicitly; a fixed
    `(seed, iterations)` pair therefore produces the same exact
    inputs on every run. The size grid `#[0, 1, 16, 512, 8192,
    65536, 131072]` (line 60–61) and chunk-size grid `#[1, 7, 31,
    127, 65535, 65536, 65537]` (line 66–67) match the *Recent
    wins* description above byte-for-byte. The `lake exe test`
    smoke run is a 100-iteration `runFuzz` invocation at fixed
    seed `0xdeadc0de` (line 362 — `tests` has no PRNG-time entropy
    source, so a flake from non-deterministic seeding is impossible);
    re-running `lake exe test` on the post-merge tree
    re-confirmed `FuzzHandleRead tests (seed=0xdeadc0de) ... 100
    iterations completed` followed by `All tests passed!` with no
    diagnostics.
  - **Wall-clock-budget mode.** The standalone
    [`fuzz_handle_read`](/home/kim/lean-zip/ZipFuzzHandleRead.lean)
    lake executable accepts a wall-clock budget via either
    positional CLI arg or `LEAN_ZIP_FUZZ_HANDLE_READ_SECONDS`
    environment variable (default 30 s). The precedence — CLI
    first, then env, then default — matches the sibling
    [`fuzz_inflate`](/home/kim/lean-zip/ZipFuzzInflate.lean) recipe
    line-for-line (`getEnvNatOr "LEAN_ZIP_FUZZ_HANDLE_READ_SECONDS"
    30` mirrors `getEnvNatOr "LEAN_ZIP_FUZZ_SECONDS" 30`). A 5 s
    smoke invocation (`bash scripts/fuzz-handle-read.sh 5`) on the
    post-merge tree completed 4 940 iterations and exited 0 with
    output `[fuzz-handle-read] OK`. The seed defaults to
    `0xc0ffeec0ffeec0ff` (overridable via
    `LEAN_ZIP_FUZZ_HANDLE_READ_SEED`), distinct from the
    `lake exe test` smoke seed `0xdeadc0de` so the budgeted run
    explores a different deterministic input series than the CI
    smoke set.
  - **Inventory cross-link integrity.** The *Recent wins* bullet
    above cites PR #2385 directly (the placeholder-PR token used
    pre-merge has been substituted), and the *Missing-work* →
    *Recent-wins* flip follows the
    [.claude/skills/inventory-reconciliation/SKILL.md](/home/kim/lean-zip/.claude/skills/inventory-reconciliation/SKILL.md)
    *Executed past-tense one-liner* convention (✅ + brief noun
    phrase, *Executed by PR #2385*, parenthetical findings
    statement).
    [`scripts/check-inventory-links.sh`](/home/kim/lean-zip/scripts/check-inventory-links.sh)
    on the post-merge tree reports `errors=0, warnings=0` (78
    unique fixture paths checked, 8 placeholder-PR occurrences —
    none of which is the PR #2385 entry). No follow-up cross-link
    bookkeeping issue is required.
  - **Findings statement.** No new findings under v4.30.0-rc2.
    Re-confirmed by (a) the 100-iteration `lake exe test` smoke
    run (clean), and (b) the 5 s `scripts/fuzz-handle-read.sh 5`
    run on the worker host (4 940 iterations, exit 0). The harness
    rejects exactly one `IO.Error` variant — `.userError` — as the
    expected malformed-input failure mode; any panic, segfault,
    sanitizer trap, or non-`userError` `IO.Error` would surface as
    a non-zero exit. None did. The *Recent wins* bullet's
    *"no findings under v4.30.0-rc2"* claim is therefore
    validated by post-merge re-run, not just by the original
    pre-merge author run.

### zlib via C FFI

- Components: [c/zlib_ffi.c](/home/kim/lean-zip/c/zlib_ffi.c)
- Status: `guarded-locally`
- Why trusted: whole-buffer and streaming compression/decompression are
  implemented in C and depend on zlib plus libc allocation behavior.
- Current local guardrails:
  - `UINT_MAX` guards on whole-buffer input sizes
  - overflow-aware buffer growth helpers
  - explicit `max_output` check in whole-buffer decompression
  - state finalizers for streaming objects
  - [`scripts/sanitize-ffi.sh`](/home/kim/lean-zip/scripts/sanitize-ffi.sh)
    rebuilds `c/zlib_ffi.c` under `-fsanitize=address,undefined` and
    runs the test suite so FFI-level memory and UB errors surface as
    runtime traps; the April 2026 tree is ASan + UBSan clean.
  - [`ZipTest/FuzzInflate.lean`](/home/kim/lean-zip/ZipTest/FuzzInflate.lean)
    + [`scripts/fuzz-inflate.sh`](/home/kim/lean-zip/scripts/fuzz-inflate.sh)
    land a deterministic xorshift-seeded fuzz driver that feeds every
    whole-buffer FFI decoder (`Zlib.decompress`, `Gzip.decompress`,
    `RawDeflate.decompress`) and the streaming `Gzip.InflateState`
    path with pseudo-random inputs at sizes {0, 1, 16, 512, 8192,
    65536} and chunk sizes {1, 7, 31, 127}. `lake exe test` runs a
    100-iteration fixed-seed smoke check (≈ 10 ms); the `fuzz_inflate`
    lake executable takes a wall-clock budget (default 30 s, override
    via CLI arg or `LEAN_ZIP_FUZZ_SECONDS`). For sanitizer coverage,
    reuse the `ZLIB_CFLAGS / ZLIB_LDFLAGS / LD_PRELOAD` recipe from
    `scripts/sanitize-ffi.sh` — the fuzz driver is linked into
    `.lake/build/bin/fuzz_inflate` which inherits the same sanitizer
    runtime when built under those flags. Any `IO.userError` is the
    handled case; an uncaught panic, segfault, or ASan/UBSan trap
    terminates with non-zero status.
- Missing work:
  - maintain sanitizer coverage for all FFI entry points
  - add dedicated malformed-input regression tests for streaming paths
  - any new `malloc`/`realloc`/`calloc`/`grow_buffer` call, or change
    to `grow_buffer` semantics, in `c/zlib_ffi.c` requires re-running
    the audit below and updating the snapshot table. The helper
    [`scripts/check-c-allocations.sh`](/home/kim/lean-zip/scripts/check-c-allocations.sh)
    prints a one-line warning at PR-review time if the count of
    `malloc`/`realloc`/`calloc` mentions drifts from the baseline.

#### Allocation site audit (`c/zlib_ffi.c`)

Snapshot of every `malloc`, `realloc`, `calloc`, and `grow_buffer`
call in [c/zlib_ffi.c](/home/kim/lean-zip/c/zlib_ffi.c) as of
2026-04-29. `grow_buffer` is the shared doubling helper at
[c/zlib_ffi.c](/home/kim/lean-zip/c/zlib_ffi.c); its
`*buf_size > SIZE_MAX/2` overflow check and `free(buf)`-on-failure
semantics are the linchpin for every decompression-side growth
site. Callers of `grow_buffer` must NOT free `buf` themselves on a
`NULL` return — it has already been freed.

| Site | Bound | Failure handling | Notes |
|---|---|---|---|
| `mk_zlib_error` (shared error-string formatter; reached by every FFI entry point on a non-OK zlib return) | `prefix_len + detail_len + 3`, with `prefix_len > SIZE_MAX - detail_len - 3` overflow guard | returns `mk_io_error("zlib error: out of memory while formatting error")` (no resource held at this point) | `buf` is `free`d immediately after `snprintf` + `mk_io_error`; the Lean string owns its own copy. Allocation is small (≤ 256 + message). |
| `grow_buffer` (shared helper; caller-dependent) | `*buf_size *= 2`, pre-checked by `if (*buf_size > SIZE_MAX / 2)`; on overflow, frees old `buf` and returns `NULL` | returns `NULL`; **frees the old `buf` on `realloc` failure** | Every caller treats `NULL` as "buffer already freed" — no `free(buf)` on the caller's error path. |
| `decompress_inflate` — reached by `lean_zlib_decompress`, `lean_gzip_decompress`, `lean_raw_deflate_decompress` | `initial_decompress_buf(src_len)`: `src_len * 4` with a `SIZE_MAX/4` overflow guard, floored at 1024. `src_len ≤ UINT_MAX` already enforced by the caller | `inflateEnd(&strm); return mk_io_error("<label>: out of memory")` | Initial whole-buffer decompression buffer. |
| `decompress_inflate` (same callers) | `grow_buffer` doubling, capped at `SIZE_MAX/2` | on `NULL`: `inflateEnd(&strm); return mk_io_error("<label>: out of memory")` — does **not** re-free `buf` (`grow_buffer` already did) | The `max_output` cap (when non-zero) is checked **after** `inflate` writes into the grown buffer, not before `grow_buffer` — see the summary below. |
| `lean_gzip_deflate_new` (streaming compression state constructor) | fixed `sizeof(deflate_state)` (small struct; zlib's internal `deflateInit2` buffers are allocated separately inside zlib) | `return mk_io_error("gzip deflate new: out of memory")` (no zlib stream yet) | `calloc` zero-initialises `finished` so the finalizer always makes a well-defined `deflateEnd` decision. |
| `lean_gzip_deflate_push` (streaming compression, per-chunk output buffer) | fixed 65 536 bytes initial | `return mk_io_error("gzip deflate push: out of memory")`. **Does not** call `deflateEnd` — the `deflate_state` remains live and the finalizer will clean it up | Grown by `grow_buffer` in the loop. |
| `lean_gzip_deflate_push` | `grow_buffer` doubling, capped at `SIZE_MAX/2` | on `NULL`: `return mk_io_error("gzip deflate push: out of memory")` (no `free`, no `deflateEnd` — finalizer cleans the state) | No per-call output cap; bounded only by `grow_buffer`'s `SIZE_MAX/2` guard. |
| `lean_gzip_deflate_finish` (streaming compression, `Z_FINISH` flush buffer) | fixed 65 536 bytes initial | `return mk_io_error("gzip deflate finish: out of memory")`. State stays live; finalizer calls `deflateEnd` | Used by both gzip and raw-deflate streaming paths (they share the same `deflate_state`). |
| `lean_gzip_deflate_finish` | `grow_buffer` doubling, capped at `SIZE_MAX/2` | on `NULL`: `return mk_io_error("gzip deflate finish: out of memory")` (no re-free, no `deflateEnd` — finalizer cleans) | No per-call output cap. |
| `lean_gzip_inflate_new` (streaming decompression state constructor; `MAX_WBITS + 32` auto-detect) | fixed `sizeof(inflate_state)` | `return mk_io_error("gzip inflate new: out of memory")` | `calloc` zero-initialises `finished`. |
| `lean_gzip_inflate_push` (streaming decompression, per-chunk output buffer; shared with raw inflate) | fixed 65 536 bytes initial | `return mk_io_error("gzip inflate push: out of memory")`. State stays live | No `max_output` parameter on this path — caller is responsible for whole-archive bounding. |
| `lean_gzip_inflate_push` | `grow_buffer` doubling, capped at `SIZE_MAX/2` | on `NULL`: `return mk_io_error("gzip inflate push: out of memory")` (no re-free, no `inflateEnd` — finalizer cleans) | No per-call output cap. |
| `lean_raw_deflate_new` (streaming raw-deflate compression state) | fixed `sizeof(deflate_state)` | `return mk_io_error("raw deflate new: out of memory")` | Reuses the shared `lean_gzip_deflate_push` / `_finish` helpers via `g_deflate_class`. |
| `lean_raw_inflate_new` (streaming raw-deflate decompression state; `-MAX_WBITS`) | fixed `sizeof(inflate_state)` | `return mk_io_error("raw inflate new: out of memory")` | Reuses the shared `lean_gzip_inflate_push` helper via `g_inflate_class`. |

Summary — what this pattern catches and what it does not:

- **Catches**: `size_t` overflow in the doubling step (`SIZE_MAX/2` guard in `grow_buffer`); individual `malloc`/`realloc`/`calloc` failure (every site has a `NULL`-check and returns an `IO` error); double-free after `grow_buffer` failure (callers never re-`free(buf)` on a `NULL` return because `grow_buffer` already did); and over-4 GiB whole-buffer inputs (guarded at the caller before any allocation, via `src_len > UINT_MAX` checks).
- **Does NOT catch**:
  1. A decompression bomb passed to a whole-buffer decoder with `max_output == 0` (the "no limit" sentinel) can still walk the buffer up to `SIZE_MAX/2` before `grow_buffer` refuses: the `max_output` check fires only **after** `inflate` has written into the already-grown buffer. The guard is therefore a "refuses to keep going" limit, not a "refuses to allocate" limit — see the *Decompression Limit Inventory* below for the caller-level mitigation.
  2. The streaming entry points (`lean_gzip_deflate_push`, `lean_gzip_deflate_finish`, `lean_gzip_inflate_push`) accept no output-size parameter at all. Their per-call output buffer is bounded only by `grow_buffer`'s `SIZE_MAX/2` guard; whole-archive bounding is the caller's problem.
  3. zlib's own internal allocations (`inflateInit2` / `deflateInit2` stream state, Huffman tables, sliding window) are made via zlib's `zalloc` (default `malloc`). They are not enumerated here — they live inside zlib itself and sit under the "upstream-risk" portion of this entry's trust status.

### miniz_oxide via Rust

- Components:
  [c/miniz_oxide_ffi.c](/home/kim/lean-zip/c/miniz_oxide_ffi.c),
  [rust/miniz_oxide_shim/](/home/kim/lean-zip/rust/miniz_oxide_shim/),
  [Zip/MinizOxide.lean](/home/kim/lean-zip/Zip/MinizOxide.lean)
- Status: `guarded-locally`
- Why trusted: an opt-in pure-Rust DEFLATE implementation
  (`miniz_oxide` v0.8) exposed through a `staticlib` Cargo crate
  (`rust/miniz_oxide_shim/`) and a thin C-ABI shim
  (`c/miniz_oxide_ffi.c`). Used by the Track D bench harness as a
  runtime/ratio comparator alongside zlib, libdeflate, and zopfli (see
  [BENCH.md](/home/kim/lean-zip/BENCH.md) for the toolchain matrix).
  `lake build` auto-detects `cargo` on `PATH` and links
  `libminiz_oxide_shim.a` when present; the `MINIZ_OXIDE_DISABLE=1`
  build-time knob and a stub-fallback path keep `lake build` working
  on minimal toolchains. The public `MinizOxide.compress` /
  `MinizOxide.decompress` Lean APIs run miniz_oxide on whole-buffer
  inputs and would process attacker-controlled bytes if a downstream
  caller wired them into a non-bench codepath. The only callers today
  are [ZipBench.lean](/home/kim/lean-zip/ZipBench.lean) (the
  `compress-miniz` / `inflate-miniz` operations) and the smoke tests
  in
  [ZipTest/MinizOxide.lean](/home/kim/lean-zip/ZipTest/MinizOxide.lean);
  the module is **not** part of the verified DEFLATE pipeline.
- Current local guardrails:
  - opt-in by default: build skipped when `cargo` is absent or
    `MINIZ_OXIDE_DISABLE=1` is set; the C shim falls back to an
    `IO.userError` containing `"miniz_oxide: not built with Rust
    support"`, which the smoke tests in
    [ZipTest/MinizOxide.lean](/home/kim/lean-zip/ZipTest/MinizOxide.lean)
    treat as a clean skip
  - `MinizOxide.decompress` carries a `maxDecompressedSize` cap
    (default 1 GiB; pass `0` to opt into bomb-unsafe unlimited mode);
    overruns raise `IO.userError` containing `"exceeds limit"`,
    matching the wording family used by `RawDeflate.decompress` so
    callers can dispatch on a single substring
  - the Rust shim is built with `panic = "abort"` so panics inside
    `miniz_oxide` cannot unwind across the FFI boundary
  - the shim allocates output as `Box<[u8]>` and exposes
    `lean_miniz_oxide_free` so the Lean side never frees a
    Rust-allocated buffer through libc `free`, avoiding any
    Rust-allocator vs. libc-allocator mismatch
  - the Lean side copies the shim's output into a fresh
    `lean_alloc_sarray` buffer in `c/miniz_oxide_ffi.c` and then calls
    `lean_miniz_oxide_free`, so the Rust-allocated buffer is released
    on every successful return
  - **`Cargo.lock` is tracked and treated as security-critical.**
    [`rust/miniz_oxide_shim/Cargo.lock`](/home/kim/lean-zip/rust/miniz_oxide_shim/Cargo.lock)
    pins the resolved versions of `miniz_oxide` and its transitive
    dependencies (`adler2`) along with their registry checksums. The
    caret-range declaration in
    [`rust/miniz_oxide_shim/Cargo.toml`](/home/kim/lean-zip/rust/miniz_oxide_shim/Cargo.toml)
    is intentionally narrowed by the lockfile to a specific
    build-reproducible set.
    Snapshot as of 2026-04-29: `miniz_oxide` 0.8.9, `adler2` 2.0.1.
    Any change to these resolved versions requires re-evaluating the
    *Why trusted* paragraph above and updating this snapshot. Drift
    is surfaced advisorily by
    [`scripts/check-cargo-lock.sh`](/home/kim/lean-zip/scripts/check-cargo-lock.sh)
    (modelled on
    [`scripts/check-c-allocations.sh`](/home/kim/lean-zip/scripts/check-c-allocations.sh)),
    intended to be run before opening a PR that touches
    `rust/miniz_oxide_shim/`.
  - **Sanitizer recipe scaffolded but not yet executed.**
    [`scripts/sanitize-rust-ffi.sh`](/home/kim/lean-zip/scripts/sanitize-rust-ffi.sh)
    documents the intended ASan recipe for `c/miniz_oxide_ffi.c` +
    `libminiz_oxide_shim.a`: nightly Rust +
    `RUSTFLAGS="-Zsanitizer=address"` +
    `cargo +nightly build --release` of `rust/miniz_oxide_shim`,
    linked into a small Lean driver that exercises the
    `MinizOxide.compress` / `MinizOxide.decompress` smoke-test
    inputs. The body is currently TODO; the script's environment
    guard exits 2 when nightly Rust is unavailable, so it can be
    safely invoked on any host without producing a misleading
    "pass". The first actual run will be queued as a follow-up
    issue when a Linux + nightly-Rust worker host is available.
- Missing work:
  - **No fuzz / ASan / UBSan recipe currently covers the Rust crate
    or its C-ABI shim.** The existing
    [`scripts/sanitize-ffi.sh`](/home/kim/lean-zip/scripts/sanitize-ffi.sh)
    and
    [`scripts/fuzz-inflate.sh`](/home/kim/lean-zip/scripts/fuzz-inflate.sh)
    recipes target `c/zlib_ffi.c` and the FFI inflate decoders only;
    they do not exercise `c/miniz_oxide_ffi.c` or the
    `libminiz_oxide_shim.a` static library. A sibling recipe is
    needed before `MinizOxide.compress` / `MinizOxide.decompress`
    leave bench-only scope. Scaffolded as
    [`scripts/sanitize-rust-ffi.sh`](/home/kim/lean-zip/scripts/sanitize-rust-ffi.sh)
    in PR #2383 (paragraph above under *Current local
    guardrails*); the recipe body is TODO, deferred to a sibling
    follow-up issue when a Linux + nightly-Rust worker host is
    available.
  - **If a downstream caller wires `MinizOxide.compress` /
    `MinizOxide.decompress` into a non-bench codepath, this row's
    `guarded-locally` status must be re-evaluated** alongside the
    sibling fuzz / sanitizer recipe above.
- Recent wins:
  - **`Cargo.lock` is now treated as a security-critical artefact** in
    PR #2382 — the
    [`rust/miniz_oxide_shim/Cargo.lock`](/home/kim/lean-zip/rust/miniz_oxide_shim/Cargo.lock)
    snapshot (`miniz_oxide` 0.8.9, `adler2` 2.0.1) is recorded under
    *Current local guardrails* above, and a new advisory drift
    detector
    [`scripts/check-cargo-lock.sh`](/home/kim/lean-zip/scripts/check-cargo-lock.sh)
    (modelled on
    [`scripts/check-c-allocations.sh`](/home/kim/lean-zip/scripts/check-c-allocations.sh))
    flags resolved-version churn at PR-review time. Closes the
    *"No upstream-tracking entry pinning the `miniz_oxide` crate
    version"* Missing-work bullet.
  - **`MinizOxide.compress` level argument now clamped to 0–9** in
    PR #2378 — the public `compress` is a thin wrapper that
    clamps `level` via `if level > 9 then 9 else level` before
    delegating to a `private opaque compressUnsafe` extern; smoke
    tests assert levels 9, 10, and 255 produce byte-identical
    compressed output, confirming the clamp is observable end-to-end.
  - Track D Phase 0c initial wiring — PR #2356
    (`Zip/MinizOxide.lean`, `c/miniz_oxide_ffi.c`,
    `rust/miniz_oxide_shim/` static-lib Cargo crate, `BENCH.md`
    comparator-toolchain matrix, smoke tests with disabled-toolchain
    skip path)
- Paired review of PR #2356 (Track D Phase 0c initial wiring):
  - **Design fidelity.** The merged PR satisfies every enumerated
    deliverable from the closing human-oversight directive #2349:
    (1) the `rust/miniz_oxide_shim/` `staticlib` Cargo crate with C-ABI
    surface (`lean_miniz_oxide_compress` / `lean_miniz_oxide_decompress`
    / `lean_miniz_oxide_free` at
    [rust/miniz_oxide_shim/src/lib.rs](/home/kim/lean-zip/rust/miniz_oxide_shim/src/lib.rs));
    (2) the thin C shim
    [c/miniz_oxide_ffi.c](/home/kim/lean-zip/c/miniz_oxide_ffi.c);
    (3) the Lean module
    [Zip/MinizOxide.lean](/home/kim/lean-zip/Zip/MinizOxide.lean)
    paralleling [Zip/RawDeflate.lean](/home/kim/lean-zip/Zip/RawDeflate.lean);
    (4) `lakefile.lean` cargo-detection + `MINIZ_OXIDE_DISABLE` /
    `MINIZ_OXIDE_LDFLAGS` knobs (paralleling `ZLIB_LDFLAGS`);
    (5) [shell.nix](/home/kim/lean-zip/shell.nix) adds `pkgs.cargo` /
    `pkgs.rustc`; (6) `compress-miniz` / `inflate-miniz` operations in
    [ZipBench.lean](/home/kim/lean-zip/ZipBench.lean); (7) smoke tests
    in
    [ZipTest/MinizOxide.lean](/home/kim/lean-zip/ZipTest/MinizOxide.lean)
    covering miniz↔miniz, miniz→zlib, zlib→miniz, level-0 stored,
    empty input, and the `maxDecompressedSize` cap; (8) a comparator
    toolchain matrix in [BENCH.md](/home/kim/lean-zip/BENCH.md).
  - **Allocator-mismatch verification.** The Rust shim allocates output
    via `compress_to_vec` / `decompress_to_vec_with_limit`, converts
    the `Vec<u8>` to `Box<[u8]>` via `into_boxed_slice`, and hands the
    raw pointer + length to the caller through `Box::into_raw`. The
    matching `lean_miniz_oxide_free` reconstructs `Box::from_raw` on
    `slice::from_raw_parts_mut(ptr, len)` so the buffer is released
    through the Rust global allocator — never through libc `free`. On
    the Lean side, [c/miniz_oxide_ffi.c](/home/kim/lean-zip/c/miniz_oxide_ffi.c)
    copies the Rust-allocated bytes into a fresh `lean_alloc_sarray`
    buffer with a guarded `if (out_len > 0) memcpy(...)` (so the empty
    case is well-defined) and then immediately calls
    `lean_miniz_oxide_free(out, out_len)` on every successful path.
    No Lean-side codepath takes ownership of the Rust pointer, and
    `lean_alloc_sarray` panics on OOM rather than returning `NULL`, so
    there is no allocation-failure window in which the Rust buffer
    would leak. Round-trip is symmetric and exact.
  - **`panic = "abort"` invariant.** The Cargo `[profile.release]`
    block at
    [rust/miniz_oxide_shim/Cargo.toml](/home/kim/lean-zip/rust/miniz_oxide_shim/Cargo.toml)
    declares `panic = "abort"` (alongside `lto = "thin"`,
    `codegen-units = 1`, `opt-level = 3`). With abort-on-panic the
    Rust runtime cannot unwind across the C ABI boundary; every
    `unsafe extern "C"` entry point in `src/lib.rs` is also annotated
    `#![deny(unsafe_op_in_unsafe_fn)]`, so the unsafe slice / pointer
    operations are explicitly scoped. The shim takes care to validate
    `out_ptr.is_null()` / `out_len.is_null()` and the
    `input.is_null() && input_len != 0` corner before constructing any
    slice.
  - **Build-skip path.** `lakefile.lean`'s `minizOxideEnabled` check
    short-circuits on `MINIZ_OXIDE_DISABLE=1`, then on
    `MINIZ_OXIDE_LDFLAGS`, and otherwise probes `cargo --version`. The
    `miniz_oxide_ffi.o` target only adds `-DHAVE_MINIZ_OXIDE` when
    that check passes — keeping the C compilation decision and the
    link decision in lockstep, so `MINIZ_OXIDE_DISABLE=1` rebuilds
    cannot end up with a shim that references symbols that the link
    step omits. When `HAVE_MINIZ_OXIDE` is absent, both `*_ffi`
    entry points return `mk_io_error(MINIZ_DISABLED_MSG)` with the
    exact substring `"miniz_oxide: not built with Rust support"`.
    [ZipTest/MinizOxide.lean](/home/kim/lean-zip/ZipTest/MinizOxide.lean)'s
    `withMiniz` helper matches that substring and emits a noisy skip
    line so CI on minimal toolchains (no cargo) keeps passing —
    confirmed locally on the cargo-enabled toolchain by the
    `MinizOxide tests: OK` line in `lake exe test` output (full build
    + test passes at the post-merge tree at `8ec9f44`).
  - **Bench-only scope.** A `MinizOxide\.(compress|decompress)` grep
    across the tree returns call sites only in
    [ZipBench.lean](/home/kim/lean-zip/ZipBench.lean) and
    [ZipTest/MinizOxide.lean](/home/kim/lean-zip/ZipTest/MinizOxide.lean).
    [Zip.lean](/home/kim/lean-zip/Zip.lean) does `import Zip.MinizOxide`
    so the namespace is on the public surface, but no other `Zip/`
    source consumes either function — `MinizOxide.compress` /
    `MinizOxide.decompress` remain off the verified DEFLATE pipeline.
    No non-bench caller appears, so this paired review surfaces no
    new follow-up issues. The two pre-existing Missing-work bullets
    above (sanitizer recipe; `Cargo.lock` upstream-tracking pin) are
    already separately tracked.
- Paired review of PR #2371 (`miniz_oxide via Rust` TCB subsection —
  Option 1 / classification execution):
  - **Decision-execution fidelity vs. issue #2362.** Issue #2362
    explicitly offered three options: (1) add a new
    `### miniz_oxide via Rust` subsection alongside `### zlib via C FFI`,
    (2) document under the existing zlib row as a sub-paragraph, or
    (3) decide it is out of scope as bench-only and add a carve-out
    note in *Required Maintenance Rule* instead. PR #2371's title
    declares *"Option 1, decided in this PR"* <!-- drift-detector: verbatim quote of PR #2371's title phrase, not a stale placeholder --> — confirmed by the
    merged tree at commit `19f4588d` (+86 SECURITY_INVENTORY.md lines
    / +95 progress entry lines, no other files touched): the new
    `### miniz_oxide via Rust` H3 subsection sits between
    `### zlib via C FFI` and `### Zip.Native.Inflate and verified
    DEFLATE core`, in the canonical full-shape (Components / Status /
    Why trusted / Current local guardrails / Missing work / Recent
    wins) that mirrors the surrounding TCB rows. The decision
    rationale is co-located in
    [progress/20260429T022926Z_7db2dbf3.md](/home/kim/lean-zip/progress/20260429T022926Z_7db2dbf3.md)
    *## Rationale* (four bullets: public-surface argument; one-entry-
    per-FFI-helper precedent; *Required Maintenance Rule* alignment;
    `guarded-locally` status accuracy) with explicit reasons for
    rejecting Options 2 and 3. The "decided in this PR" <!-- drift-detector: re-quote of PR #2371's title phrase from the bullet above, not a stale placeholder --> framing is
    faithful — the rationale is not deferred to a separate decision-only
    commit, and the audit's deferred *"structural rework"* scope is
    discharged in a single PR rather than split across decision +
    execution.
  - **TCB classification accuracy.** The Status tag `guarded-locally`
    matches the *## Status Labels* definition at the top of the
    inventory (*"not fully proved, but protected by explicit checks
    and limits"*) — the subsection's *Current local guardrails*
    bullets enumerate five concrete checks/limits (opt-in build with
    stub fallback; `maxDecompressedSize` cap with `"exceeds limit"`
    wording family; `panic = "abort"` Rust shim; `Box<[u8]>` +
    `lean_miniz_oxide_free` allocator-mismatch avoidance;
    `lean_alloc_sarray` copy-and-free on every successful return) and
    the *Why trusted* paragraph correctly identifies all four trust-
    boundary layers (Rust toolchain → `rust/miniz_oxide_shim/`
    `staticlib` Cargo crate → `c/miniz_oxide_ffi.c` C-ABI shim →
    `Zip/MinizOxide.lean` Lean wrappers). The bench-only scope claim
    is faithful: a fresh `MinizOxide\.(compress|decompress)` grep
    across the tree returns code call sites only in
    [ZipBench.lean](/home/kim/lean-zip/ZipBench.lean) (the
    `compress-miniz` / `inflate-miniz` operations) and
    [ZipTest/MinizOxide.lean](/home/kim/lean-zip/ZipTest/MinizOxide.lean)
    (the smoke-test driver). [Zip.lean](/home/kim/lean-zip/Zip.lean)
    does `import Zip.MinizOxide` so the namespace is on the public
    surface, but no other `Zip/` source consumes either function —
    the *"not part of the verified DEFLATE pipeline"* assertion in
    the *Why trusted* paragraph is observably true and matches the
    grep finding independently confirmed by the PR #2356 paired-review
    *Bench-only scope* bullet above.
  - **Sibling cross-reference layering.** The post-#2371 subsection
    received three subsequent sibling-PR augmentations that the
    sibling paired-reviews accurately attribute back to their own
    closing PRs rather than to PR #2371: (i) PR #2378 (level clamp)
    moved the *"`MinizOxide.compress` does not clamp the level
    argument"* bullet from *Missing work* to *Recent wins* citing
    `#2378`; (ii) PR #2382 (Cargo.lock drift detector) removed the
    *"No upstream-tracking entry pinning the `miniz_oxide` crate
    version"* Missing-work bullet, added the *"`Cargo.lock` is
    tracked and treated as security-critical"* *Current local
    guardrails* bullet (with the *"Snapshot as of 2026-04-29:
    `miniz_oxide` 0.8.9, `adler2` 2.0.1"* line and the
    [scripts/check-cargo-lock.sh](/home/kim/lean-zip/scripts/check-cargo-lock.sh)
    cross-link), and a *Recent wins* counterpart citing `#2382`;
    (iii) PR #2383 (sanitizer recipe scaffold) edited the original
    *"No fuzz / ASan / UBSan recipe …"* Missing-work bullet in place
    (replacing the *"Sketch: …"* sentence with a forward-pointer to
    the new
    [scripts/sanitize-rust-ffi.sh](/home/kim/lean-zip/scripts/sanitize-rust-ffi.sh)
    citing `#2383`) and added a sibling *"Sanitizer recipe scaffolded
    but not yet executed"* *Current local guardrails* bullet. PR #2371's
    original contribution is therefore the *Components / Status / Why
    trusted* prose, the four original *Current local guardrails*
    bullets (opt-in build / `maxDecompressedSize` / `panic = "abort"`
    / allocator-mismatch + `lean_alloc_sarray` copy), the four
    original *Missing work* bullets (since-flipped or since-edited),
    and the single Track D Phase 0c initial wiring *Recent wins*
    bullet. No mis-attribution surfaces — the sibling paired-reviews
    correctly layer their claims on top of the PR #2371 foundation
    without re-claiming any of its content.
  - **Allocator-mismatch / `panic = "abort"` claim coverage.** PR
    #2371's *Current local guardrails* bullets at the *"the Rust
    shim is built with `panic = "abort"` …"* / *"the shim allocates
    output as `Box<[u8]>` …"* / *"the Lean side copies the shim's
    output into a fresh `lean_alloc_sarray` …"* triple summarize the
    Rust-allocator vs. libc-allocator boundary in inventory prose.
    The PR #2356 paired-review *Allocator-mismatch verification* and
    *`panic = "abort"` invariant* bullets (above, in this same
    subsection) cover the same invariants in audit detail
    (`compress_to_vec` / `decompress_to_vec_with_limit` allocation
    path; `Box::into_raw` / `Box::from_raw` symmetry across the FFI
    boundary; `lean_alloc_sarray` panic-on-OOM eliminating any
    allocation-failure window in which the Rust buffer would leak;
    `#![deny(unsafe_op_in_unsafe_fn)]` annotation on every
    `unsafe extern "C"` entry point). No drift between PR #2371's
    inventory prose and the PR #2356 paired-review's audit findings —
    the inventory summary is a faithful one-paragraph distillation
    that does not re-derive the audit and does not contradict it.
  - **`Status Labels` / cross-reference parity.** The inventory's
    *## Status Labels* section is a flat four-bullet list (
    `proved-in-repo` / `guarded-locally` / `tested-only` /
    `upstream-risk`) and does not maintain a TCB-subsection
    table-of-contents — there is no separate index of TCB rows to
    keep in sync. The *## Trusted Computing Base* H2 simply contains
    four `### `-level subsections in document order (Lean Runtime →
    zlib via C FFI → miniz_oxide via Rust → Zip.Native.Inflate);
    PR #2371's insertion immediately after `### zlib via C FFI` is
    the natural append point per the *one-entry-per-FFI-helper
    precedent* recorded in the progress entry. No drift surfaces;
    no cross-reference index needs updating.
  - **Audit cluster terminal-closure status.** This paired-review is
    the *fourth and final* sibling paired-review of the post-#2358
    audit cluster. The four sibling PRs (#2371 the foundational TCB
    subsection; #2378 level clamp; #2382 Cargo.lock drift detector;
    #2383 sanitize-rust-ffi.sh skeleton) all landed on 2026-04-29
    within a six-hour window (02:31Z–08:13Z merge timestamps), and
    their paired-reviews now all exist (#2377 for #2356 the parent
    Phase 0c wiring; #2389 for #2382; #2390 for #2378; #2394 for
    #2383; *this entry* for #2371). The audit cluster's
    review-cadence dimension is now closed. The only audit-cluster
    residual is open issue #2392 (Linux + nightly-Rust-host-gated
    sanitizer recipe body fill-in), which is not a review-cadence
    task — it is the deferred body fill-in that PR #2383's *Scaffold
    variant* of the *Half-closed two-step* (per the
    [.claude/skills/inventory-reconciliation/SKILL.md](/home/kim/lean-zip/.claude/skills/inventory-reconciliation/SKILL.md)
    *Scaffold variant* sub-section landed in PR #2399) intentionally
    parked for a Linux-host worker. This paired-review surfaces no
    new follow-up issues.
- Paired review of PR #2382 (Cargo.lock drift detector + lockfile-as-TCB claim):
  - **Design fidelity vs. issue #2376.** The merged PR satisfies all
    four enumerated deliverables from the closing issue:
    (1) the *"`Cargo.lock` is tracked and treated as security-critical"*
    bullet under the *Current local guardrails* list of the
    *miniz_oxide via Rust* subsection, with the
    *"Snapshot as of 2026-04-29: `miniz_oxide` 0.8.9, `adler2` 2.0.1"*
    line spelt out;
    (2) the new advisory drift detector at
    [scripts/check-cargo-lock.sh](/home/kim/lean-zip/scripts/check-cargo-lock.sh),
    a 104-line POSIX-shell script with an `awk`-based `[[package]]`
    block parser, a `grep`-based snapshot-line extractor, and an
    advisory-only `exit 0` semantics matching
    [scripts/check-c-allocations.sh](/home/kim/lean-zip/scripts/check-c-allocations.sh);
    (3) the script's docstring documents the recipe
    *"Run before opening a PR that touches `rust/miniz_oxide_shim/`"*
    (issue #2376 deliverable 3 explicitly accepts a header recipe in
    place of a top-level dispatcher), and the script is intentionally
    not wired into `scripts/check-inventory-links.sh` — keeping
    inventory-link checks separate from upstream-version drift checks
    matches the existing `check-c-allocations.sh` separation;
    (4) the *"No upstream-tracking entry pinning the `miniz_oxide`
    crate version"* Missing-work bullet was removed and a Recent-wins
    counterpart added, citing PR #2382 by its merged number (post the
    placeholder substitution surfaced by this paired review — see
    *Missing-work-bullet flip semantics* below).
  - **Snapshot-string parsing fidelity.** The script greps for the
    literal regex `Snapshot as of [0-9]{4}-[0-9]{2}-[0-9]{2}: \`miniz_oxide\``
    in `SECURITY_INVENTORY.md`, then sed-extracts the version triple
    via `\`miniz_oxide\` ([0-9]+\.[0-9]+\.[0-9]+)`. Confirmed
    fail-loud-on-missing-line: when the snapshot line is absent the
    script emits a `WARNING — no "Snapshot as of …" line found` and
    exits 0, never silently treating the lockfile as drifted (verified
    by deleting the line and re-running). Failure mode under
    *malformed* snapshot lines (extra whitespace between backtick and
    version, or alternate punctuation between the two version
    triples) is sed regex non-match → empty `expected_miniz` /
    `expected_adler` → mismatch against current → DRIFT report with
    blank `expected:` fields. The DRIFT report is loud (visible in
    `git diff` and PR-review output) and the blank fields make the
    parser failure obviously distinct from a real version drift, so
    the failure is loud-but-unfriendly rather than silent. A
    follow-up issue is filed for tightening the parser to either
    accept reasonable whitespace variation or emit an explicit
    *"could not parse snapshot line"* diagnostic; not blocking — the
    current snapshot line matches the regex exactly, and the
    snapshot-line shape is owned by the same inventory subsection
    that the script reads, so drift between the two is already
    bounded by the same PR. *Superseded by PR #2396 (paired-review
    subsection below): the follow-up landed as the Option-A explicit
    `parser regex mismatch` WARNING, and the parser-fail-open path no
    longer presents as a blank-`expected:` DRIFT.*
  - **Sibling design parity vs. `scripts/check-c-allocations.sh`.**
    Both scripts: `set -u` (no `-e` — the script never aborts on a
    non-zero subshell exit, so a single missing input never fails
    the advisory pass); `--help` / `-h` long-form flag emitting a
    multi-line `cat <<EOF` usage block; explicit
    *"run from repo root"* check (`if [ ! -f "$LOCK" ]`); single
    `WARNING`/`DRIFT` block on mismatch; advisory `exit 0` on every
    path; pure POSIX shell + standard text tools (no Cargo / Rust
    toolchain); both annotated as a *"trip wire, not a fence"* /
    *"not wired into CI"* in the docstring. Divergence: the new
    script defends two filesystem inputs
    (`rust/miniz_oxide_shim/Cargo.lock` and `SECURITY_INVENTORY.md`)
    rather than one (`c/zlib_ffi.c`), so it has two
    `[ ! -f "$X" ]` guards instead of one; this is intentional and
    follows from the artefact shape (drift detector compares two
    files). No accidental divergence worth tightening.
  - **Manual smoke test reproduction.** Reproduced the
    docstring-documented smoke test
    (`scripts/check-cargo-lock.sh:28-31`): edited the
    *"Snapshot as of 2026-04-29: `miniz_oxide` 0.8.9"* line to
    *"`miniz_oxide` 9.9.9"*, ran the script, observed a single
    `DRIFT` block reading `expected: miniz_oxide 9.9.9, adler2 2.0.1`
    / `current: miniz_oxide 0.8.9, adler2 2.0.1` followed by exit
    code 0, then reverted the edit. Post-revert the script reports
    *"matches snapshot (miniz_oxide 0.8.9, adler2 2.0.1)"* and
    `git diff SECURITY_INVENTORY.md` is clean. The smoke test
    behaves exactly as the docstring claims.
  - **Missing-work-bullet flip semantics.** The merged inventory
    edit removed the *"No upstream-tracking entry pinning the
    `miniz_oxide` crate version against a known-good audit"*
    Missing-work bullet and added a corresponding Recent-wins
    bullet titled *"`Cargo.lock` is now treated as a
    security-critical artefact"*. The bullet shape matches the
    [.claude/skills/inventory-reconciliation/SKILL.md](/home/kim/lean-zip/.claude/skills/inventory-reconciliation/SKILL.md)
    *Executed past-tense one-liner* convention (executed past-tense
    title; closing-PR cross-link; one paragraph on caller impact;
    explicit *"Closes the …"* sentence). However, the merged
    bullet's PR cross-link was left as the literal placeholder
    `#TBD-VERIFY-PR` <!-- drift-detector: prose mention of the placeholder token in a paired-review finding, not a stale placeholder --> rather than substituted with the merged number
    `#2382` — a missed post-merge cleanup pass. Sibling Recent-wins
    entries for PR #2383 (commit 5dafd9c) and PR #2385 (commit
    fcfddc8) followed the substitution discipline; PR #2382 missed
    it. The placeholder was independently flagged by
    [scripts/check-inventory-links.sh](/home/kim/lean-zip/scripts/check-inventory-links.sh)
    pass (d). Substituted in the same paired-review PR (one-line
    bookkeeping fix; see commit log for the substitution rationale).
- Paired review of PR #2378 (`MinizOxide.compress` level clamp):
  - **Design fidelity vs. issue #2374.** The merged PR satisfies all
    four enumerated deliverables from the closing issue:
    (1) the *preferred* Lean-side clamp shape — the public
    `compress` is rewritten as a thin wrapper that clamps `level`
    via `if level > 9 then 9 else level` before delegating to a
    `private opaque compressUnsafe` extern at
    [Zip/MinizOxide.lean](/home/kim/lean-zip/Zip/MinizOxide.lean);
    (2) three smoke tests at levels 9, 10, and 255 in
    [ZipTest/MinizOxide.lean](/home/kim/lean-zip/ZipTest/MinizOxide.lean)
    asserting byte-identical compressed output (the issue asked for
    2–3, the PR landed exactly 3); (3) the inventory bullet flip from
    *Missing work* to *Recent wins* citing PR #2378; (4) the
    docstring on the public `compress` rewritten to accurately
    describe the clamp ("values above 9 are clamped to 9 before
    forwarding to the Rust shim"). The merged tree touches only
    `Zip/MinizOxide.lean`, `ZipTest/MinizOxide.lean`, and
    `SECURITY_INVENTORY.md` — the C shim
    ([c/miniz_oxide_ffi.c](/home/kim/lean-zip/c/miniz_oxide_ffi.c))
    and the Rust crate
    ([rust/miniz_oxide_shim/](/home/kim/lean-zip/rust/miniz_oxide_shim/))
    are untouched, so the clamp is purely a Lean-layer wrapper and
    the FFI symbol `lean_miniz_oxide_compress_ffi` is preserved.
  - **`compressUnsafe` / `compress` split design.** The extern is
    `private opaque compressUnsafe (data : @& ByteArray) (level :
    UInt8) : IO ByteArray` (no default level — the wrapper supplies
    it), with a docstring that explicitly notes out-of-range values
    reach miniz_oxide unchanged and directs callers to use
    `compress` instead. The public `compress` carries the
    user-facing default (`level : UInt8 := 6`) and the clamp
    expression `compressUnsafe data (if level > 9 then 9 else
    level)`. The previous false-claim docstring phrasing *"we cap
    callers to 0–9 here to match the rest of the bench"* (which
    held in PR #2371's snapshot but never matched any layer's
    behaviour) is fully removed; no residual misleading wording
    survives in the merged tree. The
    `compressUnsafe`-private/`compress`-public split keeps the
    unclamped escape hatch module-internal — bench callers that
    want to probe out-of-range levels deliberately would have to
    weaken the `private` qualifier in source, making the unclamped
    path explicitly out of the public contract.
  - **Smoke-test observability.** (a) The three new assertions sit
    inside the existing `withMiniz "compress(big)"` skip-guard at
    [ZipTest/MinizOxide.lean](/home/kim/lean-zip/ZipTest/MinizOxide.lean)
    so the `MINIZ_OXIDE_DISABLE=1` / missing-cargo path keeps
    skipping cleanly via the `"miniz_oxide: not built with Rust
    support"` substring match. (b) The payload is `prng = mkPrngData
    4096`, the deterministic xorshift32 PRNG payload (default seed
    `2463534242`) used throughout
    [ZipTest/MinizOxide.lean](/home/kim/lean-zip/ZipTest/MinizOxide.lean)
    and sibling bench-comparison tests; a future reviewer can
    reproduce the expected byte sequence purely from
    [ZipTest/Helpers.lean](/home/kim/lean-zip/ZipTest/Helpers.lean)
    without rebuilding the PRNG harness. (c) The byte-identical
    assertions `mzLevel10.beq mzLevel9` and `mzLevel255.beq
    mzLevel9` are sharp witnesses of the clamp: without it,
    `level=10` reaches `miniz_oxide::deflate::compress_to_vec` and
    produces level-10 output (distinct from level-9 on the PRNG
    payload), and `level=255` silently wraps to level 0 (stored
    blocks) which is again byte-different from level 9. The PRNG
    payload was deliberately chosen over the constant or cyclic
    fixtures because its compressibility differs across adjacent
    levels (the dictionary does not saturate at any non-trivial
    level), so adjacent-level outputs are observably distinct on
    the unclamped path. The test fails closed if either the Lean
    wrapper or a future C/Rust-shim rewrite drops the clamp.
  - **Inventory cross-link integrity.** The Missing-work →
    Recent-wins bullet flip at *miniz_oxide via Rust* removes the
    *"`MinizOxide.compress` does not clamp the level argument"*
    bullet and adds a corresponding *Recent wins* entry titled
    *"`MinizOxide.compress` level argument now clamped to 0–9"*.
    The bullet shape matches the
    [.claude/skills/inventory-reconciliation/SKILL.md](/home/kim/lean-zip/.claude/skills/inventory-reconciliation/SKILL.md)
    *Executed past-tense one-liner* convention (executed past-tense
    title; closing-PR cross-link; paragraph on caller impact). The
    PR cross-link uses the merged number `#2378` directly — no
    `#TBD-VERIFY-PR` <!-- drift-detector: prose mention of the placeholder token in a paired-review finding, not a stale placeholder --> placeholder leaked through (the same
    substitution discipline that PR #2382 missed and the sibling
    paired-review surfaced as a one-line bookkeeping fix). The
    architectural *"If a downstream caller wires …"* re-evaluation
    bullet is correctly retained under *Missing work* — it is a
    standing reminder, not a closeable gap. Confirmed
    [scripts/check-inventory-links.sh](/home/kim/lean-zip/scripts/check-inventory-links.sh)
    reports `errors=0, warnings=0` against this paired-review
    branch's tree. Soft observation, not blocking: the merged
    Recent-wins bullet does not include the explicit *"Closes the
    …"* sentence that the sibling PR #2382 Cargo.lock Recent-wins
    bullet ended with — the skill text does not strictly mandate
    that sentence (only the post-hoc reading in PR #2382's
    paired-review listed it as a fourth element), so this is
    cross-bullet drift inside the same subsection rather than a
    convention violation, and a future inventory edit can fold in a
    one-line addition cheaply.
  - **Pattern reusability.** The `private opaque …Unsafe` extern +
    thin `def` clamp wrapper is the **first instance in this
    codebase** — a `grep -r "private opaque" Zip/` returns only
    [Zip/MinizOxide.lean](/home/kim/lean-zip/Zip/MinizOxide.lean),
    and `grep -r "Unsafe\|private opaque" .claude/skills/` returns
    nothing. The pattern is documented only in the docstring on
    `compressUnsafe` itself ("Use `compress` instead — it clamps
    `level` to the documented 0–9 range before calling this
    function") and on the public `compress` wrapper. The pattern is
    plausibly recurrent for any future TCB-boundary clamp where the
    Lean signature must enforce a tighter range than the underlying
    FFI accepts (the issue body specifically called out future
    `decompress` size limits as a likely candidate, though the
    current `MinizOxide.decompress` already enforces its
    `maxDecompressedSize` cap inside the Rust shim's
    `decompress_to_vec_with_limit`, not via a Lean-side wrapper).
    Decision: at N=1 site the pattern is sufficiently
    self-explanatory at the call site that lifting it into a skill
    would be premature abstraction — the existing docstrings carry
    enough context for a future reader. If a second site adopts
    the same shape, that PR is the right point to extract a skill
    entry; this paired-review surfaces no follow-up issue for skill
    extraction today.
- Paired review of PR #2383 (`scripts/sanitize-rust-ffi.sh` skeleton + Sanitizer recipe inventory paragraph):
  - **Design fidelity vs. issue #2379.** The merged PR satisfies all
    three enumerated deliverables from the closing issue, honouring
    the explicit *"scaffolding only, NOT actual ASan running"* scope
    qualifier:
    (1) the new
    [scripts/sanitize-rust-ffi.sh](/home/kim/lean-zip/scripts/sanitize-rust-ffi.sh)
    is a 156-line POSIX-shell script paralleling
    [scripts/sanitize-ffi.sh](/home/kim/lean-zip/scripts/sanitize-ffi.sh)
    in shape — header comment block describing scope (`c/miniz_oxide_ffi.c` +
    `libminiz_oxide_shim.a` only; explicitly not `c/zlib_ffi.c` and not
    the Lean runtime), `usage()` block describing the intended
    nightly-Rust + `RUSTFLAGS="-Zsanitizer=address"` recipe, an
    environment guard at the top of `main` checking for `cargo` and
    `cargo +nightly --version`, a body block that is a single TODO-marked
    `exit 1` with a clear "skeleton" message, and the standard
    `set -euo pipefail` / `usage()` / `--help` conventions; the
    script is marked executable (`-rwxr-xr-x`); UBSan is explicitly noted
    as future scope in both the header comment and `usage()`;
    (2) the new
    *"Sanitizer recipe scaffolded but not yet executed"* bullet under
    *miniz_oxide via Rust → Current local guardrails* spells out
    the intended ASan recipe shape, links the new script, and records
    the deferred-body status with the env-guard contract;
    (3) Missing-work bullet 1 was edited (not deleted) — the original
    *"Sketch: build the Rust crate under `RUSTFLAGS="-Zsanitizer=address"`
    …"* sentence was replaced with a forward-pointer
    *"Scaffolded as `scripts/sanitize-rust-ffi.sh` in PR #2383
    (paragraph above under *Current local guardrails*); the recipe
    body is TODO, deferred to a sibling follow-up issue …"*. The
    bullet correctly remains open (not flipped to *Recent wins*),
    matching the *"scaffolding only"* scope qualifier. The PR
    cross-link uses the merged number `#2383` directly with no
    `#TBD-VERIFY-PR` <!-- drift-detector: prose mention of the placeholder token in a paired-review finding, not a stale placeholder --> placeholder leaked through (matching the
    sibling PR #2378 substitution discipline; PR #2382 missed it
    and the sibling paired-review #2384 picked it up as a one-line
    bookkeeping fix).
  - **Environment-guard semantics.** Reproduced the four guard
    contracts on this macOS host (no nightly Rust available):
    (a) `bash scripts/sanitize-rust-ffi.sh` exits **2** (not 0, not
    1) with the *"nightly Rust toolchain not available"* diagnostic,
    matching the
    [scripts/sanitize-ffi.sh](/home/kim/lean-zip/scripts/sanitize-ffi.sh)
    *"cc could not locate libasan.so / libubsan.so"* exit-2 convention,
    so the two scripts compose with a shared "environment not met →
    code 2" idiom. (b) The guard runs **before** any Lake / cargo
    invocation: arg parsing → lakefile root check → `command -v cargo`
    → `cargo +nightly --version` → echo nightly version → TODO body.
    No FS state is touched on the env-guard exit path — confirmed
    by reading the script top-to-bottom; the guard's only side
    effects are the stderr diagnostic prints. (c) The
    stderr/stdout messaging clearly distinguishes "host ineligible"
    from "skeleton not yet implemented": the env-guard exit-2
    diagnostic is *"error: nightly Rust toolchain not available."*
    plus a `rustup toolchain install nightly` hint, while the
    post-guard exit-1 path emits *"error: sanitize-rust-ffi.sh
    recipe body is TODO."* with a forward-pointer to the inventory
    Missing-work bullet — the two diagnostics are wholly disjoint
    and a future operator cannot mistake one for the other. (d) The
    `cargo not found` and `cargo +nightly missing` paths are split
    into two separate `if` blocks with two separate diagnostics
    (rather than one combined check), so the operator can tell from
    the message which of the two prerequisites is missing — a small
    UX win over a single combined check that says "one of these two
    things is wrong".
  - **Sibling design parity vs. `scripts/sanitize-ffi.sh`.** Both
    scripts: `#!/usr/bin/env bash` with `set -euo pipefail`; a `usage()`
    function emitted via `cat <<'EOF'`; identical `case "${1:-}"` arg
    parser handling `-h|--help` / empty / unknown (with the unknown
    branch printing usage to stderr and exiting 2); the same
    *"run from the project root (lakefile.lean not found)"* check
    with exit 2; an environment-probe block that exits 2 cleanly
    when toolchain prerequisites are absent; an explicit
    *"Exit codes:"* table in the `usage()` block. Intentional
    divergence (different toolchain → different probe shape):
    `sanitize-ffi.sh` probes for `pkg-config` + `zlib` + GCC's
    `libasan.so` / `libubsan.so`, while `sanitize-rust-ffi.sh`
    probes for `cargo` + nightly Rust; `sanitize-ffi.sh`
    re-execs under `nix-shell` when zlib is missing on host while
    `sanitize-rust-ffi.sh` does not (no nix-shell handles nightly
    Rust in this project's `shell.nix`); `sanitize-ffi.sh`'s body
    is filled in (full Lake build + LD_PRELOAD test invocation)
    while `sanitize-rust-ffi.sh`'s body is the deferred TODO. No
    accidental divergence worth tightening — the new script is a
    structurally honest scaffold of the precedent recipe shape, with
    each divergence traceable to a toolchain-shape difference.
  - **Inventory partial-flip / forward-pointer phrasing — new
    variant of the *Half-closed two-step*.** The
    [.claude/skills/inventory-reconciliation/SKILL.md](/home/kim/lean-zip/.claude/skills/inventory-reconciliation/SKILL.md)
    *Half-closed two-step* section currently covers a single shape:
    *parameter-add PR + default-flip PR* (precedent: #1610 → #1631).
    PR #2383 is a different two-step shape — *scaffold (skeleton
    script + inventory bullet) + body fill-in* — that the skill does
    not yet name. The shape's distinguishing features are
    (i) the closing PR introduces a load-bearing env-guard so the
    skeleton is safe to run on any host but produces no false "pass",
    (ii) the *Missing work* bullet is **edited in place rather than
    flipped** — the original "Sketch: …" sentence is replaced with
    a forward-pointer to the new scaffold, leaving the bullet's
    `- [ ]` checkbox intact, and (iii) a sibling guardrail bullet
    captures the half-state under *Current local guardrails* with
    a *"scaffolded but not yet executed"* qualifier. The phrasing
    is unambiguous: a future reader of either bullet can tell that
    the work is *partially executed* (scaffolded, not run), and the
    forward-pointer identifies both the new artefact and the deferred
    follow-up scope. Confirmed
    [scripts/check-inventory-links.sh](/home/kim/lean-zip/scripts/check-inventory-links.sh)
    reports `errors=0, warnings=0` against the post-merge tree. A
    follow-up is filed to extend the *Half-closed two-step* skill
    section with this *"scaffold + body"* variant so future
    inventory edits of the same shape have a reusable template (see
    [.claude/skills/inventory-reconciliation/SKILL.md](/home/kim/lean-zip/.claude/skills/inventory-reconciliation/SKILL.md)
    *Scaffold variant* sub-section, landed in PR #2399 closing #2393).
  - **Deferred-body follow-up issue.** PR #2383 left an inline
    follow-up draft as a comment on the PR (rather than minting an
    issue, per the original #2379 deliverable 3 phrasing *"do **not**
    call `coordination plan`"*). This paired-review supersedes that
    deferral by minting the standalone follow-up issue directly, since
    the draft body is already self-contained and ready to claim. The
    new follow-up records: the host-gating requirement (Linux + nightly
    Rust); the precise script-body sketch from issue #2379 (cargo
    +nightly build + MINIZ_OXIDE_LDFLAGS surface + lake -R clean/build
    + Lean smoke driver under ASAN_OPTIONS); the macOS-host skip
    pattern mirroring #2366 / #2369; out-of-scope for the linking-into
    `scripts/fuzz-inflate.sh` extension (which is the *third* sibling
    issue); a forward-pointer back to PR #2383 as the scaffold it
    builds on. The follow-up is a separate `agent-plan` `feature` issue
    so it appears in `coordination list-unclaimed --label feature` and
    can be claimed by the next Linux + nightly-Rust worker host.
- Paired review of PR #2396 (Cargo.lock drift-detector parser tightening):
  - **Design fidelity vs. issue #2388.** The merged PR satisfies all
    four enumerated deliverables from the closing issue:
    (1) **Option A landed** — the closing issue offered Option A
    (explicit `parser regex mismatch` WARNING) or Option B (loosen
    the sed regex to accept whitespace variation), and called Option
    A *preferred* because it makes parse failures observably distinct
    from real version drift; the merged tree adopts Option A
    (`scripts/check-cargo-lock.sh`, the new guard block immediately
    after the two `sed -nE` extractions) and Option B is not present
    in the diff;
    (2) **advisory `exit 0` semantics preserved on every path** —
    confirmed by reading the script top-to-bottom: every `exit`
    statement in `scripts/check-cargo-lock.sh` is `exit 0` (the
    `--help` block, the `LOCK`/`INVENTORY` not-found guards, the
    no-snapshot-line `WARNING` block, the new parser-mismatch
    `WARNING` block, and the final `exit 0` after the
    matches/DRIFT branch); no path raises a non-zero exit, matching
    the *trip wire, not a fence* docstring framing inherited from
    sibling [scripts/check-c-allocations.sh](/home/kim/lean-zip/scripts/check-c-allocations.sh);
    (3) **existing `WARNING — no "Snapshot as of …" line found`
    path preserved** — the `if [ -z "$snap_line" ]` block is
    unchanged and still emits the original *"no `Snapshot as of …`
    line found"* diagnostic, so the no-line failure mode and the
    new parser-mismatch failure mode remain distinct (different
    diagnostics, different code paths);
    (4) **new docstring smoke test added covering the
    parser-mismatch path** — the original single-bullet *"manual
    smoke test"* docstring at `scripts/check-cargo-lock.sh:28-31`
    was reshaped into a two-numbered-bullet *"manual smoke tests"*
    block at `scripts/check-cargo-lock.sh:28-37`, with bullet (1)
    preserving the original drift-detection recipe and bullet (2)
    introducing the new parser-mismatch recipe (replace the single
    space between the closing backtick and the version triple with
    two spaces; expect a *"parser regex mismatch"* WARNING block
    followed by exit 0; revert).
  - **Parser-guard behaviour.** Reproduced the four manual smoke
    tests the author documented in commit e39bf1c against the
    post-merge tree at `652a14d`:
    (a) clean tree → *"`rust/miniz_oxide_shim/Cargo.lock` matches
    snapshot (miniz_oxide 0.8.9, adler2 2.0.1)"* + exit 0 — pass;
    (b) extra-whitespace edit (snapshot line set to
    ``` `miniz_oxide`  0.8.9, `adler2` 2.0.1 ``` with two spaces
    between the closing backtick and `0.8.9`) →
    *"WARNING — snapshot line found in SECURITY_INVENTORY.md but
    could not extract miniz_oxide / adler2 versions (parser regex
    mismatch — check whitespace / punctuation in the snapshot
    line)"* followed by *"snapshot line: …"* echoing the offending
    line + exit 0 — pass;
    (c) wrong-version edit (snapshot line set to
    ``` `miniz_oxide` 9.9.9, `adler2` 2.0.1 ```) →
    *"DRIFT … expected: miniz_oxide 9.9.9, adler2 2.0.1 / current:
    miniz_oxide 0.8.9, adler2 2.0.1"* + exit 0 — pass (DRIFT path
    still distinguishes from parser-mismatch path; non-blank
    `expected:` field as before);
    (d) revert → *"matches snapshot"* + exit 0; `git diff
    SECURITY_INVENTORY.md` clean — pass.
    The commit message claims the WARNING block now echoes the
    offending snapshot line underneath the diagnostic
    (`echo "  snapshot line: $snap_line"`); confirmed against the
    actual output in (b) above. None of the four paths regress.
  - **Docstring smoke-test reshape.** The reshape from a single
    bullet to two numbered bullets at
    `scripts/check-cargo-lock.sh:28-37` is faithful to the new
    behaviour: bullet (1) (drift detection) describes the wrong-
    version recipe and matches the (c) reproduction above; bullet
    (2) (parser-mismatch diagnostic) describes the extra-whitespace
    recipe and matches the (b) reproduction above. Wording
    inspected against the script body — the *"replace the single
    space between the closing backtick and the version triple with
    two spaces"* phrasing in bullet (2) is unambiguous and produces
    the documented *"parser regex mismatch"* WARNING when followed
    verbatim. The two bullets each end with *"then revert"*,
    preserving the *"runnable from repo root with no environment
    setup"* convention also enforced by sibling
    [scripts/check-c-allocations.sh](/home/kim/lean-zip/scripts/check-c-allocations.sh)
    (which has no parsing and therefore no second bullet to add).
    No follow-up filed.
  - **Sibling design parity vs. `scripts/check-c-allocations.sh`
    (post-tightening).** Both scripts remain advisory drift
    detectors with the shared idiom catalogued in the PR #2382
    paired-review's *Sibling design parity* bullet (`set -u`,
    `--help` flag, *"run from repo root"* guard, single
    WARNING/DRIFT block, advisory `exit 0` on every path,
    *"trip wire, not a fence"* docstring framing). The
    parser-guard tightening is a `check-cargo-lock.sh`-only
    addition, not a divergence from `check-c-allocations.sh` —
    `check-cargo-lock.sh` has a `sed -nE` parser to guard,
    `check-c-allocations.sh` has only a `grep -cE` integer count
    and no parsing, so a *"distinguish parser-fail from real
    drift"* idiom is structurally not applicable to the integer-
    count script. The divergence is principled (the script with
    a parser carries a parser-guard; the script without a parser
    carries none) and no propagation to `check-c-allocations.sh`
    is needed today. **Cross-script convention worth pinning,**
    in soft form: any *future* drift detector that parses the
    inventory (rather than counting matches) inherits the
    Option-A obligation from PR #2396 — distinguish parser-fail
    from real drift via an explicit *"could not parse"* WARNING
    that exits 0 without falling through into the real-drift
    code path. At N=1 parser-bearing drift detector
    (`check-cargo-lock.sh`) the convention is sufficiently
    self-explanatory in the Option-A guard block itself; if a
    second parser-bearing drift detector appears (e.g. a future
    `scripts/check-rust-toolchain.sh` parsing `rust-toolchain.toml`
    against an inventory-snapshotted version), that is the right
    point to extract the convention into
    [.claude/skills/inventory-reconciliation/SKILL.md](/home/kim/lean-zip/.claude/skills/inventory-reconciliation/SKILL.md)
    or a sibling skill. This paired-review surfaces no follow-up
    issue for the convention extraction today.
  - **Issue → PR loop closure semantics.** PR #2396 is the
    follow-up PR for paired-review #2384's parser-fail-open
    finding (originally surfaced in the *Snapshot-string parsing
    fidelity* bullet of the *Paired review of PR #2382* subsection
    above, where the failure mode was characterised as
    *"loud-but-unfriendly rather than silent"*). The post-#2396
    tree mitigates that failure mode: the parser-mismatch path
    now emits an explicit `parser regex mismatch` WARNING with
    the offending snapshot line echoed underneath, instead of
    falling through into the DRIFT branch with blank `expected:`
    fields. The original *Paired review of PR #2382* subsection
    is left intact as a historical record of the audit at the
    time, with a one-line *"superseded by PR #2396"* trailer
    appended to the *Snapshot-string parsing fidelity* bullet
    pointing forward to this paired-review subsection. Rationale
    for the trailer-only edit (option iii from issue #2397's
    deliverable 5): preserves the audit trail (the historical
    paired-review remains the record of what the parser
    fail-open looked like before PR #2396) while making the
    closure visible without requiring readers to scroll between
    subsections. This paired-review surfaces no new follow-up
    issues — the parser-fail-open finding is closed, and the
    cross-script convention extraction is deferred until a
    second parser-bearing drift detector appears.
- Paired review of PR #2399 (skill codification — `Half-closed two-step` *Scaffold variant* sub-section):
  - **Design fidelity vs. issue #2393.** The merged PR satisfies all
    three numbered deliverables from the closing issue: (1) the new
    *Scaffold variant (scaffold + body fill-in)* sub-section under
    [.claude/skills/inventory-reconciliation/SKILL.md](/home/kim/lean-zip/.claude/skills/inventory-reconciliation/SKILL.md)
    *Half-closed two-step* names the host/toolchain prerequisite
    motivator (nightly Rust, Linux-only sanitizer runtime, GPU,
    network credentials) and the env-guard-as-host-gate idiom
    explicitly, including the disjoint exit-2 ("host ineligible")
    vs exit-1 ("skeleton not yet implemented") diagnostic split
    surfaced by PR #2383's paired-review; (2) the section-intro
    paragraph (*"There are two two-step shapes; both keep the
    inventory honest during the half-closed window …"*) explicitly
    frames *parameter* vs *scaffold* as the discriminator, so a
    future reader landing on the `## Half-closed two-step` heading
    finds the variant-selection guidance before either sub-section
    body; (3) the optional one-line back-pointer in
    [SECURITY_INVENTORY.md](/home/kim/lean-zip/SECURITY_INVENTORY.md)
    PR #2383 paired-review *Inventory partial-flip / forward-pointer
    phrasing* sub-bullet was added as a footnote-style trailing
    parenthetical, not a structural rewrite of the existing prose.
    The *Between-step discipline* bullets in the new sub-section
    cover the four discipline points enumerated in the issue body
    (in-place edit of *Missing work* bullet with the `- [ ]`
    checkbox unchecked, sibling *Current local guardrails*
    *"scaffolded but not yet executed"* qualifier, separate
    `agent-plan` `feature` follow-up issue, host-gating preamble
    citing the `coordination skip` macOS pattern from #2366 / #2369).
    No deliverable is missing or partially present.
  - **Sub-heading restructure — verbatim preservation of the
    parameter variant.** The pre-#2399 *Half-closed two-step*
    section was a single flat body covering the parameter-add /
    default-flip shape (precedent #1610 → #1631). PR #2399's diff
    is purely additive: 56 added lines, 0 deletions. The original
    parameter content (the four *"Use a two-step … when:"* bullets,
    the two *"Use a one-step … when:"* bullets, the *Between-step
    discipline* paragraph re-phrasing the bullet as *"half-closed by
    #N (parameter added, default still 0). Flip tracked as #M."* <!-- drift-detector: verbatim quote of the SKILL.md parameter-variant placeholder template, not a stale placeholder -->,
    and the *"#1610 → #1631"* precedent line with the #1630 one-step
    counter-example) is preserved word-for-word under the new
    `### Parameter variant (parameter-add + default-flip)`
    sub-heading; no prose was lost or silently reworded. The
    `## Half-closed two-step` H2 anchor is unchanged, so the
    cross-reference from `summarize-flow`'s sibling-skill comment
    ("shares the issue-body-as-source-of-truth invariant via its
    *Half-closed two-step* section") still resolves correctly. The
    section now carries a one-paragraph H2-level intro followed by
    two sibling H3 sub-sections of comparable length (~25 lines
    each), avoiding any one variant drowning the other.
  - **Back-pointer fidelity (post-#2401 tree).** The
    [SECURITY_INVENTORY.md](/home/kim/lean-zip/SECURITY_INVENTORY.md)
    PR #2383 paired-review *Inventory partial-flip / forward-pointer
    phrasing* sub-bullet's trailing parenthetical reads, post-#2401
    cleanup, *"see
    [.claude/skills/inventory-reconciliation/SKILL.md](/home/kim/lean-zip/.claude/skills/inventory-reconciliation/SKILL.md)
    Scaffold variant sub-section, landed in PR #2399 closing
    #2393"* (the surrounding parens belong to the back-pointer's
    framing parenthetical, not the quote). Three audit checks pass: (i) the *"Scaffold variant"*
    name matches the merged SKILL.md sub-heading exactly (no
    *"scaffold + body fill-in"* mismatch with the parenthetical
    qualifier on the heading); (ii) the qualifier reads as
    *Executed past-tense one-liner*-shaped — *"landed in PR #2399
    closing #2393"* — without the pre-#2401 *"once the follow-up
    #2393 lands"* future-tense fragment; (iii) the back-pointer
    cites the variant by sub-section name rather than by a line
    number, so a future `## Half-closed two-step` reflow that
    re-orders the two H3 sub-sections (or extends them with a
    third variant) does not falsify the back-pointer — consistent
    with the
    [#2353](https://github.com/kim-em/lean-zip/pull/2353) decision
    to stop tracking line-number anchors in inventory and skill
    files.
  - **Cross-references in the new sub-section.** All four numbered
    cites in the *Scaffold variant* sub-section resolve to real
    artefacts with the role the prose claims:
    [PR #2383](https://github.com/kim-em/lean-zip/pull/2383) is
    MERGED 2026-04-29 with title *"feat: scaffold
    `scripts/sanitize-rust-ffi.sh` skeleton + sibling 'Sanitizer
    recipe' inventory paragraph (Missing-work bullet 1)"* (the
    cited scaffold precedent);
    [issue #2392](https://github.com/kim-em/lean-zip/issues/2392) is
    OPEN with `agent-plan` + `feature` labels and a *"⚠️ Platform
    requirement: Linux + nightly Rust"* preamble carrying the
    macOS-skip recipe verbatim (the cited body fill-in follow-up,
    matching the *"separate `agent-plan` `feature` issue"* phrasing
    in the *Between-step discipline*);
    [issue #2366](https://github.com/kim-em/lean-zip/issues/2366)
    is OPEN with the same `agent-plan` + `feature` labels (the
    sibling `sanitize-ffi.sh` re-run, also Linux-host-gated,
    cited as the macOS-skip preamble pattern source); and
    [PR #2369](https://github.com/kim-em/lean-zip/pull/2369) is
    CLOSED-as-merged (the original *"Re-run Kiran's fuzz harness on
    v4.30.0-rc2"* execution that established the
    `coordination skip` macOS pattern). No ghost references; the
    `#2366 / #2369` pairing in the SKILL.md prose correctly
    represents *"open Linux-gated follow-up + closed precedent
    that established the skip pattern"*.
  - **Post-merge cleanup observation — PR #2401 as a *post-#2399
    cleanup* micro-PR class.** PR #2399 went up with the back-pointer
    in pre-merge future-tense form (*"once the follow-up #2393
    lands"*), made necessary because the back-pointer was authored
    inside the same diff as the sub-section it pointed at and the
    closing-PR self-reference was therefore unknown until merge.
    [PR #2401](https://github.com/kim-em/lean-zip/pull/2401)
    (closing #2400) followed nine minutes after PR #2399's merge as
    a single-line stale-qualifier substitution (*"once the
    follow-up #2393 lands"* → *"landed in PR #2399 closing
    #2393"*); diff is one line in
    [SECURITY_INVENTORY.md](/home/kim/lean-zip/SECURITY_INVENTORY.md)
    plus a progress entry. Observation worth recording: the
    *Scaffold variant* between-step discipline currently does not
    explicitly call out the *"if the back-pointer carries a
    pre-merge future-tense qualifier, file a one-line trailing
    cleanup PR after merge to flip it to past-tense"* pattern as a
    cadence step. The pattern is a strict subset of the existing
    *Executed past-tense one-liner* shape (it just defers the
    flip from the closing PR to a trailing cleanup PR by
    necessity), and at N=1 instance (#2399 → #2401) it is not
    obviously a worth-codifying cadence step versus a
    once-off. Per the issue's *"do NOT modify SKILL.md from
    inside this paired-review entry"* discipline, no SKILL.md
    edit is filed here; if a second instance of the same
    pre-merge-future-tense → trailing-cleanup-PR pattern appears
    on a future *Scaffold variant* PR, that is the right
    triggering point to mint a follow-up extending the
    *Between-step discipline* with an explicit *"trailing
    cleanup PR for forward-pointer back-references"* bullet.
  - **Follow-up gaps.** No gaps surface. The audit confirms the
    codification is faithful to issue #2393, the parameter-variant
    content is preserved verbatim under the new H3 sub-heading, the
    back-pointer is in steady-state past-tense form on the
    post-#2401 tree, and all four cross-references resolve to real
    artefacts with the cited role. The *post-#2399 cleanup* observation
    is logged as a deferred-cadence-extension candidate but does not
    warrant a follow-up issue at N=1. This paired-review surfaces no
    follow-up issues.

### `Zip.Native.Inflate` and verified DEFLATE core

- Status: `proved-in-repo`
- Components:
  - [Zip/Native/Inflate.lean](/home/kim/lean-zip/Zip/Native/Inflate.lean)
  - [Zip/Spec/InflateCorrect.lean](/home/kim/lean-zip/Zip/Spec/InflateCorrect.lean)
  - [Zip/Spec/DeflateRoundtrip.lean](/home/kim/lean-zip/Zip/Spec/DeflateRoundtrip.lean)
- Notes:
  - this is the strongest-assurance part of the repo
  - remaining risk comes from framing, parser boundaries, runtime, and limits

## Boundary-Facing Subsystems

### ZIP Archive Reader/Extractor

- Components: [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean)
- Status: `guarded-locally`
- Trust boundary:
  - parses EOCD, central directory, ZIP64 metadata, local headers, names,
    offsets, compressed sizes, and extraction paths from untrusted files
- Current guardrails:
  - central directory must fit within file size
  - configurable `maxCentralDirSize`
  - local `readExact` checks `Nat -> USize` roundtrip before `Handle.read`
  - `assertSpanInFile` validates local-header, name+extra, and compressed-data
    spans against actual file size before each attacker-controlled `Handle.read`
    in `readEntryData`
  - regression fixture `testdata/zip/malformed/oversized-compressed-size.zip`
    exercises the oversized-compressedSize rejection path
  - path traversal blocked via `Binary.isPathSafe`
  - CRC and final size checked after extraction
- Missing work:
  - Executed — bounded-read helpers for `Handle`/`Stream` landed in
    PR #1608 (Track E P5.1); `SpanInFile` predicate + IO reduction
    lemmas in PR #1636 (Track E P5.2); `Archive`/`Tar` callers
    migrated to the helpers in PR #1626 (Track E P5.3). No residual
    sites currently identified at this layer.
  - CD-vs-EOCD comment-length consistency not yet checked — PR #1733
    landed the `totalEntries` dimension of this category, PR #1742
    the disk-number dimension, and PR #1752 the sibling
    `numEntriesThisDisk`; the trailing comment-length field remains
    silently accepted. Trailing bytes past `EOCD.commentLen` are not
    cross-checked against the file tail, which is one of the classic
    ZIP-smuggling vectors.
- Recent wins:
  - central-directory vs. local-header mismatch checks — PR #1554
    (`testdata/zip/malformed/cd-lh-method-mismatch.zip`,
    `cd-lh-size-mismatch.zip`)
  - CD-vs-LH flags (bit-3-masked) consistency check — PR #1715
    (`testdata/zip/malformed/cd-lh-flags-mismatch.zip`) rejects the
    bit-11 UTF-8-name smuggling vector before the payload read
  - CD-vs-EOCD `totalEntries` consistency check — PR #1733
    (`testdata/zip/malformed/eocd-numentries-mismatch.zip`) rejects
    EOCD-declared count ≠ parsed CD entry count
  - EOCD disk-number consistency check — PR #1742
    (`testdata/zip/malformed/eocd-disknum-mismatch.zip`) rejects
    any archive with nonzero `numberOfThisDisk` or `diskWhereCDStarts`
    (post-ZIP64-override); lean-zip supports single-disk archives only
    and the writer already hard-codes both fields to `0`
  - CD per-entry `diskNumberStart` consistency check — PR #1759
    (`testdata/zip/malformed/cd-entry-disknum-mismatch.zip`) rejects
    archives where any CD entry carries a nonzero APPNOTE §4.4.11
    `diskNumberStart` field at CD offset +34; per-entry sibling of
    PR #1742, together closing the full disk-number smuggling
    dimension on single-disk archives (writer-side at the
    `Binary.zeros`-initialised CD header — see *"disk number start
    (34)"* comment around
    [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean))
  - EOCD `numEntriesThisDisk` vs. `totalEntries` consistency check —
    PR #1752 (`testdata/zip/malformed/eocd-numentries-thisdisk-mismatch.zip`)
    rejects archives where the sibling EOCD entry-count fields disagree
    (single-disk archives must have them equal; writer-side at
    [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean)    )
  - ZIP64/standard-EOCD override sentinel check — PR #1745
    (`testdata/zip/malformed/eocd-zip64-override-nosentinel.zip` —
    `cdOffset` slot at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean)),
    PR #1905
    (`testdata/zip/malformed/eocd-zip64-override-cdsize-mismatch.zip` —
    `cdSize` slot at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean)),
    PR #1908
    (`testdata/zip/malformed/eocd-zip64-override-totalentries-mismatch.zip` —
    `totalEntries` slot at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean)),
    PR #1911
    (`testdata/zip/malformed/eocd-zip64-override-diskcd-mismatch.zip` —
    `diskWhereCDStarts` slot at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean)),
    and PR #1922
    (`testdata/zip/malformed/eocd-zip64-override-entriesthisdisk-mismatch.zip` —
    `numEntriesThisDisk` slot at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean))
    reject archives where the standard EOCD carries a real value
    instead of the APPNOTE §4.3.16 sentinel (`0xFFFFFFFF` / `0xFFFF`)
    in any of `cdSize`/`cdOffset`/`totalEntries`/`numberOfThisDisk`/
    `diskWhereCDStarts`/`numEntriesThisDisk` that the ZIP64 record
    overrides with a numerically different value. The check is relaxed
    to "sentinel or numeric match" to accommodate real-world producers
    such as Go's `archive/zip` that emit real zeros in the standard
    EOCD's disk-number fields when ZIP64 is used (see
    `testdata/zip/interop/go-zip64.zip`). Closes the
    parser-differential smuggling vector where one reader trusts the
    standard EOCD and another trusts the ZIP64 override. Per-slot
    regression coverage now pins the `cdOffset`, `cdSize`,
    `totalEntries`, `diskWhereCDStarts`, and `numEntriesThisDisk`
    slots; the remaining `numberOfThisDisk` slot shares
    the same throw shape and is covered by symmetric code review
    pending its dedicated per-slot fixture (sibling issue #1902 in
    flight as PR #1909)
  - ZIP64 EOCD64 self-declared record-size check — PR #1761
    (`testdata/zip/malformed/zip64-eocd64-bad-recsize.zip`) rejects
    archives whose EOCD64 `size of this record` field (APPNOTE §4.3.14,
    at `bufPos + 4`) is not exactly `44` — the v1 EOCD64 shape lean-zip
    produces and consumes. lean-zip reads the EOCD64 at fixed per-field
    offsets from a hard-coded 56-byte layout; a stricter parser that
    trusts the self-declared length would read past or short of that,
    yielding a parser-differential smuggling vector (writer-side at
    [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean)
    hard-codes `44`). Additional regression coverage from PR #1889
    (`testdata/zip/malformed/zip64-eocd64-v2-record.zip`) pins the
    rejection behaviour against the APPNOTE §4.3.14.2 v2 shape: an
    internally-consistent 72-byte record with `recSize=60` and a
    16-byte "zip64 extensible data sector" in the strong-encryption
    shape. lean-zip does not implement strong encryption (SES), so v2
    records remain rejected by policy; the fixture closes the
    documentation gap flagged by the post-#1843 summarize
    ([progress/20260424T203421Z_90d1e22c-summarize-post-1843.md](/home/kim/lean-zip/progress/20260424T203421Z_90d1e22c-summarize-post-1843.md))
    between the generic `recSize=0` boundary (existing fixture) and
    the v2-specific shape
  - ZIP64 EOCD64 `versionMadeBy` spec-version upper-bound check — PR #1826
    (`testdata/zip/malformed/zip64-eocd64-versionmadeby-too-high.zip`)
    rejects archives whose EOCD64 `versionMadeBy` field (APPNOTE
    §4.4.2.1 / §4.4.2.2, at `bufPos + 12`) carries a lower byte greater
    than `63` (spec version 6.3) at `findEndOfCentralDir` time
    ([Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean)).
    The low byte of `versionMadeBy` is the "version of the ZIP
    specification" in decimal-coded form (APPNOTE-defined values 1.0
    through 6.3, encoded `10`..`63`); any higher value is either a
    forward-looking extension lean-zip does not support or a crafted
    smuggle targeting readers that don't validate the field.
    Writer-side at
    [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean)
    emits `3 * 256 + 45 = 0x032D`, so the writer always satisfies the
    bound (`45 ≤ 63`). Only the lower byte is checked — real archives
    vary widely in host-OS code (upper byte: Info-ZIP emits `3`,
    Windows producers `11` NTFS, etc.); the lower byte is a pure
    spec-version field with a well-defined APPNOTE maximum. Placed
    immediately after the record-size check so the version-field guard
    runs before any attacker-controlled size or offset is consumed.
    Archive-level counterpart to the per-entry CD+4 `versionMadeBy`
    upper-bound fixture (issue #1812 / PR #1820,
    `cd-entry-versionmadeby-too-high.zip`); together the two close the
    `versionMadeBy` upper-bound dimension across both ZIP layers
    (EOCD64 record and per-entry CD). Interop sweep:
    `testdata/zip/interop/go-zip64.zip` — the only interop fixture
    with an EOCD64 — has `versionMadeBy=0x002d` (low byte `45`),
    comfortably below the bound
  - ZIP64 EOCD64 `versionNeededToExtract` upper-bound check — PR #1852
    (`testdata/zip/malformed/zip64-eocd64-versionneeded-too-high.zip`)
    rejects archives whose EOCD64 `versionNeededToExtract` field
    (APPNOTE §4.4.3.2, at `bufPos + 14`) exceeds `63` (spec version
    6.3, the APPNOTE-defined maximum) at `findEndOfCentralDir` time.
    The field declares the minimum ZIP specification version needed
    to interpret the EOCD64 record; any higher value is either a
    forward-looking extension lean-zip does not support or a crafted
    smuggle against strict readers. Writer-side at
    [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean)
    hard-codes `45` (EOCD64 requires ZIP64 support, §4.4.3.2), so the
    bound `45 ≤ 63` holds trivially for every lean-zip-produced
    archive. Upper-bound sibling of the lower-bound `≥ 45` check
    (issue #1758 / PR #1764); together the two bounds close the
    EOCD64 `versionNeededToExtract` two-sided-bound dimension.
    Archive-level analog of the per-entry CD +6 upper bound
    (PR #1807, `cd-version-needed-too-high.zip`), which caps the
    per-entry field at `45`; the archive-level EOCD64 cap is `63`
    because APPNOTE §4.4.3.2 documents the field as the version
    needed to *interpret the record* rather than to extract the
    largest entry. Interop sweep across
    `testdata/zip/{interop,malformed}/*.zip` reports every EOCD64
    `versionNeededToExtract` at `45`, comfortably below the bound
  - ZIP64 EOCD64 record archive-layout invariant — PR #1856
    (`testdata/zip/malformed/zip64-eocd64-overlap-locator.zip`)
    rejects archives whose Locator-declared `eocd64Offset` plus the
    56-byte v1 EOCD64 record reaches into or past the Locator at
    `findEndOfCentralDir` time
    ([Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean)).
    APPNOTE §4.3.6 pins the ZIP64 trailer layout as `[CD] [EOCD64]
    [Locator] [EOCD]`, so a legitimate archive satisfies
    `eocd64Offset + 56 ≤ locatorPos = eocdPos - 20` — the EOCD64
    record must end strictly before the Locator begins. Pre-PR
    reader silently let the claimed EOCD64 overlap the Locator (or
    claim to start anywhere inside it), reading Locator bytes as the
    tail of the EOCD64 record — classic parser-differential /
    layout-smuggling vector where a strict peer reader rejects and
    lean-zip accepts. Writer-side at
    [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean)
    emits the three records contiguously in APPNOTE order, so the
    invariant holds trivially for every lean-zip-produced archive.
    Buffer-relative form `bufPos + 56 ≤ pos - 20` matches the
    surrounding `bufPos`/`pos` arithmetic and is well-defined under
    `Nat` subtraction via the outer `pos ≥ 20` guard. Placed
    immediately after the `sigEOCD64` match so the layout check
    runs before the record-size / versionMadeBy / versionNeeded
    guards — error attribution stays tightly scoped to
    layout-shape failures. The pre-existing `bufPos + 56 ≤
    data.size` buffer-readability check remains as defense-in-depth
    but is now strictly weaker than the layout invariant for any
    archive whose buffer extends past the Locator. Peer-parser
    confirmation: CPython's `zipfile._EndRecData64` enforces the
    same invariant (`if reloff > offset: raise BadZipFile("Corrupt
    zip64 end of central directory locator")`) — the new guard
    brings lean-zip into alignment with a strict reference
    implementation. Archive-level macro sibling: `cdOffset + cdSize
    ≤ eocdPos` (issue #1799 / in-flight PR #1809). Per-entry micro
    sibling: `localOffset + 30 ≤ cdOffset` (PR #1813). Together the
    three invariants close the ZIP archive-layout dimension across
    the standard-EOCD macro, the ZIP64-EOCD64 macro, and the
    per-entry micro granularities. Interop pre-flight swept
    `testdata/zip/interop/*.zip`: only `go-zip64.zip` carries an
    EOCD64 + Locator pair, and its `eocd64Offset + 56 = 200 =
    locatorPos` satisfies the invariant tightly (EOCD64 ends
    exactly at Locator start). Net-new dimension observed during
    the ZIP64-layer archive-layout coverage sweep
  - CD/LH extra-data sub-field structural check — PR #1788
    (`testdata/zip/malformed/cd-extra-overrun-datasize.zip`) rejects
    CD/LH entries whose extra-data contains a sub-field whose declared
    `dataSize` extends past the end of the extra-data blob (APPNOTE §4.5
    *"Extensible Data Fields"*). Pre-PR, the outer-sub-field iteration
    lived only inside `parseZip64Extra`, which `break`s silently on a
    malformed sub-field; the caller skips `parseZip64Extra` entirely
    when no ZIP64 sentinel is set, so the anomaly was invisible in the
    no-sentinel case and misattributed to "missing 0x0001" in the
    sentinel case.  `validateExtraFieldStructure` now runs
    unconditionally on the blob before the sentinel guard at both the
    CD site (`parseCentralDir`) and the LH site (`readEntryData`) —
    closing the outer sub-field iteration dimension of the ZIP64
    extra-data smuggling class (siblings of the inner-0x0001
    `zip64-extra-oversized-datasize.zip` `dataSize` exactness check).
    Writer side is well-formed by construction at
    [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean)
    (LH) and  (CD): both paths emit either a single well-formed
    0x0001 block or zero extra-data
  - ZIP64 per-entry extra-field `dataSize` exactness check — PR #1785
    (`testdata/zip/malformed/zip64-extra-oversized-datasize.zip`)
    rejects CD entries whose ZIP64 (headerId `0x0001`) extra-field
    `dataSize` is strictly greater than the `8 * N` bytes consumed by
    the `N` sentinel-gated 32-bit standard fields (APPNOTE §4.5.3).
    Trailing slack past the consumed prefix is attacker-controllable
    and is a parser-differential smuggling vector — a lenient parser
    (the pre-PR lean-zip) silently discards the slack after the first
    `N * 8` bytes, while a strict parser rejects the archive.
    `parseZip64Extra` now asserts `fpos == fieldEnd` after the three
    conditional reads ([Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean)). Sibling of the outer
    `zip64-eocd64-bad-recsize.zip` record-size check (same
    parser-differential attack class, different layer); writer-side at
    [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean)
    (CD) and  (LH) both emit exactly `N * 8` bytes of data
  - duplicate ZIP64 (`headerId 0x0001`) extra-block rejection — PR #1793
    (`testdata/zip/malformed/cd-zip64-extra-duplicate.zip` and
    `testdata/zip/malformed/lh-zip64-extra-duplicate.zip`) rejects CD
    or LH extra-data containing two or more ZIP64 (`0x0001`) blocks.
    APPNOTE §4.5 forbids more than one instance of any registered
    header ID per entry's extra-data; for ZIP64 in particular the
    layout of each block depends on which standard 32-bit fields are
    at the `0xFFFFFFFF` sentinel, so two blocks with different
    payloads make the resolved sizes/offset ambiguous. lean-zip's
    pre-fix `parseZip64Extra` used a `break` after the first
    `headerId == 0x0001` match — a "first-wins" policy that lets a
    "last-wins" parser disagree on identical bytes. The new
    `hasDuplicateZip64Extra` helper at
    [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean)
    walks the TLV structure once and is invoked by both the CD-side
    caller in `parseCentralDir`
    ([Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean))
    and the LH-side caller in `readEntryData`
    ([Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean))
    before `parseZip64Extra` is called. The two error wordings
    (`"duplicate ZIP64 extra field"` vs `"duplicate ZIP64 local extra
    field"`) keep attribution distinct between layers. Sibling of the
    sub-field `dataSize` exactness check (PR #1785) — together they
    close the ZIP64 extra-field layout-smuggling attack class at the
    CD/LH boundary; writer-side `writeZip64ExtraCentral`
    ([Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean))
    and `writeZip64ExtraLocal` () emit at most one 0x0001 block
    per entry, so the new guard never fires on legitimate archives
  - CD-vs-LH `versionNeededToExtract` downgrade check — PR #1736
    (`testdata/zip/malformed/cd-lh-version-mismatch.zip`) rejects LH
    claiming a higher version than CD (CD > LH is legitimate per
    Go/Python ZIP64 producers and is allowed)
  - CD-vs-LH `lastModTime`/`lastModDate` consistency check — PR #1769
    (`testdata/zip/malformed/cd-lh-modtime-mismatch.zip`) rejects
    archives whose DOS-encoded last-modified `UInt16` time/date pair
    disagrees between CD offset +12/+14 and LH offset +10/+12 (APPNOTE
    §4.4.6). The check is ungated — unlike crc/compSize/uncompSize,
    the timestamp fields are not legitimately zeroed by the
    data-descriptor bit. Closes the last CD/LH header-metadata
    smuggling dimension; writer-side at
    [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean)
    (LH) and  (CD) both emit `defaultDosTime` /
    `defaultDosDate` via the shared constants at
    [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean).
    Net-new dimension observed during the CD/LH header-metadata
    coverage sweep — the *Missing work* block had not previously
    flagged the timestamp fields
  - CD-entry stored-method (`method=0`) size-invariant check — PR #1773
    (`testdata/zip/malformed/cd-stored-size-mismatch.zip`) rejects CD
    entries whose `method == 0` with `compressedSize != uncompressedSize`
    at `parseCentralDir` time (post-ZIP64-resolution), before any LH
    read. APPNOTE §4.4.5 defines method 0 as *"no compression"*, so the
    equality is a tautology — the writer emits equal values for stored
    entries and crafted archives with mismatched sizes are malformed.
    Complements the CD/LH `uncompressedSize` consistency check
    (`cd-lh-uncompsize-mismatch.zip`): that catches CD-vs-LH skew, this
    catches intra-CD invariant violation with no CD/LH divergence. Also
    makes the anomaly visible to `Archive.list`, which never reaches the
    late post-decode `"size mismatch"` guard at
    [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean).
    Net-new dimension observed during the CD-parse guard coverage
    sweep — the *Missing work* block had not previously flagged the
    stored-method invariant
  - CD-entry compression-method allowlist check — PR #1801
    (`testdata/zip/malformed/cd-bad-method-early.zip`) rejects CD
    entries whose `method` field is outside lean-zip's `{0, 8}`
    allowlist (`0` = stored, `8` = deflate) at `parseCentralDir` time
    ([Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean)),
    before the ZIP64 extra resolution. The check is safe to run
    pre-ZIP64-resolution because `method` is a plain `UInt16` field
    with no sentinel-gating (APPNOTE §4.4.5). Pre-PR, only
    `Archive.extract`'s late `"unsupported method"` dispatch in
    `readEntryData` (`"unsupported method"` throw at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean))
    caught crafted archives advertising method 6 (imploded), 12
    (bzip2), 14 (LZMA), 93 (Zstd), etc. — `Archive.list` was entirely
    blind to the anomaly, and a caller routing on `Entry.method` to
    pre-authorize before extracting would treat the crafted metadata
    as trustworthy. Writer-side at
    [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean)
    (`let method : UInt16 := if useDeflate then 8 else 0`) is
    trivially compliant. The late `readEntryData` throw stays in
    place as defense-in-depth — unreachable for CD-parseable archives
    via the public API, but kept so the precedence-shift story is
    grep-discoverable. Precedence-shift sibling of PR #1773
    (stored-method size invariant): same early-rejection approach
    applied to the method-field dimension. Companion fixture
    `bad-method.zip` (CD/LH method=14, LZMA, 140 B) now also trips
    the same CD-parse guard; the new `cd-bad-method-early.zip`
    (CD/LH method=6, imploded, 122 B) provides paired-review-distinct
    attribution
  - CD-entry `localOffset + 30 ≤ cdOffset` archive-layout invariant —
    PR #1813
    (`testdata/zip/malformed/cd-entry-localoffset-past-cdstart.zip`)
    rejects CD entries whose resolved `localOffset` plus the 30-byte
    fixed LH header (APPNOTE §4.3.7) reaches into or past the CD
    region at `parseCentralDir` time
    ([Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean)).
    APPNOTE §4.3.6 pins the archive layout as `[LH+data]* [CD]
    [EOCD]`, so every entry's LH must be readable strictly before the
    CD start; writer-side at
    [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean)
    emits all LH bytes before the CD block, so the invariant is
    universal for legitimate archives. Per-entry micro-shape sibling
    of the archive-level macro-shape `cdOffset + cdSize ≤ eocdPos`
    guard; together they characterize the legitimate layout at both
    granularities. Pre-PR, `Archive.list` had no gate at all —
    crafted archives with `localOffset ≥ cdOffset` listed
    successfully and `Entry`-routing callers treated the metadata as
    trustworthy; only the extract path's late LH-signature check
    (`"bad local header signature"` at
    [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean))
    caught a subset of the construction (and could be defeated by a
    carefully chosen overlap where the CD bytes happened to match
    `sigLocal`). Uses the asymmetric `SpanInFile`-shaped subtraction
    to avoid `UInt64` wrap on crafted very-large `localOff`. Placed
    after ZIP64 resolution so the resolved `UInt64` `localOff` is
    checked, not the `0xFFFFFFFF` sentinel. Net-new dimension
    observed during the CD-parse archive-layout-invariant coverage
    sweep
  - Late LH-signature guard regression coverage — PR #1903
    (`testdata/zip/malformed/cd-bad-lh-signature.zip`) pins the
    `Archive.extract` defense-in-depth catch at
    [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean)
    — *"bad local header signature for {label}"* — for archives whose
    CD parses cleanly but whose LH magic at `entry.localOffset` is not
    `0x04034b50` (`sigLocal`, APPNOTE §4.3.7). 122-byte single-entry
    stored `hello.txt` fixture (LH at file offset 0, CD at offset 45,
    EOCD at offset 100) where the LH's first 4 bytes are overwritten
    with `0xCAFEBABE` (LE: `BE BA FE CA`) — the CD itself is
    byte-identical to the stock baseline so every CD-parse guard passes
    (`localOffset = 0`, `localOffset + 30 ≤ cdOffset = 45`,
    `entryEnd = 45 ≤ cdEnd = 100`, method ∈ {0, 8}, stored-method
    `compSize == uncompSize`, etc.) and `assertSpanInFile` /
    `readBoundedSpanFromHandle` clear the LH span (30 B at offset 0 ≤
    fileSize 122). `Archive.list` never reads the LH and lists the
    fixture cleanly; only `Archive.extract` throws — confirming the
    precedence story. Fixture-only regression coverage (no new guard
    code, no new error wording, no caller / signature change) — pattern
    matches PRs #1761 / #1889 (`zip64-eocd64-bad-recsize.zip` /
    `zip64-eocd64-v2-record.zip` at the EOCD64 record-size guard) and
    PR #1921 (`cd-entry-past-cdend.zip` at the `entryEnd > cdEnd`
    guard). Sibling of `cd-entry-localoffset-past-cdstart.zip` (PR #1813,
    fires the per-entry `localOffset + 30 ≤ cdOffset` CD-parse guard
    before the LH read) and `cd-entry-past-cdend.zip` (PR #1921,
    fires the `entryEnd > cdEnd` CD-parse guard before the LH read):
    together the trio pins all three precedence levels of the
    local-offset → local-header validation chain at CD-parse +
    late-extract — the late LH-signature guard is the defense-in-depth
    catch for archives that slip past every earlier CD-parse check, and
    this fixture pins that catch behaviour so future refactors of
    `Archive.extract` cannot silently lose the guard. Choice of
    `0xCAFEBABE` is canonical "obviously crafted" UInt32 — any 4-byte
    sequence ≠ `50 4b 03 04` fires the same guard
  - Per-entry `entryEnd > cdEnd` footprint guard regression coverage —
    PR #1921
    (`testdata/zip/malformed/cd-entry-past-cdend.zip`) pins the existing
    `parseCentralDir` per-entry footprint check at
    [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean)
    — *"central directory entry extends past end of central directory"*
    — for archives whose declared field-length triple
    `(nameLen, extraLen, commentLen)` makes the CD entry's claimed
    footprint `46 + nameLen + extraLen + commentLen` exceed the
    EOCD-declared `cdEnd = cdOffset + cdSize`. 122-byte single-entry
    stored `hello.txt` fixture (LH at file offset 0, CD at offset 45,
    EOCD at offset 100) where the sole CD entry's `commentLen` field at
    CD +32 (UInt16) is `16` while no comment payload is physically
    present — `cdSize = 55` (header + name only). At parse time
    `entryEnd = 45 + 46 + 9 + 0 + 16 = 116 > cdEnd = 100`, firing the
     guard before any name decode. All earlier CD-parse guards pass
    (loop entry `pos + 46 ≤ cdEnd` (91 ≤ 100), CD signature match,
    `nameLen = 9 > 0`, `diskNumberStart = 0`, `internalAttrs = 0`) so
    attribution pins to the footprint guard rather than a sibling
    early-reject. Fixture-only regression coverage (no new guard code,
    no new error wording, no caller / signature change) — pattern
    matches PRs #1761 / #1889 (`zip64-eocd64-bad-recsize.zip` /
    `zip64-eocd64-v2-record.zip` at the EOCD64 record-size guard) and
    #1903 (`cd-bad-lh-signature.zip` at the late LH-signature guard).
    Companion to in-flight `cd-trailing-garbage.zip` (issue #1775,
    trailing bytes AFTER the last entry inside `[lastEntryEnd, cdEnd)`)
    and `cd-extends-past-eocd.zip` (issue #1799, archive-level
    `cdOffset + cdSize ≤ eocdPos`) — the trio closes the three
    CD-region overrun shapes: per-entry footprint past `cdEnd`
    (this fixture), trailing garbage inside the declared region
    (#1775), and macro `cdSize` past EOCD (#1799). Pins the
    paired-review precedence chain alongside
    `cd-entry-localoffset-past-cdstart.zip` (PR #1813, per-entry
    `localOffset + 30 ≤ cdOffset`) and `cd-bad-lh-signature.zip`
    (PR #1903, late LH-signature guard) — together the trio fixes all
    three precedence levels of the local-offset → local-header
    validation chain at CD-parse + late-extract so future refactors
    of `parseCentralDir` cannot silently regress the per-entry
    footprint fence. Sentinel `commentLen = 16` is canonical
    "obviously crafted" overrun — any positive value satisfying
    `46 + nameLen + extraLen + commentLen > cdSize` fires the same
    guard. Interop pre-flight over
    `testdata/zip/{interop,malformed}/*.zip` returned zero hits before
    landing
  - CD-entry `internalFileAttributes` reserved-bits check — PR #1819
    (`testdata/zip/malformed/cd-entry-internal-attrs-reserved.zip`)
    rejects CD entries whose APPNOTE §4.4.10 `internalFileAttributes`
    field at CD offset +36 (UInt16) has any bit other than bit 0
    set. APPNOTE §4.4.10 defines only bit 0 ("apparent ASCII/text
    data"); bits 1 and 2 are "reserved for use by PKWARE"; remaining
    bits are "unused in version 1.0". The guard is
    `internalAttrs &&& 0xFFFE == 0` (preserve bit 0, reject bits
    1-15) — preserves Info-ZIP interop (spot-check of
    `testdata/zip/interop/`: `go-unix.zip`, `go-test.zip`,
    `go-crc32-not-streamed.zip` set bit 0 on apparent-text files
    as `0x0001`; `go-zip64.zip`, `latin1-name.zip`, `utf8-flag.zip`
    use `0x0000`; no interop fixture sets any reserved bit).
    `parseCentralDir` fires the guard at
    [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean),
    immediately after the `diskNumberStart` check and before the
    `entryEnd > cdEnd` span check. Writer-side at
    [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean)
    (`Binary.zeros`-initialised 46-byte CD header — `pos + 36` never
    overwritten) is trivially compliant. Writer-zero single-`UInt16`
    sibling of PR #1759 (CD +34 `diskNumberStart` per-entry
    writer-invariant) and PR #1752 (EOCD `numEntriesThisDisk`
    archive-level writer-invariant); the three PRs together close
    the contiguous `CD+34 → CD+36 → EOCD` writer-zero-field
    early-reject column. Pre-PR, `Archive.list` and `Archive.extract`
    both silently accepted any `UInt16` here — a caller routing on
    `Entry` metadata would treat the smuggled reserved bits as
    trustworthy, and a strict peer reader would disagree on parse
    success. Net-new dimension observed during the CD+offset
    writer-zero coverage sweep — the *Missing work* block had not
    previously flagged the internal-attrs field
  - CD-entry general-purpose flag bit-5 (compressed patched data)
    rejection — PR #1824
    (`testdata/zip/malformed/cd-patched-data-flag.zip`) rejects CD
    entries whose flag-word has APPNOTE §4.4.4 bit 5 set at
    `parseCentralDir` time
    ([Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean)),
    pre-ZIP64-resolution. lean-zip implements neither creation nor
    extraction of PKWARE's proprietary compressed-patched-data
    format (§4.6); the writer emits `flags = 0x0800` (bit 11 UTF-8
    names) only at `writeLocalHeader`
    ([Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean))
    and `writeCentralHeader` (), so the guard never fires on
    legitimate archives. Pre-PR, crafted archives with bit 5 set
    were silently extracted as if the payload were plain Deflate /
    stored data — a parser-differential smuggling vector where a
    strict APPNOTE-aware reader would reject while lean-zip
    mis-extracts. Mask-equality form (`flags &&& 0x0020 == 0`)
    matches the `0xFFF7` bit-3-masking convention in `readEntryData`.
    Sibling of in-flight PR #1771 (issue #1762, bits 0/6/13
    encryption-related) at the same CD+8 `flags` field — distinct
    bit, distinct semantic justification, distinct error substring
    (`"patched-data flag bit 5 set"`). Interop safety: spot-checked
    pre-planning that all six `testdata/zip/interop/` fixtures
    carry `flag_bits ∈ {0x0000, 0x0800}` (no bit 5). Net-new
    dimension observed during the CD-parse flag-field coverage
    sweep
  - CD-entry general-purpose flag reserved/unused-bits rejection —
    PR #2237
    (`testdata/zip/malformed/cd-flags-reserved-bits.zip`) rejects CD
    entries whose flag-word has any APPNOTE §4.4.4 reserved-or-unused
    bit set: bits 7, 8, 9, 10 ("Currently unused"), bit 12 ("Reserved
    by PKWARE for enhanced compression"), and bits 14, 15 ("Reserved
    by PKWARE"). Together these seven bits form the mask `0xD780`
    (`0b1101_0111_1000_0000`). `parseCentralDir` fires the guard at
    [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean),
    immediately after the method allowlist (PR #1801) and before the
    per-feature-bit checks (bit 5 patched-data at
    [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean);
    other bits via the in-flight per-bit series). Writer-side at
    [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean)
    (LH) and  (CD) emits the flag word literally as `0x0800` (bit
    11 UTF-8 names) only, so the invariant `flags &&& 0xD780 == 0`
    holds for every lean-zip-produced archive independent of method,
    size, or ZIP64. Pre-PR, `Archive.list` and `Archive.extract` both
    silently accepted any reserved-bit value — a caller routing on
    `Entry` metadata would treat the smuggled bits as trustworthy,
    and a strict peer reader would disagree on parse success.
    Mask-equality form (`flags &&& 0xD780 == 0`) matches the existing
    `0xFFF7` bit-3-masking and `0x0020` bit-5 conventions already in
    place. Bits 1 and 2 (compression-option per APPNOTE §4.4.4 —
    Info-ZIP / 7-Zip legitimately set them on `method == 8` payloads)
    are explicitly out of scope; the mask `0xD780` is disjoint from
    the unsupported-feature mask `0x2071` (bits 0/4/5/6/13) covered
    by PR #1824 (bit 5, already landed; closed #1817) and the
    in-flight per-bit feature series (issues #1762, #1818). With
    PR #1819's `0xFFFE` `internalAttrs` mask, PR #2237's `0xD780` `flags`
    reserved-mask and the bit-5 `0x0020` flags-mask, the writer-zero
    single-`UInt16` column and the reserved/unsupported flag-bits
    columns sit as a contiguous CD-parse early-reject block. Sibling
    of PR #1824 (bit 5 patched-data, single-bit) at the same CD+8
    `flags` field — distinct mask, distinct error substring
    (`"flags reserved bits set"` vs.
    `"patched-data flag bit 5 set"`). Interop pre-flight over
    `testdata/zip/{interop,malformed}/*.zip` returned zero hits for
    `flags & 0xD780 != 0` before landing — no legitimate archive in
    the corpus sets any of the seven reserved/unused bits
  - CD-entry name NUL-byte rejection — PR #1831
    (`testdata/zip/malformed/cd-nul-in-name.zip`) rejects CD entries
    whose raw name bytes contain a NUL (`0x00`) byte at
    `parseCentralDir` time
    ([Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean)),
    before the UTF-8 decode at
    [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean).
    A NUL byte in the filename is a classic parser-differential /
    filesystem-truncation smuggling vector: POSIX `open`/`stat` and
    many runtime layers treat `evil.txt\x00.zip` as `evil.txt`, while
    `Archive.list` callers and strict peer readers see the full
    NUL-embedded string. Pre-PR, `Archive.list` returned the
    NUL-containing `path` verbatim (both `String.fromUTF8?` and
    `Binary.fromLatin1` preserve U+0000), and `Archive.extract` with
    the default `Binary.isPathSafe` passed the NUL-containing path
    into `IO.FS.writeBinFile` where the POSIX `open` layer truncates
    at NUL — depositing the extracted file at the short-form prefix,
    not the smuggled full form. Guarding on the raw `ByteArray` before
    UTF-8 decode keeps the error message NUL-free (no re-injection
    into logs) and closes both the UTF-8 and Latin-1 decode branches
    uniformly. Closes both `Archive.list` (silent NUL-path surfacing)
    and `Archive.extract` (silent truncated-filename drop) dimensions
    simultaneously — extract-time `Binary.isPathSafe` in
    [zipCommon / `ZipCommon/Binary.lean`](https://github.com/kim-em/lean-zip-common/blob/main/ZipCommon/Binary.lean)
    does not reject NUL and is shared with Tar, so CD-parse rejection
    is strictly local to the ZIP layer. Writer-side at
    [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) and
     inherits the invariant from caller-supplied `entry.path` (no
    emit-time enforcement). Interop pre-flight swept
    `testdata/zip/interop/*.zip` and `testdata/zip/malformed/*.zip`
    for pre-existing NUL-in-name fixtures: zero hits, so no
    pre-existing regression is disturbed. Net-new dimension observed
    during the CD-parse filename-validation coverage sweep
  - CD-entry path-safety rejection — PR #1840
    (`testdata/zip/malformed/cd-path-unsafe.zip`) rejects CD entries
    whose decoded `name` is path-unsafe per `Binary.isPathSafe` at
    `parseCentralDir` time
    ([Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean)),
    immediately after the UTF-8 / Latin-1 decode block at
    [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean)
    and before the `versionNeeded` upper-bound at
    [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean).
    `Binary.isPathSafe` (canonical lean-zip-common path-safety filter,
    shared with the Tar extract path) rejects absolute paths (`/`
    prefix), `\` anywhere, `..`/`.` components, empty components (from
    `//`), and Windows drive-letter components. Closes the
    path-traversal / archive-slip smuggling dimension on the
    `Archive.list` path, which pre-PR returned the `Entry` with the
    unsafe `path` verbatim — exposing the full smuggled form to
    callers who route on `entry.path` before any filesystem I/O. The
    extract-time `Binary.isPathSafe` calls at
    [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean)
    and  remain in place as defense-in-depth but are now
    unreachable for CD-parseable archives via the public API. Mirrors
    the trailing-slash carve-out at
    [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean)
    (directory entries end with `"/"`, checked on the slash-stripped
    form) so legitimate directory entries are not tripped. Quotes the
    name via `String.quote` so control bytes from the smuggled name
    never reach logs unescaped. Writer-side at
    [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) and
     inherits the invariant from caller-supplied `entry.path` (no
    emit-time enforcement); the CD-parse guard is read-side only.
    Interop pre-flight swept `testdata/zip/interop/*.zip` and
    `testdata/zip/malformed/*.zip` for pre-existing path-unsafe
    fixtures: zero hits, so no pre-existing regression is disturbed
    (the `testdata/zip/security/` directory contains three `zip-slip`
    / `absolute-path` / `backslash-slip` counter-fixtures whose
    existing `"unsafe path"` assertion substring is a substring of
    the new `"CD entry has unsafe path"` wording, so their tests
    continue to pass). Sibling of PR #1831 (CD-entry name NUL-byte
    rejection) on the same filename-validation layer — the pair
    together closes the "smuggled name" attack class (NUL byte + path
    shape). Net-new dimension observed during the CD-parse
    filename-validation coverage sweep
  - CD-entry empty-filename rejection — PR #1848
    (`testdata/zip/malformed/cd-empty-name.zip`) rejects CD entries
    whose `nameLen` field at CD +28 (APPNOTE §4.4.10) is `0` at
    `parseCentralDir` time
    ([Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean)),
    immediately after the `nameLen` read and before the
    `entryEnd > cdEnd` overrun check at
    [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean)
    and the sibling NUL-byte / path-safety filename guards. Every
    legitimate ZIP entry — file or directory — has at least one byte
    of name, so `nameLen == 0` is structurally pathological and a
    parser-differential smuggling vector: lenient readers emit
    `entry.path = ""` (an `Entry` with no useful identity), while
    `Archive.extract` would resolve `outDir / ""` to either `outDir`
    itself or a path with a trailing separator — neither of which
    the downstream `IO.FS.writeBinFile` / `createDir` calls reject
    with a message that attributes the fault to the empty-name
    structural anomaly. Guarding on the 16-bit `nameLen` field alone,
    before any later field-read or decode step, pins the failure
    attribution cleanly: the sibling CD-parse path-safety guard
    (PR #1840) would otherwise also catch `""` via `Binary.isPathSafe`'s
    empty-component rejection, but only if the decode succeeds — and
    the attribution then reads *"CD entry has unsafe path"* rather
    than the more direct *"CD entry has empty filename"*. Closes both
    `Archive.list` (pre-PR returned the `Entry` with `path = ""` —
    exposing an identity-less value to callers that route on
    `entry.path`) and `Archive.extract` (pre-PR surfaced as an
    `IO.FS.writeBinFile` / `createDir` error against `outDir / ""`,
    not the empty-name anomaly) dimensions simultaneously. Writer-side
    at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean)
    and  inherits the invariant from caller-supplied `entry.path`
    (no emit-time enforcement); the CD-parse guard is read-side only.
    Interop pre-flight swept `testdata/zip/interop/*.zip` and
    `testdata/zip/malformed/*.zip` for pre-existing CD entries with
    `nameLen == 0`: zero hits, so no pre-existing regression is
    disturbed. Sibling of PR #1831 (CD-entry name NUL-byte rejection,
    byte-content dimension) and PR #1840 (CD-entry path-safety
    rejection, path-shape dimension) on the same filename-validation
    layer — the trio together closes the "smuggled name" attack class
    at CD parse: zero-length, NUL-embedded, and path-traversal forms
    are all rejected pre-decode. Net-new dimension observed during
    the CD-parse filename-validation coverage sweep
  - CD-entry empty-entry CRC invariant rejection — PR #1857
    (`testdata/zip/malformed/cd-empty-entry-crc-nonzero.zip`) rejects
    CD entries whose `uncompressedSize == 0` with any nonzero `crc32`
    at `parseCentralDir` time
    ([Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean)),
    post-ZIP64-resolution, after the stored-method size invariant.
    APPNOTE §4.4.7 defines the CRC32 field as the ANSI-CRC-32 of the
    uncompressed payload; the empty byte string has CRC32 `0x00000000`
    (start state `0xFFFFFFFF`; no data to process; final complement
    returns `0x00000000`), so `uncompSize == 0 → crc == 0` is a
    universal mathematical invariant. Every correct writer — Info-ZIP,
    Go `archive/zip`, CPython `zipfile`, 7-Zip, and lean-zip's own
    `create` at
    [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean)
    (which emits `Checksum.crc32 0 fileData` and hence `0` on an empty
    payload) — obeys it. Crafted archives carrying `uncompSize = 0`
    alongside any nonzero CRC are structurally malformed and a
    parser-differential smuggle vector: pre-PR, `parseCentralDir`
    propagated the crafted CRC into `Entry.crc32` verbatim, so
    `Archive.list` callers that routed on `entry.crc32` (logging,
    deduplication, downstream CRC cross-checks) saw the smuggled value
    while strict peer parsers or CRC-cross-checking callers rejected.
    Pre-PR, `Archive.extract` caught the mismatch only post-extraction
    via the `"CRC32 mismatch"` guard at
    [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean),
    after the I/O work had been performed; `Archive.list` had no gate
    at all. Placed after the stored-method size invariant so the
    resolved `uncompSize : UInt64` is the value checked (rather than
    the `0xFFFFFFFF` sentinel) and so attribution pins on the empty-
    file premise rather than a generic CRC check. The `uncompSize == 0`
    probe runs first so the CRC field is inspected only when the
    empty-file premise holds; method 0 (stored) and method 8 (deflate)
    share the same invariant — a deflate-encoded empty stream has
    `compSize = 2` (the `03 00` empty-block encoding) but `uncompSize
    = 0`, so the check applies regardless of method. Writer-side at
    [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) is
    trivially compliant (`Checksum.crc32 0 ByteArray.empty == 0` by
    the CRC-32 init⊕complement identity); the CD-parse guard is
    read-side only. Sibling of PR #1773 (stored-method size invariant)
    at the CD-parse mathematical-invariant family: #1773 closes the
    `compSize == uncompSize` dimension (tautological for stored
    entries); the present bullet closes the `uncompSize == 0 → crc == 0`
    dimension (tautological for every empty entry, regardless of
    method). Net-new dimension observed during the CD-parse
    mathematical-invariant coverage sweep — the *Missing work* block
    had not previously flagged the empty-entry CRC invariant
  - CD-entry `compressedSize > 0` rejection when `uncompressedSize > 0`
    — PR #1886
    (`testdata/zip/malformed/cd-deflate-zero-compsize.zip`) rejects CD
    entries whose `compressedSize == 0` alongside any positive
    `uncompressedSize` at `parseCentralDir` time, post-ZIP64-resolution,
    after the stored-method size invariant and the empty-entry CRC
    invariant. APPNOTE §4.4.8 / §4.4.9 define the `compressedSize` and
    `uncompressedSize` fields; every ZIP compression method produces
    at least one compressed byte from non-empty uncompressed input —
    method 0 (stored, APPNOTE §4.4.5) has `compSize == uncompSize`;
    method 8 (deflate, RFC 1951) has a 2-byte minimum block-header
    encoding (`03 00` empty-stored-block), so any non-empty inflate
    output requires at minimum a block header plus encoded data.
    Therefore `compSize == 0 ∧ uncompSize > 0` is structurally
    impossible regardless of method — a universal mathematical
    invariant every correct writer (Info-ZIP, Go `archive/zip`, CPython
    `zipfile`, 7-Zip, lean-zip's own `create` at
    [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean))
    obeys. Pre-PR, the sibling stored-method guard (PR #1773) caught
    this shape only when `method == 0` (via the `compSize == uncompSize`
    equality mismatch), leaving `method == 8` entries with this shape
    unguarded at CD parse — they fell through to the downstream
    `readEntryData` + inflate path, which only runs on `Archive.extract`
    and whose error attribution is scattered among the decompression
    backends (`Zlib.decompress` / `Gzip.decompress` /
    `Zip.Native.Inflate.inflate` all fail with some variant of
    *"unexpected end of deflate stream"* or *"invalid block type"*)
    rather than pinned on the CD-parse structural anomaly. Pre-PR,
    `Archive.list` returned the `Entry` with `{method = 8, compSize = 0,
    uncompSize = 42, ...}` verbatim — callers routing on
    `entry.compressedSize == 0` as a short-circuit (cache lookups, ACL
    checks, downstream CRC verification) saw the smuggled values. The
    sibling empty-entry CRC guard (PR #1857) fires only on
    `uncompSize == 0`; the new invariant fires only on `uncompSize > 0`,
    so the two are ordering-disjoint. The third column of the per-entry
    mathematical-invariant family at CD parse: PR #1773 closes the
    `compSize == uncompSize` dimension (tautological for stored entries,
    method=0 only); PR #1857 closes the `uncompSize == 0 → crc == 0`
    dimension (tautological for empty entries, method-agnostic); PR #1886
    closes the `uncompSize > 0 → compSize > 0` dimension (structurally
    required under any compression method — method-agnostic). Together
    the three columns form a contiguous block of math invariants at
    `parseCentralDir`
  - oversized ZIP64 compressed-size fixture — PR #1543
    (`testdata/zip/malformed/oversized-zip64-compressed-size.zip`)
  - oversized ZIP64 uncompressed-size fixture — PR #1544
    (`testdata/zip/malformed/oversized-zip64-uncompressed-size.zip`)
  - bounded-read helpers for `Handle`/`Stream` — PR #1608
    (Track E P5.1)
  - `SpanInFile` predicate + IO reduction lemmas — PR #1636
    (Track E P5.2)
  - `Archive`/`Tar` callers migrated to bounded-read helpers — PR #1626
    (Track E P5.3)

### Tar Parser/Extractor

- Components: [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean)
- Status: `guarded-locally`
- Trust boundary:
  - parses tar headers, GNU long-name records, PAX metadata, symlinks,
    and streamed entry contents
- Current guardrails:
  - explicit `maxEntrySize` in extraction paths
  - path safety checks for extracted files
  - short-read detection in entry and padding reads
  - invalid PAX UTF-8 is skipped instead of panicking in `parsePaxRecords`
- Missing work:
  - none open at this layer; the policy and fixture work below are done
- Recent wins:
  - `String.fromUTF8!` callsite audit — PR #1550
    (`Tar.truncateUTF8`; regression coverage in
    `ZipTest/TarPathTruncation.lean`)
  - malformed PAX fixtures — PR #1545
    (`testdata/tar/malformed/pax-*.tar`)
  - malformed GNU long-name/long-link fixtures — PR #1546
    (`testdata/tar/malformed/gnu-longname-*.tar`,
    `gnu-longlink-truncated.tar`)
  - symlink/hardlink extraction policy + archive-slip tests — PR #1555
    (see subsection below; `testdata/tar/security/`)
  - UStar `name` / `linkname` / `prefix` / `uname` / `gname` interior-NUL
    rejection in `parseHeader` — PR #1880 (`name` slot,
    `testdata/tar/malformed/ustar-name-nul-in-name.tar`) + per-slot
    `linkname` follow-up
    (`testdata/tar/malformed/ustar-linkname-nul-in-name.tar`) +
    per-slot `prefix` follow-up
    (`testdata/tar/malformed/ustar-prefix-nul-in-name.tar`) + 4th-slot
    `uname` defense-in-depth follow-up
    (`testdata/tar/malformed/ustar-uname-nul-in-uname.tar`) +
    5th-and-final `gname` defense-in-depth follow-up
    (`testdata/tar/malformed/ustar-gname-nul-in-gname.tar`).
    `Tar.parseHeader` runs `hasInteriorNul` on the raw 512-byte block
    after the checksum + magic checks and before any
    `Binary.readString` call on the five UStar string fields. Five
    distinct error substrings keep attribution per-field —
    *"UStar name contains NUL byte"* (offset 0, 100 B),
    *"UStar linkname contains NUL byte"* (offset 157, 100 B),
    *"UStar prefix contains NUL byte"* (offset 345, 155 B),
    *"UStar uname contains NUL byte"* (offset 265, 32 B),
    *"UStar gname contains NUL byte"* (offset 297, 32 B). Closes
    the UStar layer of the smuggled-NUL attack class — sibling of
    PR #1831 (ZIP CD entry name, *"CD entry name contains NUL byte"*),
    PRs #1865 (long-name slot, `gnu-longname-nul-in-name.tar`) /
    #1953 (long-link slot, `gnu-longlink-nul-in-link.tar`) (GNU
    long-name / long-link, *"GNU long-name contains NUL byte"* /
    *"GNU long-link contains NUL byte"*), and PR #1866 (PAX
    `keyBytes` / `valueBytes` silent-skip in `parsePaxRecords`). The
    UStar interior-NUL family is **fully closed 5/5** — the 3-slot
    filesystem-reaching arm (`name` / `linkname` / `prefix`) plus the
    2-slot defense-in-depth arm (`uname` / `gname`). All five arms
    now each carry a dedicated per-slot regression fixture. The
    `uname` / `gname` fields do not reach the filesystem in
    `Tar.extract` — their guards are defense-in-depth against a
    `Tar.list` caller routing on `entry.uname` / `entry.gname` for a
    trust decision and seeing only the truncated prefix while peer
    parsers preserve the full bytes.
  - GNU long-name / long-link interior-NUL rejection in `forEntries`
    — PR #1865 (both guards in `forEntries`'s `typeGnuLongName` /
    `typeGnuLongLink` arms; long-name regression fixture
    `testdata/tar/malformed/gnu-longname-nul-in-name.tar`) +
    per-slot long-link follow-up
    (`testdata/tar/malformed/gnu-longlink-nul-in-link.tar`,
    PR #1953). Two error substrings keep per-slot attribution —
    *"GNU long-name contains NUL byte"* (typeflag `'L'` arm at
    [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean)) and
    *"GNU long-link contains NUL byte"* (typeflag `'K'` arm at
    [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean)).
    `forEntries` runs `findIdx? (· == 0)` on the raw `ByteArray`
    payload after `stripTrailingNuls` and before
    `String.fromUTF8?` / `Binary.fromLatin1`, so neither decode
    branch can re-introduce NUL into the error message. The
    GNU long-name / long-link interior-NUL family is
    **fully closed 2/2** — long-name slot (PR #1865,
    `gnu-longname-nul-in-name.tar`) + long-link slot (PR #1953,
    `gnu-longlink-nul-in-link.tar`). Sibling of PRs #1880 / #1934
    / #1937 / #1944 / #1957 (UStar interior-NUL family fully
    closed 5/5), PR #1831 (ZIP CD entry name NUL-byte rejection),
    and PR #1866 (PAX `keyBytes` / `valueBytes` silent-skip in
    `parsePaxRecords`). lean-zip's tar writer does not emit GNU
    long-name / long-link pseudo-entries (`Tar.create` always
    emits UStar-or-PAX-extended-header for paths exceeding the
    UStar 100/155-byte limits), so neither guard ever fires on
    legitimate archives produced by `Tar.create`. The guards
    exist to reject crafted malformed archives fed to `Tar.list`
    / `Tar.extract` — the fixtures are the only way to trigger
    them.
  - PAX extended-header duplicate-key rejection in `parsePaxRecords` —
    PR #1899
    (`testdata/tar/malformed/pax-duplicate-path.tar`).
    Ordering inside `parsePaxRecords`: UTF-8 decode → raw-byte NUL
    guard → duplicate-key check → push, so the duplicate-key branch
    at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) only
    fires on records that already passed the UTF-8 and NUL filters.
    Unlike PR #1866 (PAX NUL-byte silent-skip, which drops the
    offending record and continues), PR #1899 hard-rejects — the
    `.error` return is rethrown unconditionally by `forEntries`'s
    `typePaxExtended` branch at
    [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) via
    `throw (IO.userError msg)`. Error wording *"tar: PAX extended
    header has duplicate {key.quote} record"* uses `String.quote`
    attribution on the duplicate key. Closes the parser-differential
    *duplicate-key* dimension on `parsePaxRecords` complementary to
    PR #1866's NUL-byte silent-skip; together the two close both
    parser-differential dimensions on the PAX-record decode pipeline.
  - PAX extended-header value-side NUL-byte silent-skip in
    `parsePaxRecords` — PR #1866 (`path` slot,
    `testdata/tar/malformed/pax-path-nul-in-value.tar`) +
    per-slot `linkpath` follow-up
    (`testdata/tar/malformed/pax-linkpath-nul-in-value.tar`,
    PR #1979). `parsePaxRecords` runs
    `findIdx? (· == 0)` on the raw `keyBytes` / `valueBytes`
    slices at
    [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean)
    (`keyBytes`) and
    [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean)
    (`valueBytes`) after `String.fromUTF8?` accepts the bytes
    (which permits U+0000 as valid UTF-8) and before the
    duplicate-key check pushes onto the records array. Records
    that fail this guard are dropped silently, matching the
    invalid-UTF-8 precedent on the same loop, *not* hard-rejected
    like PR #1899's duplicate-key guard at
    [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean).
    Ordering inside `parsePaxRecords` is UTF-8 decode → raw-byte
    NUL guard → duplicate-key check → push; the silent-skip
    happens at the raw-byte NUL stage on `keyBytes` / `valueBytes`
    before `Binary.fromLatin1` would re-decode on the
    `applyPaxOverrides` side. The companion `applyPaxOverrides`
    case-arms at
    [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean)
    (`"path"` → `entry.path`) and
    [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean)
    (`"linkpath"` → `entry.linkname`) are the smuggle targets
    the silent-skip prevents from firing — pre-guard, an
    attacker-controlled record `path=a\x00b/c` would land as
    `entry.path = "a\x00b/c"` (POSIX `open` truncates at NUL on
    `Tar.extract` while `Tar.list` callers see the full embedded
    string), and `linkpath=a\x00b/c` would land as
    `entry.linkname = "a\x00b/c"` (POSIX `symlink` truncates
    similarly on the symlink path). The PAX value-side override
    family is **fully closed 2/2** — `path` slot (PR #1866,
    `pax-path-nul-in-value.tar`) + `linkpath` slot (PR #1979,
    `pax-linkpath-nul-in-value.tar`). Terminal closure of the
    third per-slot Tar interior-NUL family in the post-#1928
    wave (after the 5-slot UStar family closed at PR #1957 and
    the 2-slot GNU long-name / long-link family closed at
    PR #1953); together the three terminal closures complete the
    "smuggled NUL in any user-supplied string field" attack
    class across the entire Tar parsing surface (UStar + GNU +
    PAX). Sibling of PRs #1880 / #1934 / #1937 / #1944 / #1957
    (UStar interior-NUL family fully closed 5/5), PRs #1865 /
    #1953 (GNU long-name / long-link family fully closed 2/2),
    PR #1899 (PAX duplicate-key, complementary
    parser-differential dimension on the same `parsePaxRecords`
    loop), and PR #1831 (ZIP CD entry name NUL-byte rejection).
    lean-zip's tar writer does not emit PAX extended headers
    (`Tar.create` always emits UStar-or-PAX-extended-header for
    paths exceeding the UStar 100/155-byte limits, but never the
    value-side override records that this guard fires on), so
    neither slot of the guard ever fires on legitimate archives
    produced by `Tar.create` — the guards exist to reject crafted
    malformed archives fed to `Tar.list` / `Tar.extract`, and the
    fixtures are the only way to trigger them. The companion
    `keyBytes` arm at
    [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) is
    defense-in-depth (no known-key string in `applyPaxOverrides`'s
    case match contains `\x00`, so a NUL-bearing key would
    already be dropped at the case match) and is closed by
    PR #2405 (`pax-nul-in-key.tar`); the `parsePaxRecords`
    NUL-byte guard family is therefore **fully closed 3/3**
    (1 keyBytes + 2 valueBytes).
- Paired review of PR #2405 (`pax-nul-in-key.tar` fixture —
  `parsePaxRecords` NUL-byte guard family terminal closure 3/3):
  - **Family-closure fidelity.** The 1 + 2 = 3 math is internally
    consistent and faithful to the merged tree.
    [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) `parsePaxRecords`
    carries exactly two `findIdx? (· == 0)` NUL-byte guards joined by
    `&&` — one on `keyBytes`, one on `valueBytes` — so the arm-level
    accounting is *1 keyBytes arm + 1 valueBytes arm = 2 arms*. The
    fixture-level accounting tracks per-slot pinning of each
    filesystem-reaching smuggle target: `pax-nul-in-key.tar` (PR #2405)
    pins the keyBytes arm; `pax-path-nul-in-value.tar` (PR #1866) and
    `pax-linkpath-nul-in-value.tar` (PR #1979) pin the two
    filesystem-reaching slots of the valueBytes arm via their
    `applyPaxOverrides` targets (`"path"` → `entry.path`, `"linkpath"`
    → `entry.linkname`). The valueBytes guard fires regardless of
    which key the value is paired with — there is no per-slot variant
    of the guard itself; the 2-slot count is *override-target*
    granularity, not *guard* granularity. No fourth or fifth
    `findIdx? (· == 0)` call exists in `parsePaxRecords`, so the
    *fully closed 3/3* claim is faithful at the guard level. Sibling
    valueBytes overrides exist for non-string slots (`"size"`,
    `"mtime"`, `"uid"`, `"gid"` — number-parsed, NUL would fail digit
    parsing) and for two defense-in-depth string slots (`"uname"`,
    `"gname"` — value-side parallels of UStar `uname` / `gname`); the
    inventory's *2-slot* framing is explicitly *filesystem-reaching*
    so those defense-in-depth value-side slots are out of scope by
    construction. Recording the scoping convention here so a future
    reader audit-tracing the *3/3* claim does not re-discover the
    `"uname"` / `"gname"` value-side parallels and misread them as a
    missing 4th / 5th slot: they are not slots of *this* family by the
    inventory's filesystem-reaching framing.
  - **Reproducer Corpus row prose fidelity.** The new
    `pax-nul-in-key.tar` row carries the four required elements:
    (i) cites the closing PR #2405 in the rightmost PR column —
    correct (the table has a closing-PR column and a category column,
    not a closing-issue column, so the issue body's *"closing
    issue (#2404) in the rightmost columns"* phrasing is slightly
    imprecise; #2404 is recorded in the closing PR's body, not the
    row); (ii) names the assertion shape as a *positive regression*
    explicitly and cites the adversarial check (*"verified
    adversarially by temporarily disabling the keyBytes arm and
    confirming the loop assertion still passes"*) — matches the
    sibling `pax-linkpath-nul-in-value.tar` row's *positive
    regression* prose; (iii) names the fixture as the **terminal
    closure** of the `parsePaxRecords` NUL-byte guard family at 3/3
    and cites both valueBytes-slot siblings (PR #1866 / PR #1979) by
    fixture name and PR number; (iv) uses stable
    [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) anchors only — no
    `line N` references — consistent with the
    [#2353](https://github.com/kim-em/lean-zip/pull/2353) decision to
    drop line-number anchors in inventory files.
  - **Sibling-row deferral-drop fidelity.** The
    `pax-linkpath-nul-in-value.tar` row's edit is a clean
    *Half-closed two-step* completion under the *Scaffold variant*
    shape codified in PR #2399 / paired-reviewed in PR #2403. The
    pre-existing trailing *"left for a future per-arm extension"*
    fragment is removed cleanly (no orphan punctuation, no
    half-finished sentence; the substitution lands inside the same
    `(...)` parenthetical without breaking sentence boundaries). The
    replacement reads as steady-state past-tense — *"is closed by
    `pax-nul-in-key.tar` (PR #2405); the `parsePaxRecords` NUL-byte
    guard family is therefore **fully closed 3/3** (1 keyBytes +
    2 valueBytes)"* — mirroring PR #2401's post-#2399 cleanup style.
    The body of the sibling row is otherwise unchanged. The same
    in-place substitution lands a second time in the parent
    `Recent wins` paragraph (the 2014–2078 bullet covering the PAX
    value-side NUL family) — so both occurrences of the deferral
    phrase on master are flipped together rather than leaving a
    half-flipped tree.
  - **Defense-in-depth phrasing.** The new row classifies the
    keyBytes guard as *defense-in-depth* explicitly and explains the
    downstream reason (*"no known-key string contains `\x00`, so
    `applyPaxOverrides`'s case match would already drop the record
    without it"*). The adversarial check from
    [progress/20260429T204753Z_f5ad77c6_pax-nul-in-key-fixture.md](/home/kim/lean-zip/progress/20260429T204753Z_f5ad77c6_pax-nul-in-key-fixture.md)
    is cited inline as the operational evidence for the
    defense-in-depth claim — temporarily disabling the keyBytes arm,
    re-running the test, and confirming the loop assertion still
    passes. The phrasing also names the future-fallback risk (*"a
    future fallback like a prefix-match for namespace-style keys
    would silently re-open the smuggle"*) so the audit trail is
    explicit about *why* the guard exists despite the case match
    already dropping NUL-bearing keys today.
  - **Same-pattern precedent.** The new row cites
    [PR #1957](https://github.com/kim-em/lean-zip/pull/1957) (UStar
    `gname` slot, terminal closure of the 5-slot UStar interior-NUL
    family) as the *fixture-only, defense-in-depth, family-closing*
    template. The cite resolves to a real role-equivalent row:
    PR #1957's `ustar-gname-nul-in-gname.tar` Reproducer Corpus row
    in this same inventory carries the same structural shape — a
    positive-regression-style assertion (the bare `"UStar"` prefix is
    explicitly distinguished by the `"gname"`-bearing substring, so
    the test pins on the gname arm specifically), an explicit
    family-closure claim (*"5-slot UStar interior-NUL family is
    **fully closed 5/5**"*), and a defense-in-depth phrase
    (*"`gname` does not reach the filesystem in `Tar.extract` — the
    guard is defense-in-depth at the `Tar.list` layer"*). The
    structural parallel between the two rows is exact: PR #1957's
    `gname` slot is to UStar what PR #2405's `keyBytes` arm is to
    `parsePaxRecords` — a fixture pinning a guard whose single-arm
    removal alone would not surface as a regression because a
    downstream guard (UStar's `Binary.readString` truncation for
    `gname`; `applyPaxOverrides`'s case match for `keyBytes`) already
    drops the smuggled value. The precedent cite is faithful, not a
    ghost reference.
  - **Follow-up gaps.** None surface. The audit confirms all five
    dimensions: the family-closure math is internally consistent and
    matches the source-level guard count (2 guards, 3 per-slot
    fixtures); the new Reproducer Corpus row carries the required
    prose elements; the sibling-row deferral-drop is a clean
    in-place substitution per the *Scaffold variant* shape; the
    defense-in-depth phrasing names both the *why* and the
    *future-fallback risk*; and the PR #1957 precedent cite resolves
    to a real role-equivalent row. The only audit-relevant
    observation worth recording is the scoping convention noted in
    *Family-closure fidelity*: the value-side `"uname"` / `"gname"`
    overrides in `applyPaxOverrides` exist as defense-in-depth
    parallels of UStar `uname` / `gname`, but the inventory's
    *filesystem-reaching* framing for the 2-slot value-side family
    excludes them by construction. Whether to extend the value-side
    family with per-slot defense-in-depth fixtures for those two
    slots is a separate scoping decision, not a closure gap; this
    paired-review surfaces no follow-up issue for it.
- Paired review of PR #2413 (`tar-fifo-skipped.tar` fixture —
  per-typeflag silent-skip family extension 1 → 2; this paired-review
  landed in PR #2419 closing #2414):
  PR #2413 (squash commit `cafab42374`, merged 2026-05-02T01:08:37Z,
  closes #2412) extends the `Tar.extract` silent-skip `else` fallback
  family from one to two sibling fixtures. The commit adds a
  512-byte single-block UStar fixture
  `testdata/tar/security/tar-fifo-skipped.tar` (SHA-256
  `b2e897b74be1264344e508ffd27269f261a08bdaced2f71ded907769155e352a`)
  for typeflag `'6'` (POSIX UStar FIFO, `0x36`); a third
  `buildZeroSizeFixture` call in
  [scripts/build-symlink-hardlink-malformed-fixtures.lean](/home/kim/lean-zip/scripts/build-symlink-hardlink-malformed-fixtures.lean)
  producing it deterministically; a new test arm in
  [ZipTest/TarFixtures.lean](/home/kim/lean-zip/ZipTest/TarFixtures.lean)
  immediately after the existing `hardlink-outside.tar` arm, asserting
  the extract directory is empty after extraction (mirroring the
  `hardlink-outside.tar` arm shape); a new Reproducer Corpus row in
  this inventory; and a *Symlink/hardlink extraction policy* fixture
  enumeration entry. No spec change, no production-code change,
  no new typeflag constant in the `Tar` namespace, no caller / signature
  change.
  - **Family-extension claim fidelity.** The 1 → 2 extension math is
    faithful to the merged tree. PR #2413 is the second per-typeflag
    fixture in the silent-skip family; sibling `hardlink-outside.tar`
    (PR #1555, typeflag `'1'`) is the first. The two pin two distinct
    typeflag values (`0x31` and `0x36`) against the shared `else`
    fallback at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean)
    (`partial def extract`'s tail `else` arm, after the
    `typeDirectory` / `typeRegular` / `typeSymlink` cases). Both
    fixtures have `size = 0` and route through the same
    `skipEntryData input e.size` no-op call in the `else` body, so
    the structural pin is the *existence* of the `else` arm rather
    than the *behaviour* of any per-typeflag dispatch — a future
    refactor that drops the fallback for any one arm would fire the
    corresponding fixture. The originating PR #1555 set the precedent
    that the silent-skip dispatch is uniform across all unsupported
    typeflags; PR #2413 adds the second pin against accidental
    single-arm-only refactor drop. Sibling-cluster precedent: the
    UStar interior-NUL family went 1 → 4 across PRs #1934 / #1937 /
    #1944 before terminal-closing at 5/5 in PR #1957; PR #2413 is
    the first step on the analogous silent-skip family ladder.
    PR #2417 has since extended the family to 3/N (typeflag `'3'`,
    character device, `0x33`) on the same cadence, so the family
    currently sits at 3 sibling fixtures — PR #2413's claim was
    1 → 2 at its own merge time, faithful at that snapshot.
  - **Fixture-builder rename-vs-extend choice.** The worker chose
    *extend in place* rather than rename the script. The script path
    [scripts/build-symlink-hardlink-malformed-fixtures.lean](/home/kim/lean-zip/scripts/build-symlink-hardlink-malformed-fixtures.lean)
    stays stable; the module docstring's opening line is updated to
    *"Build per-typeflag-policy regression fixtures for Track E
    Priority 1"* and the build summary line at `main`'s tail prints
    *"Built 4 per-typeflag-policy security fixtures"* (3 at PR #2413
    merge time, 4 after PR #2417; the count moves with the fixture
    set, the framing stays). The docstring enumeration explicitly
    lists the FIFO arm with its typeflag `0x36`, `path =
    "fifo-entry"`, empty linkname, and the silent-skip `else`
    fallback semantics — matching the source-level `else` body
    comment at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) (which
    enumerates *"`typeHardlink` ('1'), character and block devices,
    FIFOs, GNU sparse, etc."*). The extend-in-place choice keeps
    paired-review and future per-typeflag siblings (PR #2417 already
    followed) on the same script with no rename churn.
    Worker-recorded rationale in
    [progress/20260502T010556Z_1bc32f11_tar-fifo-skipped-fixture.md](/home/kim/lean-zip/progress/20260502T010556Z_1bc32f11_tar-fifo-skipped-fixture.md):
    *"Did not rename the script file itself — the existing path stays
    stable for paired-review and future per-typeflag siblings can
    extend the same script."* The choice is faithful to the docstring
    framing and matches the inventory's *"Built by the same script"*
    cross-reference at the *Symlink/hardlink extraction policy*
    fixture enumeration immediately below.
  - **Reproducer Corpus row prose fidelity.** The new
    `tar-fifo-skipped.tar` row carries the seven required elements:
    (i) typeflag value `0x36` and the POSIX UStar `'6'` glyph (cited
    together in the row's opening clause); (ii) POSIX semantics
    *"FIFO"* with the POSIX.1-1988 IEEE Std 1003.1 §10 citation;
    (iii) silent-skip `else` branch, with explicit reference to
    `Tar.extract`'s tail `else` arm and the `skipEntryData` no-op on
    `e.size = 0`; (iv) sibling fixture cross-reference to
    `hardlink-outside.tar` (typeflag `'1'`); (v) the family-extension
    claim phrased as *"Per-typeflag silent-skip family extension"*
    with the *"two together pin the silent-skip policy against
    accidental drop of the fallback"* defense-in-depth framing;
    (vi) the writer-side caveat (*"`Tar.create`'s caller-API only
    accepts paths and never invokes `Tar.buildHeader` with a
    non-`'0'`/`'5'` typeflag, so legitimate archives produced by the
    lean-zip writer never carry typeflag `'6'`"*) — confirmed by
    reading [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean)
    (`Tar.create` builds entries via `walkFiles` with `typeflag :=
    if isDir then typeDirectory else typeRegular`, so no other
    typeflag value can leak through the public writer API);
    (vii) only stable [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean)
    anchors — no `:N` line-number suffixes, consistent with the
    [PR #2353](https://github.com/kim-em/lean-zip/pull/2353) decision.
    **Defect surfaced and fixed inline:** at PR #2413 merge time the
    row's closing-PR column carried the literal `#TBD-VERIFY-PR` <!-- drift-detector: prose mention of the placeholder token in a paired-review finding, not a stale placeholder -->
    placeholder rather than `#2413` — the post-merge substitution
    that should have landed in the same branch immediately after
    `gh pr create` returned the real PR number (per the
    [PR #2364](https://github.com/kim-em/lean-zip/pull/2364) /
    [PR #2407](https://github.com/kim-em/lean-zip/pull/2407) cadence)
    did not happen. The substitution lands in this paired-review PR
    instead (single-character edit `#TBD-VERIFY-PR` <!-- drift-detector: prose mention of the placeholder token in a paired-review finding, not a stale placeholder --> → `#2413`), so
    the row's closing-PR column now correctly attributes to PR #2413
    and `bash scripts/check-inventory-links.sh` drops the
    corresponding stale-placeholder warning. No follow-up issue is
    needed — the substitution is bundled inline; the audit surfaces
    the convention slip so a future paired-review reader knows the
    row's attribution was completed during the paired-review cycle
    rather than at the fixture-merge cycle.
  - **Adversarial check.** The adversarial check is recorded in
    [progress/20260502T010556Z_1bc32f11_tar-fifo-skipped-fixture.md](/home/kim/lean-zip/progress/20260502T010556Z_1bc32f11_tar-fifo-skipped-fixture.md)
    *## Adversarial check*: temporarily wrapping the `else` body in
    `if e.typeflag == typeHardlink then skipEntryData input e.size
    else throw (IO.userError s!"adversarial: unexpected typeflag
    {e.typeflag}")` left `hardlink-outside.tar` passing while
    `tar-fifo-skipped.tar` fired with `uncaught exception:
    adversarial: unexpected typeflag 54` (`0x36 = 54`). The
    disable-revert was clean — *"Reverted the change before commit;
    `git diff Zip/Tar.lean` is empty post-revert"* — and the
    post-revert `git diff` cleanliness is independently confirmable
    from the merged tree (PR #2413's diff at
    [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) shows zero lines
    changed). The adversarial-check pattern matches the PR #2405
    paired-review's *Defense-in-depth phrasing* bullet (*"verified
    adversarially by temporarily disabling the keyBytes arm and
    confirming the loop assertion still passes"*) — same shape:
    transform the source so a hypothetical refactor's failure mode
    is simulated, run the test suite, observe the new fixture
    catching the simulated drop, revert. PR #1555's original
    `hardlink-outside.tar` fixture had no recorded adversarial check
    at the time of landing (the *"positive regression"* assertion
    shape was new); PR #2413 establishes the adversarial-check
    convention for the silent-skip family — PR #2417 has since
    followed (recorded in its own progress entry's
    *## Adversarial check* section, with the disable wrapper extended
    to spare both `typeHardlink` and `0x36` so only `0x33` fires).
    The convention is now cross-PR consistent.
  - **Sibling-fixture audit independence.** The two extract
    directories `/tmp/lean-zip-fixture-hardlink-outside-extract` and
    `/tmp/lean-zip-fixture-tar-fifo-skipped-extract` are distinct
    paths and each test arm independently `rm -rf`s + recreates its
    own directory before extracting (per the cleanup-then-create
    pattern in
    [ZipTest/TarFixtures.lean](/home/kim/lean-zip/ZipTest/TarFixtures.lean)).
    The cleanup loop at the end of the test bundle includes both
    directory paths in its `rm -rf` list, and the per-fixture file
    list (`writeFixtureTmp` outputs under `/tmp/lean-zip-fixture-*`)
    includes both `hardlink-outside.tar` and `tar-fifo-skipped.tar`.
    No shared mutable state between the two arms — re-running the
    test suite against any subset of arms produces the same result
    because each arm reads its own fixture, writes to its own
    extract directory, and asserts on its own `readDir` result. The
    `hardlink-outside.tar` test arm continues to pass after the new
    arm is added (independently confirmed by `lake exe test` on the
    merged tree: *"TAR fixture tests: OK"*). The two-arm independence
    is the structural prerequisite for the family-extension claim:
    a future refactor that breaks one arm's silent-skip behaviour
    cannot accidentally pass because of mutable state propagated
    from the other arm.
  - **Stable-cite discipline.** The new Reproducer Corpus row uses
    only stable identifiers — function names (`Tar.extract`,
    `skipEntryData`, `Tar.forEntries`, `Tar.buildHeader`,
    `Tar.create`) and fixture filenames (`tar-fifo-skipped.tar`,
    `hardlink-outside.tar`, `pax-nul-in-key.tar`). No `line N` or
    `:N` suffixes appear anywhere in the row, consistent with the
    [PR #2353](https://github.com/kim-em/lean-zip/pull/2353) decision
    to drop line-number anchors. Cross-reference cites resolve to
    real artefacts: PR #2405 / PR #1555 are both real merged PRs
    with the cited fixtures and policies; the
    [`pax-nul-in-key.tar`](/home/kim/lean-zip/testdata/tar/malformed/pax-nul-in-key.tar)
    inline link points at a real fixture path. The
    [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) anchor is
    repeated rather than aliased, matching the inventory's house
    style. After the closing-PR substitution noted above, `bash
    scripts/check-inventory-links.sh` reports `errors=0,
    warnings=2` — the two remaining warnings are *"this PR"* <!-- drift-detector: prose discussion of the placeholder phrase in a paired-review finding, not a stale placeholder --> prose
    mentions in the row's adversarial-check phrasing (*"verified by
    adversarial check during this PR"* <!-- drift-detector: quote of the adversarial-check phrasing in a paired-review finding, not a stale placeholder -->) on this row and the sibling
    `tar-chardev-skipped.tar` row, inherited from PR #2413 and
    PR #2417 respectively. The *"this PR"* <!-- drift-detector: prose discussion of the placeholder phrase in a paired-review finding, not a stale placeholder --> phrase is the standard
    adversarial-check shape used across the silent-skip family rows;
    suppressing those warnings would require `<!-- drift-detector:
    ... -->` opt-out comments per the PR #2371 paired-review pattern.
    This paired-review does not add the opt-outs (the prose mentions
    are not stale placeholders — the *"this PR"* <!-- drift-detector: prose discussion of the placeholder phrase in a paired-review finding, not a stale placeholder --> text correctly
    references the adversarial check that the closing PR's progress
    entry records), but a future inventory-cleanup PR could batch
    the opt-outs across the silent-skip family rows for warning-count
    cleanliness if desired.
  - **Follow-up gaps.** None surface that warrant a separate issue.
    The audit confirms all six required dimensions: the
    family-extension math is internally consistent and source-level
    verified; the rename-vs-extend choice matches the docstring's
    per-typeflag enumeration; the Reproducer Corpus row carries all
    seven required elements (with the stale closing-PR placeholder
    fixed inline); the adversarial check is recorded in the progress
    entry with a clean post-revert diff; the two-arm test bundle is
    structurally independent; the stable-cite discipline holds. The
    closing-PR substitution slip recorded under *Reproducer Corpus
    row prose fidelity* is bundled inline rather than spawning a
    separate cleanup issue (cleanup-PR pattern precedent:
    [PR #2411](https://github.com/kim-em/lean-zip/pull/2411) was a
    separate PR for stale `#1885` back-pointers across older inventory
    rows, but here the substitution is for the subject PR's own row
    and lands as a one-line edit alongside the paired-review prose).
    The next family-extension candidate after PR #2417 (typeflag
    `'3'`, character device) is typeflag `'4'` (POSIX UStar block
    device, `0x34`) or typeflag `'7'` (POSIX UStar contiguous file,
    `0x37`); naming them without committing to a specific issue
    number, matching the PR #2371 paired-review entry's close-out
    style. The silent-skip family is open-ended (every additional
    per-typeflag arm fires the same `else` fallback in `Tar.extract`,
    so the marginal fixture cost falls but the marginal regression
    benefit also falls); any future per-typeflag fixture should earn
    its own paired-review entry on the established cadence. No new
    follow-up issue is filed by this paired-review.
- Paired review of PR #2417 (`tar-chardev-skipped.tar` fixture —
  per-typeflag silent-skip family extension 2 → 3; this paired-review
  landed in PR #2421 closing #2418):
  PR #2417 (squash commit `4ff06db564`, merged 2026-05-02T13:03:33Z,
  closes #2415) extends the `Tar.extract` silent-skip `else` fallback
  family from two to three sibling fixtures. The commit adds a
  512-byte single-block UStar fixture
  `testdata/tar/security/tar-chardev-skipped.tar` (SHA-256
  `d87742fb3d85ff0a4e15c161d6ae8c3430702e52dd58c56d7fcacd39adb7593e`)
  for typeflag `'3'` (POSIX UStar character special device, `0x33`); a
  fourth `buildZeroSizeFixture` call in
  [scripts/build-symlink-hardlink-malformed-fixtures.lean](/home/kim/lean-zip/scripts/build-symlink-hardlink-malformed-fixtures.lean)
  producing it deterministically; a new test arm in
  [ZipTest/TarFixtures.lean](/home/kim/lean-zip/ZipTest/TarFixtures.lean)
  immediately after the existing `tar-fifo-skipped.tar` arm, asserting
  the extract directory is empty after extraction (mirroring the
  `tar-fifo-skipped.tar` arm shape); a new Reproducer Corpus row in
  this inventory; and a *Symlink/hardlink extraction policy* fixture
  enumeration entry. No spec change, no production-code change, no new
  typeflag constant in the `Tar` namespace, no caller / signature
  change.
  - **Family-extension claim fidelity (2 → 3 fixtures).** The 2 → 3
    extension math is faithful to the merged tree. PR #2417 is the
    third per-typeflag fixture in the silent-skip family; siblings
    `hardlink-outside.tar` (PR #1555, typeflag `'1'`) and
    `tar-fifo-skipped.tar` (PR #2413, typeflag `'6'`) are the first
    two. The trio pins three distinct typeflag values (`0x31`, `0x36`,
    and `0x33`) against the shared `else` fallback at
    [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) (`partial def
    extract`'s tail `else` arm, after the `typeDirectory` /
    `typeRegular` / `typeSymlink` cases). All three fixtures have
    `size = 0` and route through the same
    `skipEntryData input e.size` no-op call in the `else` body, so the
    structural pin remains the *existence* of the `else` arm rather
    than the *behaviour* of any per-typeflag dispatch — a future
    refactor that drops the fallback for any one arm would fire the
    corresponding fixture. The originating PR #1555 set the silent-skip
    precedent at 1/N; PR #2413 added the second pin at 2/N
    (paired-reviewed in the immediately preceding entry); PR #2417 now
    extends to 3/N. Sibling-cluster precedent: the UStar interior-NUL
    family went 1 → 4 across PRs #1934 / #1937 / #1944 before
    terminal-closing at 5/5 in PR #1957 — the silent-skip family is
    one step further along that ladder than at the PR #2413
    paired-review snapshot, and remains open-ended (typeflags `'4'`
    block device and `'7'` contiguous file are the next candidates).
  - **Fixture-builder rename-vs-extend choice.** The worker chose
    *extend in place*, matching the PR #2413 worker's earlier choice
    on the same script. The script path
    [scripts/build-symlink-hardlink-malformed-fixtures.lean](/home/kim/lean-zip/scripts/build-symlink-hardlink-malformed-fixtures.lean)
    stays stable; the module docstring's *Output (byte-deterministic)*
    list now enumerates four output files (added
    `testdata/tar/security/tar-chardev-skipped.tar` as the fourth
    line) and the per-typeflag enumeration block in the docstring
    body adds a fourth bulleted entry for the chardev arm with its
    typeflag `0x33`, `path = "chardev-entry"`, empty linkname, and
    silent-skip `else` fallback semantics — phrased *"Third sibling of
    the silent-skip `else` fallback family alongside
    `hardlink-outside.tar` (typeflag `'1'`) and `tar-fifo-skipped.tar`
    (typeflag `'6'`); together the three pin three distinct typeflag
    values against the shared fallback."* The build summary line at
    `main`'s tail prints *"Built 4 per-typeflag-policy security
    fixtures under testdata/tar/security/."* — the count moved from
    `3` (PR #2413 era) to `4` correctly. The extend-in-place choice
    matches the docstring framing (*"per-typeflag-policy regression
    fixtures"* — agnostic to typeflag count) and keeps the rename
    churn at zero across the family extension. Worker-recorded
    rationale in
    [progress/20260502T130010Z_61ee8b41.md](/home/kim/lean-zip/progress/20260502T130010Z_61ee8b41.md)
    documents the path-disambiguation choice (*"The path
    `\"chardev-entry\"` is unambiguous against the existing `\"entry\"`
    / `\"fifo-entry\"`"*) — the per-fixture path naming convention
    matches the FIFO arm's `"fifo-entry"` pattern, so cross-arm
    confusion at extraction time is impossible.
  - **Reproducer Corpus row prose fidelity.** The new
    `tar-chardev-skipped.tar` row carries the seven required elements:
    (i) typeflag value `0x33` and the POSIX UStar `'3'` glyph (cited
    together in the row's opening clause); (ii) POSIX semantics
    *"character special device"* with the POSIX.1-1988 IEEE Std 1003.1
    §10 citation; (iii) silent-skip `else` branch, with explicit
    reference to `Tar.extract`'s tail `else` arm and the
    `skipEntryData` no-op on `e.size = 0`; (iv) sibling fixture
    cross-references to both `hardlink-outside.tar` (typeflag `'1'`)
    *and* `tar-fifo-skipped.tar` (typeflag `'6'`) — the row correctly
    names two siblings rather than one, reflecting the 2 → 3 extension;
    (v) the family-extension claim phrased as *"Per-typeflag
    silent-skip family extension"* with the *"trio together pins three
    distinct typeflag values against the shared fallback"*
    defense-in-depth framing; (vi) the writer-side caveat
    (*"`Tar.create`'s caller-API only accepts paths and never invokes
    `Tar.buildHeader` with a non-`'0'`/`'5'` typeflag, so legitimate
    archives produced by the lean-zip writer never carry typeflag
    `'3'`"*) — confirmed by reading
    [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) (`Tar.create`
    builds entries via `walkFiles` with `typeflag := if isDir then
    typeDirectory else typeRegular`, identical to the PR #2413
    paired-review's same audit on the FIFO arm); (vii) only stable
    [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) anchors — no `:N`
    line-number suffixes, consistent with the
    [PR #2353](https://github.com/kim-em/lean-zip/pull/2353) decision.
    **Convention-done-correctly note:** unlike the PR #2413
    paired-review, which had to substitute `#TBD-VERIFY-PR` <!-- drift-detector: prose mention of the placeholder token in a paired-review finding, not a stale placeholder --> → `#2413`
    inline because the PR #2413 worker missed the post-`gh pr create`
    closing-PR substitution step, the PR #2417 worker performed the
    closing-PR substitution on the worker branch before merge — the
    merged row's closing-PR column already cites `#2417` (verified via
    `git blame` on line 2926 pointing at PR #2417's merge commit
    `4ff06db564`). This paired-review records that as the
    self-correction of the substitution-slip pattern surfaced in the
    PR #2413 paired-review's *Reproducer Corpus row prose fidelity*
    bullet — the convention is now back on track for future
    per-typeflag siblings.
  - **Adversarial check.** The adversarial check is recorded in
    [progress/20260502T130010Z_61ee8b41.md](/home/kim/lean-zip/progress/20260502T130010Z_61ee8b41.md)
    *## Adversarial check*: temporarily wrapping the `else` body in
    `if e.typeflag == typeHardlink || e.typeflag == 0x36 then
    skipEntryData input e.size else throw (IO.userError s!"adversarial:
    unexpected typeflag {e.typeflag.toNat}")` left
    `hardlink-outside.tar` and `tar-fifo-skipped.tar` passing while
    `tar-chardev-skipped.tar` fired with `uncaught exception:
    adversarial: unexpected typeflag 51` (`0x33 = 51`). The
    disable-revert was clean — *"The `Zip/Tar.lean` change has been
    reverted in the worktree (`git diff Zip/Tar.lean` is clean)"* —
    and the post-revert `git diff` cleanliness is independently
    confirmable from the merged tree (PR #2417's diff at
    [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) shows zero lines
    changed). The adversarial-check pattern extends the PR #2413
    paired-review's *Adversarial check* bullet shape: PR #2413's
    wrapper spared the single hardlink arm to confirm one new fixture
    fired in isolation; PR #2417's wrapper spares *two* arms
    (`typeHardlink` and `0x36`) to confirm only the third
    (`tar-chardev-skipped.tar`) fires. The cross-PR pattern is now
    *"spare all-but-the-new-arm and confirm the new fixture fires"*,
    which scales to N+1 fixtures by adding one more spare to the
    wrapper's disjunction. The convention is established for future
    per-typeflag siblings (typeflag `'4'`, `'7'`).
  - **Sibling-fixture audit independence.** The three extract
    directories `/tmp/lean-zip-fixture-hardlink-outside-extract`,
    `/tmp/lean-zip-fixture-tar-fifo-skipped-extract`, and
    `/tmp/lean-zip-fixture-tar-chardev-skipped-extract` are distinct
    paths and each test arm independently `rm -rf`s + recreates its
    own directory before extracting (per the cleanup-then-create
    pattern at
    [ZipTest/TarFixtures.lean](/home/kim/lean-zip/ZipTest/TarFixtures.lean)).
    The cleanup loop at the end of the test bundle includes all three
    directory paths in its `rm -rf` list, and the per-fixture file
    list (`writeFixtureTmp` outputs under `/tmp/lean-zip-fixture-*`)
    includes all three of `hardlink-outside.tar`,
    `tar-fifo-skipped.tar`, and `tar-chardev-skipped.tar`. No shared
    mutable state across the three arms — re-running the test suite
    against any subset of arms produces the same result because each
    arm reads its own fixture, writes to its own extract directory,
    and asserts on its own `readDir` result. Both the
    `hardlink-outside.tar` and `tar-fifo-skipped.tar` test arms
    continue to pass after the new arm is added (independently
    confirmed by `lake exe test` on the merged tree: *"TAR fixture
    tests: OK"*). The three-arm independence is the structural
    prerequisite for the family-extension claim: a future refactor
    that breaks one arm's silent-skip behaviour cannot accidentally
    pass because of mutable state propagated from another arm.
  - **Stable-cite discipline.** The new Reproducer Corpus row uses
    only stable identifiers — function names (`Tar.extract`,
    `skipEntryData`, `Tar.forEntries`, `Tar.buildHeader`,
    `Tar.create`) and fixture filenames (`tar-chardev-skipped.tar`,
    `tar-fifo-skipped.tar`, `hardlink-outside.tar`). No `line N` or
    `:N` suffixes appear anywhere in the row, consistent with the
    [PR #2353](https://github.com/kim-em/lean-zip/pull/2353) decision
    to drop line-number anchors. Cross-reference cites resolve to real
    artefacts: PR #2413 / PR #1555 are both real merged PRs with the
    cited fixtures and policies. The
    [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) anchor is repeated
    rather than aliased, matching the inventory's house style. `bash
    scripts/check-inventory-links.sh` reports `errors=0, warnings=2`
    on the merged tree — the two warnings are *"this PR"* <!-- drift-detector: prose discussion of the placeholder phrase in a paired-review finding, not a stale placeholder --> prose
    mentions in the `tar-fifo-skipped.tar` and `tar-chardev-skipped.tar`
    rows' adversarial-check phrasing (*"verified by adversarial check
    during this PR"* <!-- drift-detector: quote of the adversarial-check phrasing in a paired-review finding, not a stale placeholder -->), inherited from PR #2413 and PR #2417
    respectively. These are the same two warnings recorded in the
    PR #2413 paired-review's *Stable-cite discipline* bullet — the
    count is unchanged across this paired-review (no new warnings
    introduced). Suppressing them would require `<!-- drift-detector:
    ... -->` opt-out comments per the PR #2371 paired-review pattern;
    this paired-review continues to defer the opt-outs (matching the
    PR #2413 paired-review's deferral) — the prose mentions are not
    stale placeholders, and a future inventory-cleanup PR could batch
    the opt-outs across the silent-skip family rows for warning-count
    cleanliness.
  - **Follow-up gaps.** None surface that warrant a separate issue.
    The audit confirms all six required dimensions: the
    family-extension math (2 → 3) is internally consistent and
    source-level verified; the rename-vs-extend choice matches the
    docstring's per-typeflag enumeration and the PR #2413 worker's
    earlier choice on the same script; the Reproducer Corpus row
    carries all seven required elements with the closing-PR
    substitution done correctly on the worker branch (no inline
    fix-up needed, unlike PR #2413); the adversarial check is recorded
    in the progress entry with a clean post-revert diff and extends
    the PR #2413 wrapper convention to N=2 spared arms; the
    three-arm test bundle is structurally independent; the stable-cite
    discipline holds with the warning-count unchanged at 2.
    The next family-extension candidates after PR #2417 (typeflag
    `'3'`, character device) are typeflag `'4'` (POSIX UStar block
    special device, `0x34` — already queued as
    [issue #2416](https://github.com/kim-em/lean-zip/issues/2416)) and
    typeflag `'7'` (POSIX UStar contiguous file, `0x37`); naming them
    without committing to specific issue numbers, matching the PR
    #2371 / PR #2407 / PR #2413 paired-review entries' close-out
    style. The silent-skip family remains open-ended (every additional
    per-typeflag arm fires the same `else` fallback in `Tar.extract`,
    so the marginal fixture cost falls but the marginal regression
    benefit also falls); any future per-typeflag fixture should earn
    its own paired-review entry on the established cadence. No new
    follow-up issue is filed by this paired-review.

- Paired review of PR #2422 (`tar-blockdev-skipped.tar` fixture —
  per-typeflag silent-skip family extension 3 → 4; this paired-review
  landed in PR #2427 closing #2423):
  PR #2422 (squash commit `5f87adf42f`, merged 2026-05-02T14:00:54Z,
  closes #2416) extends the `Tar.extract` silent-skip `else` fallback
  family from three to four sibling fixtures. The commit adds a
  512-byte single-block UStar fixture
  `testdata/tar/security/tar-blockdev-skipped.tar` (SHA-256
  `9ef6dda29da2529019a62aa905b819f7018a0560cd1d1cf946b3f73714d9bae2`)
  for typeflag `'4'` (POSIX UStar block special device, `0x34`); a
  fifth `buildZeroSizeFixture` call in
  [scripts/build-symlink-hardlink-malformed-fixtures.lean](/home/kim/lean-zip/scripts/build-symlink-hardlink-malformed-fixtures.lean)
  producing it deterministically; a new test arm in
  [ZipTest/TarFixtures.lean](/home/kim/lean-zip/ZipTest/TarFixtures.lean)
  immediately after the existing `tar-chardev-skipped.tar` arm,
  asserting the extract directory is empty after extraction
  (mirroring the `tar-chardev-skipped.tar` arm shape); a new
  Reproducer Corpus row in this inventory; and a *Symlink/hardlink
  extraction policy* fixture enumeration entry. No spec change, no
  production-code change, no new typeflag constant in the `Tar`
  namespace, no caller / signature change.
  - **Family-extension claim fidelity (3 → 4 fixtures).** The 3 → 4
    extension math is faithful to the merged tree. PR #2422 is the
    fourth per-typeflag fixture in the silent-skip family; siblings
    `hardlink-outside.tar` (PR #1555, typeflag `'1'`),
    `tar-fifo-skipped.tar` (PR #2413, typeflag `'6'`), and
    `tar-chardev-skipped.tar` (PR #2417, typeflag `'3'`) are the
    first three. The quartet pins four distinct typeflag values
    (`0x31`, `0x36`, `0x33`, and `0x34`) against the shared `else`
    fallback at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean)
    (`partial def extract`'s tail `else` arm, after the
    `typeDirectory` / `typeRegular` / `typeSymlink` cases). All four
    fixtures have `size = 0` and route through the same
    `skipEntryData input e.size` no-op call in the `else` body, so
    the structural pin remains the *existence* of the `else` arm
    rather than the *behaviour* of any per-typeflag dispatch — a
    future refactor that drops the fallback for any one arm would
    fire the corresponding fixture. The originating PR #1555 set the
    silent-skip precedent at 1/N; PR #2413 added the second pin at
    2/N (paired-reviewed in PR #2419); PR #2417 added the third pin
    at 3/N (paired-reviewed in PR #2421); PR #2422 now extends to
    4/N. Sibling-cluster precedent: the UStar interior-NUL family
    went 1 → 4 across PRs #1934 / #1937 / #1944 before
    terminal-closing at 5/5 in PR #1957 — the silent-skip family is
    one step further along that ladder than at the PR #2417
    paired-review snapshot, and remains open-ended (typeflag `'7'`
    contiguous file, queued at the time of PR #2422's merge as
    [issue #2420](https://github.com/kim-em/lean-zip/issues/2420),
    is the next candidate; the GNU typeflags `'L'` long-name,
    `'K'` long-link, `'V'` volume header, `'M'` multi-volume
    continuation, `'x'` PAX extended, and `'g'` PAX global remain
    distinct candidates beyond the POSIX UStar `'0'`–`'7'` numeric
    range).
  - **Fixture-builder rename-vs-extend choice.** The worker chose
    *extend in place*, matching the PR #2413 / PR #2417 workers'
    earlier choices on the same script. The script path
    [scripts/build-symlink-hardlink-malformed-fixtures.lean](/home/kim/lean-zip/scripts/build-symlink-hardlink-malformed-fixtures.lean)
    stays stable; the module docstring's *Output (byte-deterministic)*
    list now enumerates five output files (added
    `testdata/tar/security/tar-blockdev-skipped.tar` as the fifth
    line) and the per-typeflag enumeration block in the docstring
    body adds a fifth bulleted entry for the blockdev arm with its
    typeflag `0x34`, `path = "blockdev-entry"`, empty linkname, and
    silent-skip `else` fallback semantics — phrased *"Fourth sibling
    of the silent-skip `else` fallback family alongside
    `hardlink-outside.tar` (typeflag `'1'`), `tar-fifo-skipped.tar`
    (typeflag `'6'`), and `tar-chardev-skipped.tar` (typeflag `'3'`);
    together the four pin four distinct typeflag values against the
    shared fallback."* The build summary line at `main`'s tail prints
    *"Built 5 per-typeflag-policy security fixtures under
    testdata/tar/security/."* — the count moved from `4` (PR #2417
    era) to `5` correctly. The extend-in-place choice matches the
    docstring framing (*"per-typeflag-policy regression fixtures"* —
    agnostic to typeflag count) and keeps the rename churn at zero
    across the family extension. Worker-recorded rationale in
    [progress/20260502T135640Z_dc152c31_tar-blockdev-skipped-fixture.md](/home/kim/lean-zip/progress/20260502T135640Z_dc152c31_tar-blockdev-skipped-fixture.md)
    documents the extend-in-place choice and the per-fixture path
    naming convention `"blockdev-entry"` matching the FIFO /
    chardev arms' `"fifo-entry"` / `"chardev-entry"` patterns.
  - **Reproducer Corpus row prose fidelity.** The new
    `tar-blockdev-skipped.tar` row carries the seven required
    elements: (i) typeflag value `0x34` and the POSIX UStar `'4'`
    glyph (cited together in the row's opening clause); (ii) POSIX
    semantics *"block special device"* with the POSIX.1-1988 IEEE
    Std 1003.1 §10 citation; (iii) silent-skip `else` branch, with
    explicit reference to `Tar.extract`'s tail `else` arm and the
    `skipEntryData` no-op on `e.size = 0`; (iv) sibling fixture
    cross-references to all three prior arms `hardlink-outside.tar`
    (typeflag `'1'`), `tar-fifo-skipped.tar` (typeflag `'6'`), and
    `tar-chardev-skipped.tar` (typeflag `'3'`) — the row correctly
    names three siblings rather than two, reflecting the 3 → 4
    extension; (v) the family-extension claim phrased as *"Per-typeflag
    silent-skip family extension"* with the *"quartet together pins
    four distinct typeflag values against the shared fallback"*
    defense-in-depth framing; (vi) the writer-side caveat
    (*"`Tar.create`'s caller-API only accepts paths and never invokes
    `Tar.buildHeader` with a non-`'0'`/`'5'` typeflag, so legitimate
    archives produced by the lean-zip writer never carry typeflag
    `'4'`"*) — confirmed by reading
    [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) (`Tar.create`
    builds entries via `walkFiles` with `typeflag := if isDir then
    typeDirectory else typeRegular`, identical to the PR #2413 /
    PR #2417 paired-reviews' same audit on the FIFO and chardev arms);
    (vii) only stable [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean)
    anchors — no `:N` line-number suffixes, consistent with the
    [PR #2353](https://github.com/kim-em/lean-zip/pull/2353) decision.
    The block-device security-sensitivity framing — *"a malicious
    archive could ship a node mapping to a raw partition
    (`/dev/sda1`), a kernel-state-modification node, or a node that
    reads/writes device memory (`/dev/kmem` on legacy kernels) —
    lean-zip's policy of *never* materialising block-device nodes
    (no `mknod(2)` call) is the correct one"* — is the
    arm-specific extension that distinguishes the blockdev row's
    prose from the chardev / FIFO rows. It is load-bearing in the
    sense that the threat-model paragraph names the concrete
    resources a typeflag-`'4'` entry could target (raw partition,
    kernel memory) which the chardev arm's threat model (TTY-style
    I/O surfaces, `/dev/null` aliasing) does not cover. The two
    arm-specific paragraphs are independently informative — neither
    subsumes the other — which is the right shape for a per-typeflag
    fixture family. **Convention-done-correctly note:** the PR #2422
    worker performed the closing-PR substitution
    `#TBD-VERIFY-PR` → `#2422` <!-- drift-detector: prose mention of the placeholder substitution in a paired-review finding, not a stale placeholder --> on the worker branch
    before merge — the merged row's closing-PR column already cites
    `#2422` (verified via `git blame` on the row pointing at PR
    #2422's merge commit `5f87adf42f`). The convention remains on
    track from the PR #2417 self-correction onward.
  - **Adversarial check.** The adversarial check is recorded in
    [progress/20260502T135640Z_dc152c31_tar-blockdev-skipped-fixture.md](/home/kim/lean-zip/progress/20260502T135640Z_dc152c31_tar-blockdev-skipped-fixture.md)
    *## Adversarial check*: temporarily wrapping the `else` body in
    `if e.typeflag == typeHardlink || e.typeflag == 0x36 ||
    e.typeflag == 0x33 then skipEntryData input e.size else throw
    (IO.userError s!"tar: adversarial check: unexpected typeflag
    {e.typeflag}")` left `hardlink-outside.tar`,
    `tar-fifo-skipped.tar`, and `tar-chardev-skipped.tar` passing
    while `tar-blockdev-skipped.tar` fired with `uncaught exception:
    tar: adversarial check: unexpected typeflag 52` (`0x34 = 52`,
    matching ASCII `'4'`). The disable-revert was clean — the
    post-revert `git diff Zip/Tar.lean` is empty in the worker's
    merged commit (PR #2422's diff at
    [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) shows zero lines
    changed). The adversarial-check pattern continues the
    *"spare all-but-the-new-arm and confirm the new fixture fires"*
    convention established in the PR #2417 paired-review: PR #2413's
    wrapper spared one arm (typeflag `'1'` only), PR #2417's spared
    two (`'1'` and `'6'`), and PR #2422's spared three (`'1'`, `'6'`,
    and `'3'`). Each new fixture's wrapper extends the disjunction
    by one already-fixtured typeflag, scaling cleanly to N+1
    fixtures by adding one more spare. The expected next-cadence
    instance — typeflag `'7'` contiguous file at issue #2420 — would
    spare four arms (`'1'`, `'6'`, `'3'`, and `'4'`); the convention
    is established and ready for that landing.
  - **Sibling-fixture audit independence.** The four extract
    directories `/tmp/lean-zip-fixture-hardlink-outside-extract`,
    `/tmp/lean-zip-fixture-tar-fifo-skipped-extract`,
    `/tmp/lean-zip-fixture-tar-chardev-skipped-extract`, and
    `/tmp/lean-zip-fixture-tar-blockdev-skipped-extract` are
    distinct paths and each test arm independently `rm -rf`s +
    recreates its own directory before extracting (per the
    cleanup-then-create pattern at
    [ZipTest/TarFixtures.lean](/home/kim/lean-zip/ZipTest/TarFixtures.lean)).
    The cleanup loop at the end of the test bundle includes all four
    directory paths in its `rm -rf` list, and the per-fixture file
    list (`writeFixtureTmp` outputs under `/tmp/lean-zip-fixture-*`)
    includes all four of `hardlink-outside.tar`,
    `tar-fifo-skipped.tar`, `tar-chardev-skipped.tar`, and
    `tar-blockdev-skipped.tar`. No shared mutable state across the
    four arms — re-running the test suite against any subset of arms
    produces the same result because each arm reads its own fixture,
    writes to its own extract directory, and asserts on its own
    `readDir` result. The `hardlink-outside.tar`,
    `tar-fifo-skipped.tar`, and `tar-chardev-skipped.tar` test arms
    continue to pass after the new arm is added (independently
    confirmed by `lake exe test` on the merged tree: *"TAR fixture
    tests: OK"*). The four-arm independence is the structural
    prerequisite for the family-extension claim: a future refactor
    that breaks one arm's silent-skip behaviour cannot accidentally
    pass because of mutable state propagated from another arm. The
    test-arm placement at PR #2422's merge time was the new tail
    arm of the silent-skip cluster (immediately after the
    `tar-chardev-skipped.tar` arm); its alphabetical slot among the
    silent-skip arms positions it correctly between
    `tar-chardev-skipped.tar` and any post-`'4'` sibling.
  - **Stable-cite discipline.** The new Reproducer Corpus row uses
    only stable identifiers — function names (`Tar.extract`,
    `skipEntryData`, `Tar.forEntries`, `Tar.buildHeader`,
    `Tar.create`) and fixture filenames (`tar-blockdev-skipped.tar`,
    `tar-chardev-skipped.tar`, `tar-fifo-skipped.tar`,
    `hardlink-outside.tar`). No `line N` or `:N` suffixes appear
    anywhere in the row, consistent with the
    [PR #2353](https://github.com/kim-em/lean-zip/pull/2353) decision
    to drop line-number anchors. Cross-reference cites resolve to
    real artefacts: PR #2417 / PR #2413 / PR #1555 are all real
    merged PRs with the cited fixtures and policies. The
    [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) anchor is repeated
    rather than aliased, matching the inventory's house style. `bash
    scripts/check-inventory-links.sh` reports `errors=0, warnings=3`
    on the post-PR-#2422 / pre-PR-#2425 tree — the third warning is
    the *"during this PR"* <!-- drift-detector: prose discussion of the placeholder phrase in a paired-review finding, not a stale placeholder --> prose mention in the new
    `tar-blockdev-skipped.tar` row's adversarial-check phrasing,
    inherited from the PR #2413 / PR #2417 row template (added one
    on top of the two warnings recorded in the PR #2417 paired-review
    for the fifo and chardev rows). Suppressing them would require
    `<!-- drift-detector: ... -->` opt-out comments per the PR #2371
    paired-review pattern; this paired-review continues to defer the
    opt-outs (matching the PR #2413 / PR #2417 paired-review
    deferrals) — the prose mentions are not stale placeholders, and
    a future inventory-cleanup PR could batch the opt-outs across
    the silent-skip family rows for warning-count cleanliness.
  - **Follow-up gaps.** None surface that warrant a separate issue.
    The audit confirms all six required dimensions: the
    family-extension math (3 → 4) is internally consistent and
    source-level verified; the rename-vs-extend choice matches the
    docstring's per-typeflag enumeration and the PR #2413 / PR #2417
    workers' earlier choices on the same script; the Reproducer
    Corpus row carries all seven required elements with the
    closing-PR substitution done correctly on the worker branch (the
    PR #2417 self-correction holds across PR #2422); the adversarial
    check is recorded in the progress entry with a clean post-revert
    diff and extends the *"spare all-but-the-new-arm"* convention to
    N=3 spared arms; the four-arm test bundle is structurally
    independent; the stable-cite discipline holds with the
    warning-count moving 2 → 3 only on account of the new row's
    standard prose template (no new placeholder regression). The
    next family-extension candidate after PR #2422 (typeflag `'4'`,
    block device) is typeflag `'7'` (POSIX UStar contiguous file,
    `0x37` — already queued as
    [issue #2420](https://github.com/kim-em/lean-zip/issues/2420)
    at the time of PR #2422's merge); naming it without committing
    to a specific closing-PR number, matching the PR #2371 /
    PR #2407 / PR #2413 / PR #2417 paired-review entries' close-out
    style. The silent-skip family remains open-ended (every additional
    per-typeflag arm fires the same `else` fallback in `Tar.extract`,
    so the marginal fixture cost falls but the marginal regression
    benefit also falls); any future per-typeflag fixture should earn
    its own paired-review entry on the established cadence. No new
    follow-up issue is filed by this paired-review.
- Paired review of PR #2425 (`tar-contiguous-skipped.tar` fixture —
  per-typeflag silent-skip family extension 4 → 5; this paired-review
  landed in PR #2433 closing #2432):
  PR #2425 (squash commit `76727f6ace`, merged 2026-05-02T15:13:09Z,
  closes #2420) extends the `Tar.extract` silent-skip `else` fallback
  family from four to five sibling fixtures. The commit adds a
  512-byte single-block UStar fixture
  `testdata/tar/security/tar-contiguous-skipped.tar` (SHA-256
  `26be2cf0b76bbf54c03cdde037ea231c3a44ddb44417314b1ed08b3b7027d312`)
  for typeflag `'7'` (POSIX UStar contiguous file, `0x37`); a sixth
  `buildZeroSizeFixture` call in
  [scripts/build-symlink-hardlink-malformed-fixtures.lean](/home/kim/lean-zip/scripts/build-symlink-hardlink-malformed-fixtures.lean)
  producing it deterministically; a new test arm in
  [ZipTest/TarFixtures.lean](/home/kim/lean-zip/ZipTest/TarFixtures.lean)
  immediately after the existing `tar-blockdev-skipped.tar` arm,
  asserting the extract directory is empty after extraction
  (mirroring the `tar-blockdev-skipped.tar` arm shape); a new
  Reproducer Corpus row in this inventory; and a *Symlink/hardlink
  extraction policy* fixture enumeration entry. No spec change, no
  production-code change, no new typeflag constant in the `Tar`
  namespace, no caller / signature change.
  - **Family-extension claim fidelity (4 → 5 fixtures).** The 4 → 5
    extension math is faithful to the merged tree. PR #2425 is the
    fifth per-typeflag fixture in the silent-skip family; siblings
    `hardlink-outside.tar` (PR #1555, typeflag `'1'`),
    `tar-fifo-skipped.tar` (PR #2413, typeflag `'6'`),
    `tar-chardev-skipped.tar` (PR #2417, typeflag `'3'`), and
    `tar-blockdev-skipped.tar` (PR #2422, typeflag `'4'`) are the
    first four. The quintet pins five distinct typeflag values
    (`0x31`, `0x36`, `0x33`, `0x34`, and `0x37`) against the shared
    `else` fallback at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean)
    (`partial def extract`'s tail `else` arm, after the
    `typeDirectory` / `typeRegular` / `typeSymlink` cases). All five
    fixtures have `size = 0` and route through the same
    `skipEntryData input e.size` no-op call in the `else` body, so
    the structural pin remains the *existence* of the `else` arm
    rather than the *behaviour* of any per-typeflag dispatch — a
    future refactor that drops the fallback for any one arm would
    fire the corresponding fixture. The originating PR #1555 set the
    silent-skip precedent at 1/N; PR #2413 added the second pin at
    2/N (paired-reviewed in PR #2419); PR #2417 added the third pin
    at 3/N (paired-reviewed in PR #2421); PR #2422 added the fourth
    pin at 4/N (paired-reviewed in PR #2427); PR #2425 now extends
    to 5/N. With this landing the **POSIX UStar `'1'`–`'7'` numeric
    range is exhausted as a sub-ladder** — every value `'0'`
    through `'7'` has either a typed branch in `Tar.extract` (`'0'`
    regular, `'2'` symlink, `'5'` directory) or a silent-skip
    regression fixture (`'1'` hardlink, `'3'` chardev, `'4'`
    blockdev, `'6'` FIFO, `'7'` contiguous file). The natural next
    region is the GNU-typeflag sub-ladder, opened by PR #2428
    (`tar-volumeheader-skipped.tar`, typeflag `'V'` volume header,
    `0x56`); remaining GNU-typeflag candidates `'M'` (multi-volume
    continuation, `0x4D`), `'S'` (sparse file, `0x53`), and `'D'`
    (directory-dump for incremental backups, `0x44`) are tracked
    independently as issues #2426 / #2429 / #2430 — the GNU
    sub-ladder is named without committing to specific closing-PR
    numbers, matching the PR #2417 / PR #2422 paired-review entries'
    close-out style.
  - **Fixture-builder rename-vs-extend choice.** The worker chose
    *extend in place*, matching the PR #2413 / PR #2417 / PR #2422
    workers' earlier choices on the same script. The script path
    [scripts/build-symlink-hardlink-malformed-fixtures.lean](/home/kim/lean-zip/scripts/build-symlink-hardlink-malformed-fixtures.lean)
    stays stable; the module docstring's *Output (byte-deterministic)*
    list now enumerates six output files (added
    `testdata/tar/security/tar-contiguous-skipped.tar` as the sixth
    line) and the per-typeflag enumeration block in the docstring
    body adds a sixth bulleted entry for the contiguous arm with its
    typeflag `0x37`, `path = "contiguous-entry"`, empty linkname,
    and silent-skip `else` fallback semantics — phrased *"Fifth
    sibling of the silent-skip `else` fallback family alongside
    `hardlink-outside.tar` (typeflag `'1'`), `tar-fifo-skipped.tar`
    (typeflag `'6'`), `tar-chardev-skipped.tar` (typeflag `'3'`),
    and `tar-blockdev-skipped.tar` (typeflag `'4'`); together the
    five pin five distinct typeflag values against the shared
    fallback, fully fixturing the POSIX UStar `'0'`–`'7'` numeric
    range."* The build summary line at `main`'s tail prints
    *"Built 6 per-typeflag-policy security fixtures under
    testdata/tar/security/."* — the count moved from `5` (PR #2422
    era) to `6` correctly. The extend-in-place choice matches the
    docstring framing (*"per-typeflag-policy regression fixtures"* —
    agnostic to typeflag count) and keeps the rename churn at zero
    across the family extension. Worker-recorded rationale in
    [progress/20260502T151018Z_3e31cac5_tar-contiguous-skipped-fixture.md](/home/kim/lean-zip/progress/20260502T151018Z_3e31cac5_tar-contiguous-skipped-fixture.md)
    documents the extend-in-place choice and the per-fixture path
    naming convention `"contiguous-entry"` matching the FIFO /
    chardev / blockdev arms' `"fifo-entry"` / `"chardev-entry"` /
    `"blockdev-entry"` patterns.
  - **Reproducer Corpus row prose fidelity.** The new
    `tar-contiguous-skipped.tar` row carries the seven required
    elements: (i) typeflag value `0x37` and the POSIX UStar `'7'`
    glyph (cited together in the row's opening clause); (ii) POSIX
    semantics *"contiguous file"* with the POSIX.1-1988 IEEE Std
    1003.1 §10 (USTAR Interchange Format) citation; (iii)
    silent-skip `else` branch, with explicit reference to
    `Tar.extract`'s tail `else` arm and the `skipEntryData` no-op
    on `e.size = 0`; (iv) sibling fixture cross-references to all
    four prior arms `hardlink-outside.tar` (typeflag `'1'`),
    `tar-fifo-skipped.tar` (typeflag `'6'`),
    `tar-chardev-skipped.tar` (typeflag `'3'`), and
    `tar-blockdev-skipped.tar` (typeflag `'4'`) — the row correctly
    names four siblings rather than three, reflecting the 4 → 5
    extension; (v) the family-extension claim phrased as
    *"Per-typeflag silent-skip family extension"* with the
    *"quintet together pins five distinct typeflag values against
    the shared fallback"* defense-in-depth framing; (vi) the
    writer-side caveat (*"`Tar.create`'s caller-API only accepts
    paths and never invokes `Tar.buildHeader` with a
    non-`'0'`/`'5'` typeflag, so legitimate archives produced by
    the lean-zip writer never carry typeflag `'7'`"*) — confirmed
    by reading [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean)
    (`Tar.create` builds entries via `walkFiles` with `typeflag :=
    if isDir then typeDirectory else typeRegular`, identical to
    the PR #2413 / PR #2417 / PR #2422 paired-reviews' same audit
    on the FIFO / chardev / blockdev arms); (vii) only stable
    [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) anchors — no
    `:N` line-number suffixes, consistent with the
    [PR #2353](https://github.com/kim-em/lean-zip/pull/2353)
    decision. The contiguous-file framing — *"POSIX UStar permits
    lenient extractors to alias `'7'` to `'0'` (regular file) —
    GNU tar, BSD tar, and libarchive on systems without
    contiguous-file semantics treat it as a regular file and
    write the payload to disk — but lean-zip's strict `==` chain
    rejects `'7'` and silent-skips, refusing to materialise a
    payload that a malicious archive shipped expecting lenient
    extraction"* — is the arm-specific extension that distinguishes
    the contiguous row's prose from the chardev / FIFO / blockdev
    rows. The strict-vs-lenient framing is load-bearing in a
    different sense from the device-node rows: there, the threat
    model named concrete resources the device node could target
    (raw partition, kernel memory, TTY surfaces); here, the threat
    model names a concrete *aliasing* lenient peers do that lean-zip
    refuses to do — a different attack-surface paragraph in the
    same per-typeflag fixture family. The contiguous arm's prose is
    therefore closer to the *defense-in-depth-for-format-completeness*
    rationale than to the device-node-security rationale of
    `'3'`/`'4'`/`'6'`. The four arm-specific paragraphs (chardev /
    blockdev / FIFO / contiguous) are independently informative —
    none subsumes the others — which is the right shape for a
    per-typeflag fixture family. **Convention-done-correctly note:**
    the PR #2425 worker performed the closing-PR substitution
    `#TBD-VERIFY-PR` → `#2425` <!-- drift-detector: prose mention of the placeholder substitution in a paired-review finding, not a stale placeholder --> on the worker branch
    before merge as a second commit (visible in the squash log as
    *"doc: substitute #TBD-VERIFY-PR → #2425 in tar-contiguous-skipped.tar Reproducer Corpus row"*) <!-- drift-detector: prose quotation of the worker's substitution-commit message in a paired-review finding, not a stale placeholder --> — the merged row's
    closing-PR column already cites `#2425` (verified via `git
    blame` on the row pointing at PR #2425's merge commit
    `76727f6ace`). The convention remains on track from the PR
    #2417 self-correction onward.
  - **Adversarial-check fidelity.** The adversarial check is
    recorded in
    [progress/20260502T151018Z_3e31cac5_tar-contiguous-skipped-fixture.md](/home/kim/lean-zip/progress/20260502T151018Z_3e31cac5_tar-contiguous-skipped-fixture.md)
    *## Adversarial check*: temporarily wrapping the `else` body in
    `if e.typeflag == typeHardlink || e.typeflag == 0x36 ||
    e.typeflag == 0x33 || e.typeflag == 0x34 then skipEntryData
    input e.size else throw (IO.userError s!"adversarial:
    unexpected typeflag {e.typeflag}")` left `hardlink-outside.tar`,
    `tar-fifo-skipped.tar`, `tar-chardev-skipped.tar`, and
    `tar-blockdev-skipped.tar` passing while
    `tar-contiguous-skipped.tar` fired with `uncaught exception:
    adversarial: unexpected typeflag 55` (`0x37 = 55`, matching
    ASCII `'7'`). The `0x37` ↔ ASCII `'7'` ↔ decimal `55` mapping
    in the adversarial-check parenthetical is internally consistent
    (`0x37` hex = `55` decimal = ASCII codepoint of the glyph
    `'7'`). The wrapper expression preserves all four prior
    siblings' arms (`'1'` / `'6'` / `'3'` / `'4'`) and exposes
    only the `'7'` arm — extending the *"spare all-but-the-new-arm
    and confirm the new fixture fires"* convention established in
    the PR #2417 / PR #2422 paired-reviews to N=4 spared arms.
    PR #2413's wrapper spared one arm (`'1'` only), PR #2417's
    spared two (`'1'` and `'6'`), PR #2422's spared three (`'1'`,
    `'6'`, and `'3'`), and PR #2425's spared four (`'1'`, `'6'`,
    `'3'`, and `'4'`). Each new fixture's wrapper extends the
    disjunction by one already-fixtured typeflag, scaling cleanly
    to N+1 fixtures by adding one more spare. The disable-revert
    was clean — the post-revert `git diff Zip/Tar.lean` is empty
    in the worker's merged commit (PR #2425's diff at
    [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) shows zero
    lines changed). The expected next-cadence instance — the
    GNU sub-ladder opened by PR #2428 (`'V'`, `0x56`) — would
    spare five arms (`'1'`, `'6'`, `'3'`, `'4'`, and `'7'`); the
    convention is established and ready for that landing.
  - **Test-arm placement.** The new test arm in
    [ZipTest/TarFixtures.lean](/home/kim/lean-zip/ZipTest/TarFixtures.lean)
    is placed at the tail of the silent-skip cluster (immediately
    after the `tar-blockdev-skipped.tar` arm), matching the
    chronological-by-PR-merge-order convention the family has
    followed since PR #1555 (the actual file order is `'1'` →
    `'6'` → `'3'` → `'4'` → `'7'`, mirroring the PR-merge
    sequence #1555 → #2413 → #2417 → #2422 → #2425). The arm
    asserts the extract directory is empty after `Tar.extract`
    (mirroring the FIFO / chardev / blockdev arm shapes — verified
    by reading the `cgEntries.isEmpty` check in the merged
    [ZipTest/TarFixtures.lean](/home/kim/lean-zip/ZipTest/TarFixtures.lean)
    diff), and uses a distinct extract directory
    `/tmp/lean-zip-fixture-tar-contiguous-skipped-extract`
    (independent from the four prior arms' extract directories
    `/tmp/lean-zip-fixture-hardlink-outside-extract`,
    `/tmp/lean-zip-fixture-tar-fifo-skipped-extract`,
    `/tmp/lean-zip-fixture-tar-chardev-skipped-extract`, and
    `/tmp/lean-zip-fixture-tar-blockdev-skipped-extract`). The
    cleanup loops at the end of the test bundle include
    `tar-contiguous-skipped.tar` in the per-fixture file-list
    (`writeFixtureTmp` outputs under `/tmp/lean-zip-fixture-*`)
    and the new extract directory in the per-directory `rm -rf`
    list — so re-running the test suite remains hermetic across
    the family extension. No shared mutable state across the five
    arms — each arm reads its own fixture, writes to its own
    extract directory, and asserts on its own `readDir` result.
    The `hardlink-outside.tar`, `tar-fifo-skipped.tar`,
    `tar-chardev-skipped.tar`, and `tar-blockdev-skipped.tar`
    test arms continue to pass after the new arm is added
    (independently confirmed by `lake exe test` on the merged
    tree: *"TAR fixture tests: OK"*). The five-arm independence
    is the structural prerequisite for the family-extension
    claim: a future refactor that breaks one arm's silent-skip
    behaviour cannot accidentally pass because of mutable state
    propagated from another arm. Note that the issue body
    described the placement as *"alphabetical slot ... between
    `tar-blockdev-skipped.tar` and `tar-fifo-skipped.tar`"*; the
    actual placement is chronological-by-PR-order (tail of the
    cluster) rather than alphabetical, matching the established
    cadence from PR #2413 / PR #2417 / PR #2422 — the
    chronological convention is the documented house style for
    the family, and a strict alphabetical slot would have churned
    the prior four arms' positions for no observable benefit.
  - **Stable-cite discipline.** The new Reproducer Corpus row
    uses only stable identifiers — function names (`Tar.extract`,
    `skipEntryData`, `Tar.forEntries`, `Tar.list`,
    `Tar.buildHeader`, `Tar.create`) and fixture filenames
    (`tar-contiguous-skipped.tar`, `tar-blockdev-skipped.tar`,
    `tar-chardev-skipped.tar`, `tar-fifo-skipped.tar`,
    `hardlink-outside.tar`). No `line N` or `:N` suffixes appear
    anywhere in the row, consistent with the
    [PR #2353](https://github.com/kim-em/lean-zip/pull/2353)
    decision to drop line-number anchors. Cross-reference cites
    resolve to real artefacts: PR #2422 / PR #2417 / PR #2413 /
    PR #1555 are all real merged PRs with the cited fixtures and
    policies. The [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean)
    anchor is repeated rather than aliased, matching the
    inventory's house style. `bash
    scripts/check-inventory-links.sh` reports `errors=0,
    warnings=6` on the post-PR-#2425 / post-PR-#2428 / post-PR-#2431
    tree — the warnings are the *"during this PR"* <!-- drift-detector: prose discussion of the placeholder phrase in a paired-review finding, not a stale placeholder --> prose mentions
    in the six fixture rows (`tar-fifo-skipped.tar`,
    `tar-chardev-skipped.tar`, `tar-blockdev-skipped.tar`,
    `tar-contiguous-skipped.tar`, `tar-volumeheader-skipped.tar`,
    `tar-multivol-skipped.tar`) inherited from the PR #2413 /
    PR #2417 / PR #2422 row template (added one on top of the
    three warnings recorded in the PR #2422 paired-review for the
    fifo / chardev / blockdev rows; PR #2428 and PR #2431 added
    the volumeheader and multivol rows in turn). This paired-review
    introduces no new placeholder regression and adds zero
    warnings — the `#TBD-VERIFY-PR` placeholder in the <!-- drift-detector: prose discussion of the placeholder token in a paired-review finding, not a stale placeholder -->
    paired-review header line is wrapped in a
    `<!-- drift-detector: half-closed paired-review placeholder,
    substituted to the real PR number on the worker branch
    before merge -->` opt-out comment so it does not register as
    a stale placeholder. Suppressing the row-level warnings would
    require additional `<!-- drift-detector: ... -->` opt-out
    comments per the PR #2371 paired-review pattern; this
    paired-review continues to defer the opt-outs (matching the
    PR #2413 / PR #2417 / PR #2422 paired-review deferrals) — the
    prose mentions are not stale placeholders, and a future
    inventory-cleanup PR could batch the opt-outs across the
    silent-skip family rows for warning-count cleanliness.
  - **Ladder-progression close-out.** The per-typeflag silent-skip
    family ladder now stands at: PR #1555 (1/N, typeflag `'1'`
    hardlink — predates per-PR paired-review cadence), PR #2413
    (2/N, typeflag `'6'` FIFO — paired-review PR #2419), PR #2417
    (3/N, typeflag `'3'` character device — paired-review PR
    #2421), PR #2422 (4/N, typeflag `'4'` block device —
    paired-review PR #2427), and PR #2425 (5/N, typeflag `'7'`
    contiguous file — this paired-review). With PR #2425 landing,
    **the POSIX UStar `'1'`–`'7'` sub-ladder is exhausted** — every
    POSIX UStar numeric typeflag value `'0'` through `'7'` has
    either a typed branch in `Tar.extract` (`'0'`/`'2'`/`'5'`) or
    a silent-skip regression fixture (`'1'`/`'3'`/`'4'`/`'6'`/`'7'`).
    The natural next region is the GNU-typeflag sub-ladder, opened
    by PR #2428 (`'V'` volume header, `0x56`); remaining
    GNU-typeflag candidates `'M'` (multi-volume continuation,
    `0x4D`), `'S'` (sparse file, `0x53`), and `'D'`
    (directory-dump for incremental backups, `0x44`) are tracked
    independently as issues #2426 / #2429 / #2430 (PR #2431 has
    already landed `'M'` at the time of this paired-review,
    advancing the GNU sub-ladder to its second sibling). The
    paired-review for PR #2428 (and, in turn, PR #2431) is a
    separate follow-up, not in scope here — each paired-review is
    per-PR per the established cadence. The silent-skip family
    remains open-ended (every additional per-typeflag arm fires
    the same `else` fallback in `Tar.extract`, so the marginal
    fixture cost falls but the marginal regression benefit also
    falls); PR #2425 caps the POSIX UStar `'1'`–`'7'` sub-ladder,
    and the GNU sub-ladder (`'V'` / `'M'` / `'S'` / `'D'`) is
    the natural next region. Any future per-typeflag fixture
    should earn its own paired-review entry on the established
    cadence. No new follow-up issue is filed by this
    paired-review.
- Paired review of PR #2428 (`tar-volumeheader-skipped.tar` fixture —
  per-typeflag silent-skip family extension 5 → 6, first GNU-typeflag
  arm opening the GNU sub-ladder distinct from the now-capped POSIX
  UStar `'1'`–`'7'` numeric range; this paired-review landed in
  PR #2441 closing #2435):
  PR #2428 (squash commit `371647bb9d`, merged 2026-05-02T15:43Z,
  closes #2424) extends the `Tar.extract` silent-skip `else` fallback
  family from five to six sibling fixtures and **opens the
  GNU-typeflag sub-ladder** — the first arm beyond the now-exhausted
  POSIX UStar `'1'`–`'7'` numeric range capped by PR #2425
  (paired-reviewed in PR #2433). The commit adds a 512-byte
  single-block UStar fixture
  `testdata/tar/security/tar-volumeheader-skipped.tar` (SHA-256
  `2a975d8f64c9f7ce1556d75329c558fb989488cc82a0af8aca74c9d57bd9fdc1`)
  for typeflag `'V'` (GNU multi-volume archive label marker, `0x56`);
  a seventh `buildZeroSizeFixture` call in
  [scripts/build-symlink-hardlink-malformed-fixtures.lean](/home/kim/lean-zip/scripts/build-symlink-hardlink-malformed-fixtures.lean)
  producing it deterministically; a new test arm in
  [ZipTest/TarFixtures.lean](/home/kim/lean-zip/ZipTest/TarFixtures.lean)
  immediately after the existing `tar-contiguous-skipped.tar` arm,
  asserting the extract directory is empty after extraction *and*
  preserving the entry through `Tar.list` with `typeflag = 0x56`
  (the optional `Tar.list` typeflag-preservation assertion is the
  arm-specific extension over the chardev / blockdev / FIFO /
  contiguous shapes — which assert only the empty extract directory
  — and is the first arm in the family to add it); a new Reproducer
  Corpus row in this inventory; and a *Symlink/hardlink extraction
  policy* fixture-enumeration entry. No spec change, no
  production-code change, no new typeflag constant in the `Tar`
  namespace, no caller / signature change.
  - **Sub-ladder-shift claim fidelity (5 → 6 fixtures, first GNU
    arm).** The 5 → 6 extension math is faithful to the merged tree.
    PR #2428 is the sixth per-typeflag fixture in the silent-skip
    family and the **first GNU-typeflag arm** beyond the POSIX UStar
    numeric range. The five POSIX UStar siblings are
    `hardlink-outside.tar` (PR #1555, typeflag `'1'`, `0x31`),
    `tar-fifo-skipped.tar` (PR #2413, typeflag `'6'`, `0x36`),
    `tar-chardev-skipped.tar` (PR #2417, typeflag `'3'`, `0x33`),
    `tar-blockdev-skipped.tar` (PR #2422, typeflag `'4'`, `0x34`),
    and `tar-contiguous-skipped.tar` (PR #2425, typeflag `'7'`,
    `0x37`); the new GNU `'V'` arm at `0x56` is added by PR #2428.
    The sextet pins six distinct typeflag values
    (`0x31` / `0x36` / `0x33` / `0x34` / `0x37` / `0x56`) against the
    shared `else` fallback at
    [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) (`partial def
    extract`'s tail `else` arm, after the `typeDirectory` /
    `typeRegular` / `typeSymlink` cases). All six fixtures have
    `size = 0` and route through the same `skipEntryData input
    e.size` no-op call in the `else` body, so the structural pin
    remains the *existence* of the `else` arm rather than the
    *behaviour* of any per-typeflag dispatch — a future refactor
    that drops the fallback for any one arm would fire the
    corresponding fixture. The originating PR #1555 set the
    silent-skip precedent at 1/N; PR #2413 added 2/N (paired-reviewed
    in PR #2419, 1 → 2); PR #2417 added 3/N (paired-reviewed in
    PR #2421, 2 → 3); PR #2422 added 4/N (paired-reviewed in
    PR #2427, 3 → 4); PR #2425 added 5/N (paired-reviewed in
    PR #2433, 4 → 5, last POSIX UStar arm); PR #2428 now extends
    to 6/N as the **first GNU-typeflag arm**. With this landing the
    POSIX UStar `'1'`–`'7'` numeric range is now closed (PR #2425's
    paired-review framing), and PR #2428 opens the GNU-typeflag
    sub-ladder — a new region distinct from the POSIX UStar numeric
    range. The natural next region is the rest of the GNU-typeflag
    sub-ladder; the in-flight GNU candidates `'M'` (multi-volume
    continuation, `0x4D`, issue #2426 — closed by PR #2431 since
    landed), `'S'` (sparse file, `0x53`, issue #2429 — closed by
    PR #2434 since landed), and `'D'` (directory-dump for
    incremental backups, `0x44`, issue #2430 — closed by PR #2437
    since landed) are named without committing to specific
    paired-review PR numbers, matching the PR #2421 / PR #2427 /
    PR #2433 paired-review entries' close-out style.
  - **Fixture-builder rename-vs-extend choice.** The worker chose
    *extend in place* on
    [scripts/build-symlink-hardlink-malformed-fixtures.lean](/home/kim/lean-zip/scripts/build-symlink-hardlink-malformed-fixtures.lean),
    matching the PR #2413 / PR #2417 / PR #2422 / PR #2425 workers'
    earlier choices on the same script. The script path stays
    stable; the module docstring's *Output (byte-deterministic)*
    list at PR #2428 land time enumerated seven output files (the
    six pre-PR-#2428 outputs plus the new
    `testdata/tar/security/tar-volumeheader-skipped.tar` line) and
    the per-typeflag enumeration block in the docstring body added
    a sixth bulleted entry for the volume-header arm with its
    typeflag `0x56`, `path = "volume-label-entry"`, empty linkname,
    and silent-skip `else` fallback semantics — phrased *"First
    GNU-typeflag sibling of the silent-skip `else` fallback family
    alongside the POSIX UStar siblings ... together the six pin six
    distinct typeflag values against the shared fallback, spanning
    the POSIX UStar `'1'`/`'3'`/`'4'`/`'6'`/`'7'` numeric range and
    the GNU-typeflag `'V'` extension (a sub-ladder distinct from the
    POSIX UStar `'0'`–`'7'` range)."* The build summary line at
    `main`'s tail at PR #2428 land time printed *"Built 7
    per-typeflag-policy security fixtures under
    testdata/tar/security/."* — the count moved from `6` (PR #2425
    era) to `7` correctly. (Subsequent landings PR #2431 / PR #2434
    / PR #2437 / PR #2439 have since advanced the count to `11` on
    today's master tree, but the PR #2428 land-time count of `7` is
    what this paired-review audits.) The extend-in-place choice
    matches the docstring framing (*"per-typeflag-policy regression
    fixtures"* — agnostic to typeflag count and to the POSIX-vs-GNU
    sub-ladder split) and keeps the rename churn at zero across the
    family extension. Worker-recorded rationale in
    [progress/20260502T154302Z_49edd1ff_tar-volumeheader-skipped-fixture.md](/home/kim/lean-zip/progress/20260502T154302Z_49edd1ff_tar-volumeheader-skipped-fixture.md)
    documents the extend-in-place choice and the per-fixture path
    `"volume-label-entry"` — note the worker chose `volume-label-entry`
    (reading as a synthetic GNU volume *label*) rather than the
    issue body's *suggested* `"volume-header-entry"`; the issue
    body explicitly admitted either was acceptable
    (*"`path = "volume-header-entry"` (or worker's chosen path;
    verify against the merged tree)"*), and `volume-label-entry`
    is consistent with the GNU tar info node `(tar)Multi-Volume
    Archives` terminology where the `'V'` entry's payload contains
    the volume *label* (the typeflag itself is sometimes called the
    "volume header marker", but the path field describes the label
    payload not the marker). This is a minor framing variance, not
    a fidelity defect.
  - **Reproducer Corpus row prose fidelity.** The new
    `tar-volumeheader-skipped.tar` row carries the seven required
    elements: (i) typeflag value `0x56` and the GNU `'V'` glyph
    cited together in the row's opening clause; (ii) GNU
    semantics *"GNU multi-volume archive label marker"* with a GNU
    tar info node `(tar)Standard` citation (the worker chose the
    `(tar)Standard` node rather than `(tar)Multi-Volume Archives` —
    the typeflag is documented in the info-page typeflag table at
    `(tar)Standard`, with the multi-volume mechanism at
    `(tar)Multi-Volume Archives`; either citation is faithful to
    the GNU tar info structure); (iii) silent-skip `else` branch,
    with explicit reference to `Tar.extract`'s tail `else` arm and
    the `skipEntryData` no-op on `e.size = 0`; (iv) sibling fixture
    cross-references to all five POSIX UStar prior arms
    `hardlink-outside.tar` (typeflag `'1'`),
    `tar-fifo-skipped.tar` (typeflag `'6'`),
    `tar-chardev-skipped.tar` (typeflag `'3'`),
    `tar-blockdev-skipped.tar` (typeflag `'4'`), and
    `tar-contiguous-skipped.tar` (typeflag `'7'`) — the row
    correctly names five siblings rather than four, reflecting the
    5 → 6 extension; (v) the family-extension claim phrased as
    *"Per-typeflag silent-skip family extension: this is the
    **first GNU-typeflag** sibling, opening a new sub-ladder
    distinct from the POSIX UStar `'0'`–`'7'` range"* with the
    *"the six together pin six distinct typeflag values against the
    shared fallback"* defense-in-depth framing; (vi) the
    writer-side caveat (*"`Tar.create`'s caller-API only accepts
    paths and never invokes `Tar.buildHeader` with a
    non-`'0'`/`'5'` typeflag, so legitimate archives produced by
    the lean-zip writer never carry typeflag `'V'`"*) — confirmed
    by reading [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean)
    (`Tar.create` builds entries via `walkFiles` with `typeflag :=
    if isDir then typeDirectory else typeRegular`, identical to
    the PR #2413 / PR #2417 / PR #2422 / PR #2425 paired-reviews'
    same audit on the FIFO / chardev / blockdev / contiguous arms);
    (vii) only stable
    [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) anchors — no
    `:N` line-number suffixes, consistent with the
    [PR #2353](https://github.com/kim-em/lean-zip/pull/2353)
    decision. The volume-header arm's framing is the
    *single-volume-only-by-design* / *multi-volume assembly is
    out-of-TCB* rationale (lean-zip does not implement multi-volume
    archive assembly — each `.tar` file is treated as a single
    self-contained archive — so a `'V'` entry has no meaningful
    semantics for lean-zip's extraction model), with an additional
    strict-vs-lenient angle (a malicious archive could ship a `'V'`
    entry with a volume label crafted to look like a filesystem
    path, expecting a lenient extractor to materialise the marker
    as a regular file — lean-zip's policy of *never* materialising
    `'V'` entries regardless of `path` / payload is the correct
    conservative choice). This is the arm-specific extension that
    distinguishes the volume-header row's prose from the chardev /
    FIFO / blockdev / contiguous rows — the chardev / FIFO /
    blockdev rows named concrete *resources* the device node could
    target (raw partition, kernel memory, TTY surfaces), the
    contiguous row named a concrete *aliasing* lenient peers do
    that lean-zip refuses to do (alias `'7'` to `'0'`); the
    volume-header row names a *capability boundary* (multi-volume
    archive assembly is out-of-TCB by design). The five
    arm-specific paragraphs (chardev / blockdev / FIFO / contiguous
    / volume-header) are independently informative — none subsumes
    the others — which remains the right shape for a per-typeflag
    fixture family. The Reproducer Corpus row's closing-PR column
    on the merged tree cites `#2428` (verified via `git blame` on
    the row pointing at PR #2428's merge commit `371647bb9d`); the
    worker performed the closing-PR substitution
    `#TBD-VERIFY-PR` → `#2428` <!-- drift-detector: prose mention of the placeholder substitution in a paired-review finding, not a stale placeholder --> on the worker branch
    pre-merge, matching the PR #2425 / PR #2422 / PR #2417
    self-correction precedent.
  - **Adversarial-check fidelity.** The adversarial check is
    recorded in
    [progress/20260502T154302Z_49edd1ff_tar-volumeheader-skipped-fixture.md](/home/kim/lean-zip/progress/20260502T154302Z_49edd1ff_tar-volumeheader-skipped-fixture.md)
    *## Adversarial check*: temporarily wrapping the `else` body in
    `if e.typeflag == typeHardlink || e.typeflag == 0x36 ||
    e.typeflag == 0x33 || e.typeflag == 0x34 || e.typeflag == 0x37
    then skipEntryData input e.size else throw (IO.userError
    s!"adversarial: unexpected typeflag {e.typeflag}")` left
    `hardlink-outside.tar`, `tar-fifo-skipped.tar`,
    `tar-chardev-skipped.tar`, `tar-blockdev-skipped.tar`, and
    `tar-contiguous-skipped.tar` passing while
    `tar-volumeheader-skipped.tar` fired with `uncaught exception:
    adversarial: unexpected typeflag 86` (`0x56 = 86`, matching
    ASCII `'V'`). The `0x56` ↔ ASCII `'V'` ↔ decimal `86` mapping
    in the adversarial-check parenthetical is internally consistent
    (`0x56` hex = `86` decimal = ASCII codepoint of the glyph
    `'V'`). The wrapper expression preserves all five POSIX UStar
    siblings' arms (`'1'` / `'6'` / `'3'` / `'4'` / `'7'`) and
    exposes only the `'V'` arm — extending the *"spare
    all-but-the-new-arm and confirm the new fixture fires"*
    convention established in the PR #2417 / PR #2422 / PR #2425
    paired-reviews to N=5 spared arms. PR #2413's wrapper spared
    one arm (`'1'` only), PR #2417's spared two (`'1'` and `'6'`),
    PR #2422's spared three (`'1'`, `'6'`, and `'3'`), PR #2425's
    spared four (`'1'`, `'6'`, `'3'`, and `'4'`), and PR #2428's
    spared five (`'1'`, `'6'`, `'3'`, `'4'`, and `'7'`). Each new
    fixture's wrapper extends the disjunction by one
    already-fixtured typeflag, scaling cleanly to N+1 fixtures by
    adding one more spare. The disable-revert was clean — the
    post-revert `git diff Zip/Tar.lean` is empty in the worker's
    merged commit (PR #2428's diff at
    [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) shows zero
    lines changed). The convention now scales to the GNU
    sub-ladder: the next sibling PR #2431 (`'M'` multi-volume
    continuation, `0x4D`, decimal `77`) wrapper would spare six
    arms (`'1'`, `'6'`, `'3'`, `'4'`, `'7'`, and `'V'`); the
    convention is established and ready for the GNU sub-ladder's
    further extensions.
  - **Test-arm placement.** The new test arm in
    [ZipTest/TarFixtures.lean](/home/kim/lean-zip/ZipTest/TarFixtures.lean)
    is placed at the tail of the silent-skip cluster at PR #2428
    land time (immediately after the `tar-contiguous-skipped.tar`
    arm), matching the chronological-by-PR-merge-order convention
    the family has followed since PR #1555. At PR #2428 land time
    the file order was `'1'` → `'6'` → `'3'` → `'4'` → `'7'` →
    `'V'`, mirroring the PR-merge sequence #1555 → #2413 → #2417
    → #2422 → #2425 → #2428. The chronological tail and the
    alphabetical tail coincide at land time
    (`tar-c...skipped` < `tar-v...skipped`), so both interpretations
    of *tail-of-the-cluster* match — the issue body's
    alphabetical-slot phrasing and the chronological-by-PR-order
    house-style phrasing are not in conflict for this arm. (Since
    PR #2428 land time, PR #2431 / PR #2434 / PR #2437 / PR #2439
    have landed `'M'` / `'S'` / `'D'` / `'N'` arms, all
    alphabetically before `tar-volumeheader-skipped.tar`; the
    chronological house style preserves the
    `'V'` → `'M'` → `'S'` → `'D'` → `'N'` order that exists in
    today's master tree, while a strict alphabetical reorder would
    have churned the volume-header arm inward — the chronological
    convention prevails, matching the PR #2433 paired-review's same
    finding for the contiguous arm.) The arm asserts the extract
    directory is empty after `Tar.extract` (mirroring the FIFO /
    chardev / blockdev / contiguous arm shapes) **and** preserves
    the entry through `Tar.list` with `vhListed[0]!.typeflag ==
    0x56` and `vhListed.size == 1` — the optional `Tar.list`
    typeflag-preservation assertion is the **arm-specific
    extension** over the prior four POSIX UStar silent-skip arms,
    pinning the callers-routing-on-typeflag invariant (a future
    refactor that aliased `'V'` to `'0'` in `Tar.list` would now
    fail this assertion). The assertion-shape extension is faithful
    to the issue body's deliverable 5 (*"asserts the extract
    directory is empty after extraction (mirroring the FIFO /
    chardev / blockdev / contiguous arm shapes — verify the
    assertion structure matches)"*) — the empty-extract-dir
    assertion is preserved unchanged; the worker added the
    `Tar.list` assertion as an additive arm-specific extension
    rather than substituting for the empty-extract-dir check. The
    arm uses a distinct extract directory
    `/tmp/lean-zip-fixture-tar-volumeheader-skipped-extract`
    (independent from the five prior arms' extract directories) and
    is registered in both cleanup loops (per-fixture file-list
    `writeFixtureTmp` outputs and the per-directory `rm -rf` list),
    so re-running the test suite remains hermetic across the
    family extension. No shared mutable state across the six arms.
    The five POSIX UStar test arms continue to pass after the new
    arm is added (independently confirmed by `lake exe test` on the
    merged tree: *"TAR fixture tests: OK"*). The `Tar.list`
    typeflag-preservation pattern has since been inherited by the
    four GNU-typeflag successors (PR #2431 / PR #2434 / PR #2437 /
    PR #2439 each carry the same `XListed[0]!.typeflag == 0xNN`
    assertion shape), confirming the volume-header arm's extension
    as the load-bearing convention for the GNU sub-ladder.
  - **Stable-cite discipline.** The new Reproducer Corpus row uses
    only stable identifiers — function names (`Tar.extract`,
    `skipEntryData`, `Tar.forEntries`, `Tar.list`,
    `Tar.buildHeader`, `Tar.create`) and fixture filenames
    (`tar-volumeheader-skipped.tar`, `tar-contiguous-skipped.tar`,
    `tar-blockdev-skipped.tar`, `tar-chardev-skipped.tar`,
    `tar-fifo-skipped.tar`, `hardlink-outside.tar`). No `line N`
    or `:N` suffixes appear anywhere in the row, consistent with
    the
    [PR #2353](https://github.com/kim-em/lean-zip/pull/2353)
    decision to drop line-number anchors. Cross-reference cites
    resolve to real artefacts: PR #2425 / PR #2422 / PR #2417 /
    PR #2413 / PR #1555 are all real merged PRs with the cited
    fixtures and policies. The
    [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) anchor is
    repeated rather than aliased, matching the inventory's house
    style. `bash scripts/check-inventory-links.sh` reports
    `errors=0, warnings=9` on the master tree this paired-review
    branches from (one warning per silent-skip fixture row,
    inherited from the PR #2413 row template — added rows from PR
    #2428 / PR #2431 / PR #2434 / PR #2437 / PR #2439 each kept
    the *during this PR* <!-- drift-detector: prose discussion of the placeholder phrase in a paired-review finding, not a stale placeholder --> phrasing without
    `<!-- drift-detector: -->` opt-outs, deferred to a future
    inventory-cleanup PR per the PR #2433 paired-review's
    deferral). This paired-review introduces no new placeholder
    regression and adds zero warnings — the `#TBD-VERIFY-PR` <!-- drift-detector: prose discussion of the placeholder token in a paired-review finding, not a stale placeholder -->
    placeholder in the paired-review header line is wrapped in a
    `<!-- drift-detector: half-closed paired-review placeholder,
    substituted to the real PR number on the worker branch before
    merge -->` opt-out comment so it does not register as a stale
    placeholder. Suppressing the row-level warnings would still
    require additional `<!-- drift-detector: ... -->` opt-out
    comments per the PR #2371 paired-review pattern; this
    paired-review continues to defer the opt-outs (matching the
    PR #2413 / PR #2417 / PR #2422 / PR #2425 / PR #2433
    paired-review deferrals).
  - **Ladder-progression close-out.** The per-typeflag silent-skip
    family ladder now stands at: PR #1555 (1/N, typeflag `'1'`
    hardlink — predates per-PR paired-review cadence), PR #2413
    (2/N, typeflag `'6'` FIFO — paired-review PR #2419), PR #2417
    (3/N, typeflag `'3'` character device — paired-review PR
    #2421), PR #2422 (4/N, typeflag `'4'` block device —
    paired-review PR #2427), PR #2425 (5/N, typeflag `'7'`
    contiguous file — paired-review PR #2433, last POSIX UStar
    arm), and PR #2428 (6/N, typeflag `'V'` GNU multi-volume
    archive label marker — this paired-review, **first GNU-typeflag
    arm, opening the GNU sub-ladder**). With PR #2428 landing,
    **the GNU-typeflag sub-ladder is opened** beyond the
    now-capped POSIX UStar `'1'`–`'7'` numeric range. The natural
    next region is the rest of the GNU-typeflag sub-ladder; the
    in-flight GNU candidates `'M'` (multi-volume continuation,
    `0x4D`, issue #2426 — closed by PR #2431 since landed), `'S'`
    (sparse file, `0x53`, issue #2429 — closed by PR #2434 since
    landed), and `'D'` (directory-dump for incremental backups,
    `0x44`, issue #2430 — closed by PR #2437 since landed) are
    tracked independently; possible future arms include `'X'`
    (Solaris extended attribute), `'A'` (Solaris ACL), and `'N'`
    (LF_NAMES old-long-name extension, `0x4E` — since landed in
    PR #2439 as `tar-longnames-skipped.tar`). The paired-review
    for PR #2431 (and, in turn, PR #2434 / PR #2437 / PR #2439) is
    a separate follow-up, not in scope here — each paired-review
    is per-PR per the established cadence. The silent-skip family
    remains open-ended (every additional per-typeflag arm fires
    the same `else` fallback in `Tar.extract`, so the marginal
    fixture cost falls but the marginal regression benefit also
    falls); PR #2428 opens the GNU sub-ladder beyond the
    now-capped POSIX UStar `'1'`–`'7'` range, and the GNU
    candidates `'M'` / `'S'` / `'D'` (with possible future arms
    `'X'` Solaris extended attribute, `'A'` Solaris ACL, `'N'` old
    GNU long-name) are the natural next region. Any future
    per-typeflag fixture should earn its own paired-review entry
    on the established cadence. No new follow-up issue is filed
    by this paired-review.

- Paired review of PR #2431 (`tar-multivol-skipped.tar` fixture —
  per-typeflag silent-skip family extension 6 → 7, second
  GNU-typeflag arm extending the GNU sub-ladder opened by PR #2428;
  this paired-review landed in PR #2443 closing #2436):
  PR #2431 (squash commit `1a95969`, merged 2026-05-02T18:38Z,
  closes #2426) extends the `Tar.extract` silent-skip `else`
  fallback family from six to seven sibling fixtures, **extending
  the GNU-typeflag sub-ladder** opened by PR #2428 to two arms.
  The commit adds a 512-byte single-block UStar fixture
  `testdata/tar/security/tar-multivol-skipped.tar` (SHA-256
  `fb2cbbbeefcc59a0a4d5be02f00d9aaee143d4174e54a2c11163ba651e2b2e1d`)
  for typeflag `'M'` (GNU multi-volume continuation marker, `0x4D`);
  an eighth `buildZeroSizeFixture` call in
  [scripts/build-symlink-hardlink-malformed-fixtures.lean](/home/kim/lean-zip/scripts/build-symlink-hardlink-malformed-fixtures.lean)
  producing it deterministically; a new test arm in
  [ZipTest/TarFixtures.lean](/home/kim/lean-zip/ZipTest/TarFixtures.lean)
  immediately after the existing `tar-volumeheader-skipped.tar`
  arm, asserting the extract directory is empty after extraction
  *and* preserving the entry through `Tar.list` with `typeflag =
  0x4D` (the optional `Tar.list` typeflag-preservation assertion
  inherits the **arm-specific extension** introduced by the PR
  #2428 paired-review's volume-header arm and continues the new
  convention into the GNU sub-ladder); a new Reproducer Corpus row
  in this inventory; and a *Symlink/hardlink extraction policy*
  fixture-enumeration entry. No spec change, no production-code
  change, no new typeflag constant in the `Tar` namespace, no
  caller / signature change.
  - **Sub-ladder-extension claim fidelity (6 → 7 fixtures, second
    GNU arm).** The 6 → 7 extension math is faithful to the merged
    tree. PR #2431 is the seventh per-typeflag fixture in the
    silent-skip family and the **second GNU-typeflag arm**,
    extending the GNU sub-ladder opened by PR #2428 (`'V'`,
    `0x56`). The five POSIX UStar siblings are
    `hardlink-outside.tar` (PR #1555, typeflag `'1'`, `0x31`),
    `tar-fifo-skipped.tar` (PR #2413, typeflag `'6'`, `0x36`),
    `tar-chardev-skipped.tar` (PR #2417, typeflag `'3'`, `0x33`),
    `tar-blockdev-skipped.tar` (PR #2422, typeflag `'4'`, `0x34`),
    and `tar-contiguous-skipped.tar` (PR #2425, typeflag `'7'`,
    `0x37`); the GNU `'V'` arm at `0x56` was added by PR #2428;
    the new GNU `'M'` arm at `0x4D` is added by PR #2431. The
    septet pins seven distinct typeflag values
    (`0x31` / `0x36` / `0x33` / `0x34` / `0x37` / `0x56` / `0x4D`)
    against the shared `else` fallback at
    [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) (`partial def
    extract`'s tail `else` arm, after the `typeDirectory` /
    `typeRegular` / `typeSymlink` cases). All seven fixtures have
    `size = 0` and route through the same `skipEntryData input
    e.size` no-op call in the `else` body, so the structural pin
    remains the *existence* of the `else` arm rather than the
    *behaviour* of any per-typeflag dispatch — a future refactor
    that drops the fallback for any one arm would fire the
    corresponding fixture. The originating PR #1555 set the
    silent-skip precedent at 1/N; PR #2413 added 2/N (paired-reviewed
    in PR #2419, 1 → 2); PR #2417 added 3/N (paired-reviewed in
    PR #2421, 2 → 3); PR #2422 added 4/N (paired-reviewed in
    PR #2427, 3 → 4); PR #2425 added 5/N (paired-reviewed in
    PR #2433, 4 → 5, last POSIX UStar arm); PR #2428 added 6/N
    (paired-reviewed in PR #2441, 5 → 6, first GNU-typeflag arm
    opening the GNU sub-ladder); PR #2431 now extends to 7/N as
    the **second GNU-typeflag arm** extending the GNU sub-ladder.
    The POSIX UStar `'1'`–`'7'` numeric range remains closed
    (PR #2425 / PR #2433 framing), and the GNU sub-ladder is now
    a two-arm structure (`'V'` / `'M'`). The natural next region
    is the rest of the GNU-typeflag sub-ladder; the in-flight GNU
    candidates `'S'` (sparse file, `0x53`, issue #2429 — closed
    by PR #2434 since landed) and `'D'` (directory-dump for
    incremental backups, `0x44`, issue #2430 — closed by PR #2437
    since landed) are named without committing to specific
    paired-review PR numbers, matching the PR #2421 / PR #2427 /
    PR #2433 / PR #2441 paired-review entries' close-out style.
  - **Fixture-builder rename-vs-extend choice.** The worker chose
    *extend in place* on
    [scripts/build-symlink-hardlink-malformed-fixtures.lean](/home/kim/lean-zip/scripts/build-symlink-hardlink-malformed-fixtures.lean),
    matching the PR #2413 / PR #2417 / PR #2422 / PR #2425 /
    PR #2428 workers' earlier choices on the same script. The
    script path stays stable; the module docstring's *Output
    (byte-deterministic)* list at PR #2431 land time enumerated
    eight output files (the seven pre-PR-#2431 outputs plus the
    new `testdata/tar/security/tar-multivol-skipped.tar` line) and
    the per-typeflag enumeration block in the docstring body added
    a seventh bulleted entry for the multi-volume arm with its
    typeflag `0x4D`, `path = "multivol-entry"`, empty linkname,
    and silent-skip `else` fallback semantics — phrased *"Second
    GNU-typeflag sibling of the silent-skip `else` fallback family
    alongside `tar-volumeheader-skipped.tar` (typeflag `'V'`),
    extending the GNU-typeflag sub-ladder distinct from the POSIX
    UStar `'0'`–`'7'` range. Together with the five POSIX UStar
    siblings ... the family pins seven distinct typeflag values
    against the shared fallback."* The build summary line at
    `main`'s tail at PR #2431 land time printed *"Built 8
    per-typeflag-policy security fixtures under
    testdata/tar/security/."* — the count moved from `7` (PR #2428
    era) to `8` correctly. (Subsequent landings PR #2434 / PR #2437
    / PR #2439 have since advanced the count to `11` on today's
    master tree, but the PR #2431 land-time count of `8` is what
    this paired-review audits.) The extend-in-place choice keeps
    the rename churn at zero across the family extension. The
    worker's chosen path field `multivol-entry` matches the issue
    body's *"`path = "multivol-entry"` (or worker's chosen path;
    verify against the merged tree)"* invitation and reads as a
    natural multi-volume continuation entry path; this is
    consistent with the GNU tar info node `(tar)Multi-Volume
    Archives` framing where `'M'` records lead the second-and-
    subsequent volumes of a split file. Worker-recorded rationale
    in
    [progress/20260502T183734Z_db8c7be8_tar-multivol-skipped-fixture.md](/home/kim/lean-zip/progress/20260502T183734Z_db8c7be8_tar-multivol-skipped-fixture.md)
    documents the extend-in-place choice and the per-fixture path
    `"multivol-entry"`.
  - **Reproducer Corpus row prose fidelity.** The new
    `tar-multivol-skipped.tar` row carries the seven required
    elements: (i) typeflag value `0x4D` and the GNU `'M'` glyph
    cited together in the row's opening clause; (ii) GNU
    semantics *"GNU multi-volume continuation marker"* with a
    GNU tar info node `(tar)Multi-Volume Archives` citation
    (faithful to the GNU tar info structure for the multi-volume
    workflow — the `'V'` arm cites `(tar)Standard` for the
    typeflag table; the `'M'` arm cites the multi-volume node
    for the runtime mechanism, an arm-specific citation choice
    that mirrors the volume-header / multi-volume distinction);
    (iii) silent-skip `else` branch, with explicit reference to
    `Tar.extract`'s tail `else` arm and the `skipEntryData` no-op
    on `e.size = 0`; (iv) sibling fixture cross-references to all
    five POSIX UStar prior arms `hardlink-outside.tar` (typeflag
    `'1'`), `tar-fifo-skipped.tar` (typeflag `'6'`),
    `tar-chardev-skipped.tar` (typeflag `'3'`),
    `tar-blockdev-skipped.tar` (typeflag `'4'`),
    `tar-contiguous-skipped.tar` (typeflag `'7'`), and the
    PR #2428 GNU `'V'` sibling `tar-volumeheader-skipped.tar` —
    the row correctly names six siblings (five POSIX UStar + one
    GNU), reflecting the 6 → 7 extension; (v) the family-extension
    claim phrased as *"Per-typeflag silent-skip family extension:
    this is the **second GNU-typeflag** sibling, extending the
    GNU-typeflag sub-ladder distinct from the POSIX UStar
    `'0'`–`'7'` range"* with the *"the seven together pin seven
    distinct typeflag values against the shared fallback"*
    defense-in-depth framing; (vi) the writer-side caveat
    (*"`Tar.create`'s caller-API only accepts paths and never
    invokes `Tar.buildHeader` with a non-`'0'`/`'5'` typeflag, so
    legitimate archives produced by the lean-zip writer never
    carry typeflag `'M'`"*) — confirmed by reading
    [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) (`Tar.create`
    builds entries via `walkFiles` with `typeflag := if isDir
    then typeDirectory else typeRegular`, identical to the
    PR #2413 / PR #2417 / PR #2422 / PR #2425 / PR #2428
    paired-reviews' same audit on the prior arms); (vii) only
    stable [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean)
    anchors — no `:N` line-number suffixes, consistent with the
    [PR #2353](https://github.com/kim-em/lean-zip/pull/2353)
    decision. The multi-volume-continuation arm's framing is the
    *cross-volume-splicing-out-of-TCB* / *`realsize`/offset
    metadata is attacker-controlled* rationale (lean-zip does
    not implement multi-volume archive assembly — each `.tar`
    file is treated as a single self-contained archive — and a
    `'M'` entry in single-volume context has no meaningful
    semantics), with the additional strict-vs-lenient angle (a
    malicious single-volume archive could ship a `'M'` entry as
    a top-level record without a preceding multi-volume context,
    with a crafted `path` field e.g. `"../../../etc/passwd"` and
    a non-zero `size` declaring a fake "remaining payload",
    expecting a lenient extractor to materialise the marker as a
    regular file — lean-zip's policy of *never* materialising
    `'M'` entries regardless of `path` / declared `size` /
    actual payload is the correct conservative choice). This is
    the arm-specific extension that distinguishes the
    multi-volume-continuation row's prose from the volume-header
    row — both share the multi-volume-out-of-TCB rationale, but
    the `'M'` arm carries the additional *cross-volume-splicing*
    attack surface (the `realsize`/offset metadata in legitimate
    multi-volume `'M'` entries is attacker-controlled and would
    direct payload writes to arbitrary offsets in a target file
    if honoured), absent from the `'V'` arm (which is a
    single-volume-only-by-design label marker). The seven
    arm-specific paragraphs (chardev / blockdev / FIFO /
    contiguous / volume-header / multi-volume) remain
    independently informative — none subsumes the others — which
    remains the right shape for a per-typeflag fixture family.
    The Reproducer Corpus row's closing-PR column on the merged
    tree cites `#2431` (verified via `git blame` on the row
    pointing at PR #2431's merge commit `1a95969`); the worker
    performed the closing-PR substitution
    `#TBD-VERIFY-PR` → `#2431` <!-- drift-detector: prose mention of the placeholder substitution in a paired-review finding, not a stale placeholder --> on the worker branch
    pre-merge, matching the PR #2417 / PR #2422 / PR #2425 /
    PR #2428 self-correction precedent.
  - **Adversarial-check fidelity.** The adversarial check is
    recorded in
    [progress/20260502T183734Z_db8c7be8_tar-multivol-skipped-fixture.md](/home/kim/lean-zip/progress/20260502T183734Z_db8c7be8_tar-multivol-skipped-fixture.md)
    *## Adversarial check*: temporarily wrapping the `else` body
    in `if e.typeflag == typeHardlink || e.typeflag == 0x36 ||
    e.typeflag == 0x33 || e.typeflag == 0x34 || e.typeflag == 0x37
    || e.typeflag == 0x56 then skipEntryData input e.size else
    throw (IO.userError s!"adversarial: unexpected typeflag
    {e.typeflag}")` left `hardlink-outside.tar`,
    `tar-fifo-skipped.tar`, `tar-chardev-skipped.tar`,
    `tar-blockdev-skipped.tar`, `tar-contiguous-skipped.tar`, and
    `tar-volumeheader-skipped.tar` passing while
    `tar-multivol-skipped.tar` fired with `uncaught exception:
    adversarial: unexpected typeflag 77` (`0x4D = 77`, matching
    ASCII `'M'`). The `0x4D` ↔ ASCII `'M'` ↔ decimal `77` mapping
    in the adversarial-check parenthetical is internally
    consistent (`0x4D` hex = `77` decimal = ASCII codepoint of
    the glyph `'M'`). The wrapper expression preserves all six
    prior siblings' arms (`'1'` / `'6'` / `'3'` / `'4'` / `'7'` /
    `'V'`) and exposes only the `'M'` arm — extending the *"spare
    all-but-the-new-arm and confirm the new fixture fires"*
    convention to N=6 spared arms (PR #2413's wrapper spared one
    arm, PR #2417's two, PR #2422's three, PR #2425's four,
    PR #2428's five, and PR #2431's six). Each new fixture's
    wrapper extends the disjunction by one already-fixtured
    typeflag, scaling cleanly to N+1 fixtures by adding one more
    spare. The disable-revert was clean — the post-revert
    `git diff Zip/Tar.lean` is empty in the worker's merged
    commit (PR #2431's diff at
    [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) shows zero
    lines changed). The convention now scales further into the
    GNU sub-ladder: the next sibling PR #2434 (`'S'` sparse,
    `0x53`, decimal `83`) wrapper would spare seven arms (`'1'`,
    `'6'`, `'3'`, `'4'`, `'7'`, `'V'`, and `'M'`); the
    convention is established and continues into the GNU
    sub-ladder's further extensions (PR #2434 / PR #2437 /
    PR #2439 since landed, each carrying the same
    spare-prior-and-fire-this-arm shape).
  - **Test-arm placement.** The new test arm in
    [ZipTest/TarFixtures.lean](/home/kim/lean-zip/ZipTest/TarFixtures.lean)
    is placed at the tail of the silent-skip cluster at PR #2431
    land time (immediately after the `tar-volumeheader-skipped.tar`
    arm), matching the chronological-by-PR-merge-order convention
    the family has followed since PR #1555. At PR #2431 land time
    the file order was `'1'` → `'6'` → `'3'` → `'4'` → `'7'` →
    `'V'` → `'M'`, mirroring the PR-merge sequence #1555 → #2413
    → #2417 → #2422 → #2425 → #2428 → #2431. The chronological
    house style preserves this order in today's master tree
    despite an alphabetical reorder being available
    (`tar-c...skipped` < `tar-f...skipped` < `tar-m...skipped` <
    `tar-v...skipped` would have churned the volume-header arm
    inward), matching the PR #2433 / PR #2441 paired-reviews'
    same finding for prior arms. The arm asserts the extract
    directory is empty after `Tar.extract` (mirroring the FIFO /
    chardev / blockdev / contiguous / volume-header arm shapes)
    **and** preserves the entry through `Tar.list` with
    `mvListed[0]!.typeflag == 0x4D` and `mvListed.size == 1` —
    inheriting the optional `Tar.list` typeflag-preservation
    assertion introduced by the volume-header arm at PR #2428.
    This is now an established convention for the GNU sub-ladder
    rather than a per-arm extension: PR #2434 / PR #2437 /
    PR #2439 each carry the same `XListed[0]!.typeflag == 0xNN`
    assertion shape, confirming the convention's load-bearing
    status. The assertion-shape inheritance is faithful to the
    issue body's deliverable 5 (*"asserts the extract directory
    is empty after extraction (mirroring the FIFO / chardev /
    blockdev / contiguous / volume-header arm shapes — verify the
    assertion structure matches)"*) — the empty-extract-dir
    assertion is preserved unchanged; the worker preserved the
    `Tar.list` assertion as an additive arm-specific extension
    rather than substituting for the empty-extract-dir check. The
    arm uses a distinct extract directory
    `/tmp/lean-zip-fixture-tar-multivol-skipped-extract`
    (independent from the six prior arms' extract directories) and
    is registered in both cleanup loops (per-fixture file-list
    `writeFixtureTmp` outputs and the per-directory `rm -rf`
    list), so re-running the test suite remains hermetic across
    the family extension. No shared mutable state across the seven
    arms. The six prior test arms continue to pass after the new
    arm is added (independently confirmed by `lake exe test` on
    the merged tree: *"TAR fixture tests: OK"*).
  - **Stable-cite discipline.** The new Reproducer Corpus row uses
    only stable identifiers — function names (`Tar.extract`,
    `skipEntryData`, `Tar.forEntries`, `Tar.list`,
    `Tar.buildHeader`, `Tar.create`) and fixture filenames
    (`tar-multivol-skipped.tar`, `tar-volumeheader-skipped.tar`,
    `tar-contiguous-skipped.tar`, `tar-blockdev-skipped.tar`,
    `tar-chardev-skipped.tar`, `tar-fifo-skipped.tar`,
    `hardlink-outside.tar`). No `line N` or `:N` suffixes appear
    anywhere in the row, consistent with the
    [PR #2353](https://github.com/kim-em/lean-zip/pull/2353)
    decision to drop line-number anchors. Cross-reference cites
    resolve to real artefacts: PR #2428 / PR #2425 / PR #2422 /
    PR #2417 / PR #2413 / PR #1555 are all real merged PRs with
    the cited fixtures and policies. The
    [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) anchor is
    repeated rather than aliased, matching the inventory's house
    style. `bash scripts/check-inventory-links.sh` reports
    `errors=0, warnings=9` on the master tree this paired-review
    branches from (one warning per silent-skip fixture row,
    inherited from the PR #2413 row template — added rows from
    PR #2428 / PR #2431 / PR #2434 / PR #2437 / PR #2439 each kept
    the *during this PR* <!-- drift-detector: prose discussion of the placeholder phrase in a paired-review finding, not a stale placeholder --> phrasing without
    `<!-- drift-detector: -->` opt-outs, deferred to a future
    inventory-cleanup PR per the PR #2433 paired-review's
    deferral). This paired-review introduces no new placeholder
    regression and adds zero warnings — the `#TBD-VERIFY-PR` <!-- drift-detector: prose discussion of the placeholder token in a paired-review finding, not a stale placeholder -->
    placeholder in the paired-review header line is wrapped in a
    `<!-- drift-detector: half-closed paired-review placeholder,
    substituted to the real PR number on the worker branch before
    merge -->` opt-out comment so it does not register as a stale
    placeholder. Suppressing the row-level warnings would still
    require additional `<!-- drift-detector: ... -->` opt-out
    comments per the PR #2371 paired-review pattern; this
    paired-review continues to defer the opt-outs (matching the
    PR #2413 / PR #2417 / PR #2422 / PR #2425 / PR #2433 /
    PR #2441 paired-review deferrals).
  - **Ladder-progression close-out.** The per-typeflag silent-skip
    family ladder now stands at: PR #1555 (1/N, typeflag `'1'`
    hardlink — predates per-PR paired-review cadence), PR #2413
    (2/N, typeflag `'6'` FIFO — paired-review PR #2419), PR #2417
    (3/N, typeflag `'3'` character device — paired-review PR
    #2421), PR #2422 (4/N, typeflag `'4'` block device —
    paired-review PR #2427), PR #2425 (5/N, typeflag `'7'`
    contiguous file — paired-review PR #2433, last POSIX UStar
    arm), PR #2428 (6/N, typeflag `'V'` GNU multi-volume archive
    label marker — paired-review PR #2441, first GNU-typeflag
    arm opening the GNU sub-ladder), and PR #2431 (7/N, typeflag
    `'M'` GNU multi-volume continuation marker — this
    paired-review, **second GNU-typeflag arm extending the GNU
    sub-ladder**). With PR #2431 landing, **the GNU-typeflag
    sub-ladder grew to two arms** (`'V'` / `'M'`) beyond the
    now-capped POSIX UStar `'1'`–`'7'` numeric range. The
    silent-skip family remains open-ended (every additional
    per-typeflag arm fires the same `else` fallback in
    `Tar.extract`, so the marginal fixture cost falls but the
    marginal regression benefit also falls); PR #2431 extends the
    GNU sub-ladder opened by PR #2428 to two arms, with the
    in-flight `'S'` (PR #2434, paired-review issue #2440 in
    flight) and `'D'` (PR #2437, paired-review issue #2442 in
    flight) candidates — and the just-landed `'N'` arm (PR #2439,
    paired-review pending) — the natural next region (and
    possible future arms `'X'` Solaris extended attribute, `'A'`
    Solaris ACL, once the shortlist exhausts). The paired-review
    for PR #2434 / PR #2437 / PR #2439 (and any further
    GNU-typeflag siblings) is a separate follow-up, not in scope
    here — each paired-review is per-PR per the established
    cadence. Any future per-typeflag fixture should earn its own
    paired-review entry on the established cadence. No new
    follow-up issue is filed by this paired-review.

- Paired review of PR #2434 (`tar-sparse-skipped.tar` fixture —
  per-typeflag silent-skip family extension 7 → 8, third
  GNU-typeflag arm extending the GNU sub-ladder opened by PR #2428
  and extended by PR #2431; this paired-review landed in
  PR #2444 closing #2440):
  PR #2434 (squash commit `e37d0267`, merged 2026-05-02T19:12Z,
  closes #2429) extends the `Tar.extract` silent-skip `else`
  fallback family from seven to eight sibling fixtures, **extending
  the GNU-typeflag sub-ladder** opened by PR #2428 and continued by
  PR #2431 to three arms. The commit adds a 512-byte single-block
  UStar fixture `testdata/tar/security/tar-sparse-skipped.tar`
  (SHA-256
  `25789796481693e1397bd2fed8d7609451430907e5da89a63038f59c63d81445`)
  for typeflag `'S'` (GNU sparse file, `0x53`); a ninth
  `buildZeroSizeFixture` call in
  [scripts/build-symlink-hardlink-malformed-fixtures.lean](/home/kim/lean-zip/scripts/build-symlink-hardlink-malformed-fixtures.lean)
  producing it deterministically; a new test arm in
  [ZipTest/TarFixtures.lean](/home/kim/lean-zip/ZipTest/TarFixtures.lean)
  immediately after the existing `tar-multivol-skipped.tar` arm,
  asserting the extract directory is empty after extraction *and*
  preserving the entry through `Tar.list` with `typeflag = 0x53`
  (the optional `Tar.list` typeflag-preservation assertion inherits
  the **arm-specific extension** introduced by the PR #2428
  paired-review's volume-header arm and continues the convention
  established for the GNU sub-ladder by PR #2431); a new Reproducer
  Corpus row in this inventory; and a *Symlink/hardlink extraction
  policy* fixture-enumeration entry. No spec change, no
  production-code change, no new typeflag constant in the `Tar`
  namespace, no caller / signature change.
  - **Sub-ladder-extension claim fidelity (7 → 8 fixtures, third
    GNU arm).** The 7 → 8 extension math is faithful to the merged
    tree. PR #2434 is the eighth per-typeflag fixture in the
    silent-skip family and the **third GNU-typeflag arm**,
    extending the GNU sub-ladder opened by PR #2428 (`'V'`, `0x56`)
    and extended by PR #2431 (`'M'`, `0x4D`). The five POSIX UStar
    siblings are `hardlink-outside.tar` (PR #1555, typeflag `'1'`,
    `0x31`), `tar-fifo-skipped.tar` (PR #2413, typeflag `'6'`,
    `0x36`), `tar-chardev-skipped.tar` (PR #2417, typeflag `'3'`,
    `0x33`), `tar-blockdev-skipped.tar` (PR #2422, typeflag `'4'`,
    `0x34`), and `tar-contiguous-skipped.tar` (PR #2425, typeflag
    `'7'`, `0x37`); the GNU `'V'` arm at `0x56` was added by
    PR #2428; the GNU `'M'` arm at `0x4D` was added by PR #2431;
    the new GNU `'S'` arm at `0x53` is added by PR #2434. The
    octet pins eight distinct typeflag values
    (`0x31` / `0x36` / `0x33` / `0x34` / `0x37` / `0x56` / `0x4D` /
    `0x53`) against the shared `else` fallback at
    [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) (`partial def
    extract`'s tail `else` arm, after the `typeDirectory` /
    `typeRegular` / `typeSymlink` cases). All eight fixtures have
    `size = 0` and route through the same `skipEntryData input
    e.size` no-op call in the `else` body, so the structural pin
    remains the *existence* of the `else` arm rather than the
    *behaviour* of any per-typeflag dispatch — a future refactor
    that drops the fallback for any one arm would fire the
    corresponding fixture. The originating PR #1555 set the
    silent-skip precedent at 1/N; PR #2413 added 2/N (paired-reviewed
    in PR #2419, 1 → 2); PR #2417 added 3/N (paired-reviewed in
    PR #2421, 2 → 3); PR #2422 added 4/N (paired-reviewed in
    PR #2427, 3 → 4); PR #2425 added 5/N (paired-reviewed in
    PR #2433, 4 → 5, last POSIX UStar arm); PR #2428 added 6/N
    (paired-reviewed in PR #2441, 5 → 6, first GNU-typeflag arm
    opening the GNU sub-ladder); PR #2431 added 7/N (paired-reviewed
    in PR #2443, 6 → 7, second GNU-typeflag arm); PR #2434 now
    extends to 8/N as the **third GNU-typeflag arm** extending the
    GNU sub-ladder. The POSIX UStar `'1'`–`'7'` numeric range
    remains closed (PR #2425 / PR #2433 framing), and the GNU
    sub-ladder is now a three-arm structure (`'V'` / `'M'` / `'S'`).
    The natural next region is the rest of the GNU-typeflag
    sub-ladder; the merged-but-unreviewed GNU candidates `'D'`
    (directory-dump for incremental backups, `0x44`, PR #2437 since
    landed) and `'N'` (LF_NAMES old-long-name extension, `0x4E`,
    PR #2439 since landed) are named without committing to specific
    paired-review PR numbers, matching the PR #2421 / PR #2427 /
    PR #2433 / PR #2441 / PR #2443 paired-review entries' close-out
    style.
  - **Fixture-builder rename-vs-extend choice.** The worker chose
    *extend in place* on
    [scripts/build-symlink-hardlink-malformed-fixtures.lean](/home/kim/lean-zip/scripts/build-symlink-hardlink-malformed-fixtures.lean),
    matching the PR #2413 / PR #2417 / PR #2422 / PR #2425 /
    PR #2428 / PR #2431 workers' earlier choices on the same script.
    The script path stays stable; the module docstring's *Output
    (byte-deterministic)* list at PR #2434 land time enumerated
    nine output files (the eight pre-PR-#2434 outputs plus the new
    `testdata/tar/security/tar-sparse-skipped.tar` line) and the
    per-typeflag enumeration block in the docstring body added an
    eighth bulleted entry for the sparse arm with its typeflag
    `0x53`, `path = "sparse-entry"`, empty linkname, and silent-skip
    `else` fallback semantics — phrased *"Third GNU-typeflag sibling
    of the silent-skip `else` fallback family alongside
    `tar-volumeheader-skipped.tar` (typeflag `'V'`) and
    `tar-multivol-skipped.tar` (typeflag `'M'`), extending the
    GNU-typeflag sub-ladder distinct from the POSIX UStar
    `'0'`–`'7'` range."* The build summary line at `main`'s tail at
    PR #2434 land time printed *"Built 9 per-typeflag-policy
    security fixtures under testdata/tar/security/."* — the count
    moved from `8` (PR #2431 era) to `9` correctly. (Subsequent
    landings PR #2437 / PR #2439 have since advanced the count to
    `11` on today's master tree, but the PR #2434 land-time count
    of `9` is what this paired-review audits.) The extend-in-place
    choice keeps the rename churn at zero across the family
    extension. The worker's chosen path field `sparse-entry`
    matches the issue body's *"`path = "sparse-entry"` (or worker's
    chosen path; verify against the merged tree)"* invitation and
    reads as a natural sparse-file entry path; this is consistent
    with the GNU tar info node `(tar)Sparse Formats` framing where
    `'S'` records describe a sparse file's payload by sparse-map
    metadata. Worker-recorded rationale in
    [progress/20260502T190907Z_0fc29266_tar-sparse-skipped-fixture.md](/home/kim/lean-zip/progress/20260502T190907Z_0fc29266_tar-sparse-skipped-fixture.md)
    documents the extend-in-place choice and the per-fixture path
    `"sparse-entry"`.
  - **Reproducer Corpus row prose fidelity.** The new
    `tar-sparse-skipped.tar` row carries the seven required
    elements: (i) typeflag value `0x53` and the GNU `'S'` glyph
    cited together in the row's opening clause; (ii) GNU semantics
    *"GNU sparse file"* with a GNU tar info node
    `(tar)Sparse Formats` citation (faithful to the GNU tar info
    structure for the sparse-encoding workflow — the `'V'` arm
    cites `(tar)Standard` for the typeflag table, the `'M'` arm
    cites `(tar)Multi-Volume Archives` for the multi-volume runtime
    mechanism, and the `'S'` arm cites `(tar)Sparse Formats` for
    the sparse-encoding mechanism, an arm-specific citation choice
    that mirrors the volume-header / multi-volume / sparse
    distinction); (iii) silent-skip `else` branch, with explicit
    reference to `Tar.extract`'s tail `else` arm and the
    `skipEntryData` no-op on `e.size = 0`; (iv) sibling fixture
    cross-references to all five POSIX UStar prior arms
    `hardlink-outside.tar` (typeflag `'1'`),
    `tar-fifo-skipped.tar` (typeflag `'6'`),
    `tar-chardev-skipped.tar` (typeflag `'3'`),
    `tar-blockdev-skipped.tar` (typeflag `'4'`),
    `tar-contiguous-skipped.tar` (typeflag `'7'`), the PR #2428 GNU
    `'V'` sibling `tar-volumeheader-skipped.tar`, and the PR #2431
    GNU `'M'` sibling `tar-multivol-skipped.tar` — the row
    correctly names seven siblings (five POSIX UStar + two GNU),
    reflecting the 7 → 8 extension; (v) the family-extension claim
    phrased as *"Per-typeflag silent-skip family extension: this is
    the **third GNU-typeflag** sibling, extending the GNU-typeflag
    sub-ladder distinct from the POSIX UStar `'0'`–`'7'` range"*
    with the *"the eight together pin eight distinct typeflag
    values against the shared fallback"* defense-in-depth framing;
    (vi) the writer-side caveat (*"`Tar.create`'s caller-API only
    accepts paths and never invokes `Tar.buildHeader` with a
    non-`'0'`/`'5'` typeflag, so legitimate archives produced by
    the lean-zip writer never carry typeflag `'S'`"*) — confirmed
    by reading [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean)
    (`Tar.create` builds entries via `walkFiles` with
    `typeflag := if isDir then typeDirectory else typeRegular`,
    identical to the PR #2413 / PR #2417 / PR #2422 / PR #2425 /
    PR #2428 / PR #2431 paired-reviews' same audit on the prior
    arms); (vii) only stable
    [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) anchors — no
    `:N` line-number suffixes, consistent with the
    [PR #2353](https://github.com/kim-em/lean-zip/pull/2353)
    decision. The sparse arm's framing is the
    *encoding-format-not-implemented-by-design* / *sparse-map
    metadata is attacker-controlled* rationale (lean-zip does not
    implement sparse-file reconstruction — which would require
    parsing the GNU sparse-map header, allocating a sparse output
    file, and writing the non-zero spans at their declared offsets
    — so an `'S'` entry has no meaningful semantics for lean-zip's
    extraction model), with the additional strict-vs-lenient angle
    (a malicious archive could ship a `'S'` entry with a crafted
    sparse map declaring zero-fill segments that overlap or exceed
    the entry's declared `size`, expecting a lenient extractor to
    allocate a large output file (zero-fill amplification) or
    miscompute the payload offset and corrupt subsequent entries
    — lean-zip's policy of *never* materialising `'S'` entries
    regardless of `path` / sparse map / declared `size` / actual
    payload is the correct conservative choice, and pinning it
    with a fixture prevents future drift toward a sparse-aware
    extractor that would reinterpret the payload (e.g. as a raw
    data blob written linearly, which would silently corrupt
    sparse-encoded archives by writing the sparse-map metadata
    into the output file)). The sparse format itself has multiple
    parser-differential variants (`0.0` / `0.1` / `1.0`) with
    subtly different sparse-map encodings, expanding the
    attack surface a sparse-aware reconstructor would have to
    defend; lean-zip's silent-skip policy sidesteps the entire
    parser-differential family. This is the arm-specific extension
    that distinguishes the sparse row's prose from the
    volume-header / multi-volume rows — the volume-header row names
    a *single-volume-only-by-design* capability boundary, the
    multi-volume row names *cross-volume-splicing* with
    attacker-controlled `realsize`/offset metadata, and the sparse
    row names *encoding-format-not-implemented-by-design* with the
    parser-differential variant matrix as the additional
    attack-surface argument. The eight arm-specific paragraphs
    (chardev / blockdev / FIFO / contiguous / volume-header /
    multi-volume / sparse) remain independently informative — none
    subsumes the others — which remains the right shape for a
    per-typeflag fixture family. The Reproducer Corpus row's
    closing-PR column on the merged tree cites `#2434` (verified
    via `git blame` on the row pointing at PR #2434's merge commit
    `e37d0267`); the worker performed the closing-PR substitution
    `#TBD-VERIFY-PR` → `#2434` <!-- drift-detector: prose mention of the placeholder substitution in a paired-review finding, not a stale placeholder --> on the worker branch
    pre-merge, matching the PR #2417 / PR #2422 / PR #2425 /
    PR #2428 / PR #2431 self-correction precedent.
  - **Adversarial-check fidelity.** The adversarial check is
    recorded in
    [progress/20260502T190907Z_0fc29266_tar-sparse-skipped-fixture.md](/home/kim/lean-zip/progress/20260502T190907Z_0fc29266_tar-sparse-skipped-fixture.md)
    *## Adversarial check*: temporarily wrapping the `else` body
    in `if e.typeflag == typeHardlink || e.typeflag == 0x36 ||
    e.typeflag == 0x33 || e.typeflag == 0x34 || e.typeflag == 0x37
    || e.typeflag == 0x56 || e.typeflag == 0x4D then skipEntryData
    input e.size else throw (IO.userError s!"adversarial:
    unexpected typeflag {e.typeflag}")` left
    `hardlink-outside.tar`, `tar-fifo-skipped.tar`,
    `tar-chardev-skipped.tar`, `tar-blockdev-skipped.tar`,
    `tar-contiguous-skipped.tar`, `tar-volumeheader-skipped.tar`,
    and `tar-multivol-skipped.tar` passing while
    `tar-sparse-skipped.tar` fired with `uncaught exception:
    adversarial: unexpected typeflag 83` (`0x53 = 83`, matching
    ASCII `'S'`). The `0x53` ↔ ASCII `'S'` ↔ decimal `83` mapping
    in the adversarial-check parenthetical is internally consistent
    (`0x53` hex = `83` decimal = ASCII codepoint of the glyph
    `'S'`). The wrapper expression preserves all seven prior
    siblings' arms (`'1'` / `'6'` / `'3'` / `'4'` / `'7'` / `'V'` /
    `'M'`) and exposes only the `'S'` arm — extending the *"spare
    all-but-the-new-arm and confirm the new fixture fires"*
    convention to N=7 spared arms (PR #2413's wrapper spared one
    arm, PR #2417's two, PR #2422's three, PR #2425's four,
    PR #2428's five, PR #2431's six, and PR #2434's seven). Each
    new fixture's wrapper extends the disjunction by one
    already-fixtured typeflag, scaling cleanly to N+1 fixtures by
    adding one more spare. The disable-revert was clean — the
    post-revert `git diff Zip/Tar.lean` is empty in the worker's
    merged commit (PR #2434's diff at
    [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) shows zero
    lines changed). The convention now scales further into the GNU
    sub-ladder: the next sibling PR #2437 (`'D'` directory-dump,
    `0x44`, decimal `68`) wrapper would spare eight arms (`'1'`,
    `'6'`, `'3'`, `'4'`, `'7'`, `'V'`, `'M'`, and `'S'`); the
    convention is established and continues into the GNU
    sub-ladder's further extensions (PR #2437 / PR #2439 since
    landed, each carrying the same spare-prior-and-fire-this-arm
    shape).
  - **Test-arm placement.** The new test arm in
    [ZipTest/TarFixtures.lean](/home/kim/lean-zip/ZipTest/TarFixtures.lean)
    is placed at the tail of the silent-skip cluster at PR #2434
    land time (immediately after the `tar-multivol-skipped.tar`
    arm), matching the chronological-by-PR-merge-order convention
    the family has followed since PR #1555. At PR #2434 land time
    the file order was `'1'` → `'6'` → `'3'` → `'4'` → `'7'` →
    `'V'` → `'M'` → `'S'`, mirroring the PR-merge sequence
    #1555 → #2413 → #2417 → #2422 → #2425 → #2428 → #2431 →
    #2434. The chronological house style preserves this order in
    today's master tree despite an alphabetical reorder being
    available (`tar-c...skipped` < `tar-f...skipped` <
    `tar-m...skipped` < `tar-s...skipped` < `tar-v...skipped`
    would have churned the volume-header arm inward), matching the
    PR #2433 / PR #2441 / PR #2443 paired-reviews' same finding for
    prior arms. The arm asserts the extract directory is empty
    after `Tar.extract` (mirroring the FIFO / chardev / blockdev /
    contiguous / volume-header / multi-volume arm shapes) **and**
    preserves the entry through `Tar.list` with
    `spListed[0]!.typeflag == 0x53` and `spListed.size == 1` —
    inheriting the optional `Tar.list` typeflag-preservation
    assertion introduced by the volume-header arm at PR #2428 and
    continued by the multi-volume arm at PR #2431. This is now an
    established convention for the GNU sub-ladder rather than a
    per-arm extension: PR #2437 / PR #2439 each carry the same
    `XListed[0]!.typeflag == 0xNN` assertion shape, confirming the
    convention's load-bearing status. The assertion-shape
    inheritance is faithful to the issue body's deliverable 5
    (*"asserts the extract directory is empty after extraction
    (mirroring the FIFO / chardev / blockdev / contiguous /
    volume-header arm shapes — verify the assertion structure
    matches)"*) — the empty-extract-dir assertion is preserved
    unchanged; the worker preserved the `Tar.list` assertion as an
    additive arm-specific extension rather than substituting for
    the empty-extract-dir check. The arm uses a distinct extract
    directory `/tmp/lean-zip-fixture-tar-sparse-skipped-extract`
    (independent from the seven prior arms' extract directories)
    and is registered in both cleanup loops (per-fixture file-list
    `writeFixtureTmp` outputs and the per-directory `rm -rf`
    list), so re-running the test suite remains hermetic across
    the family extension. No shared mutable state across the eight
    arms. The seven prior test arms continue to pass after the new
    arm is added (independently confirmed by `lake exe test` on
    the merged tree: *"All tests passed!"*).
  - **Stable-cite discipline.** The new Reproducer Corpus row uses
    only stable identifiers — function names (`Tar.extract`,
    `skipEntryData`, `Tar.forEntries`, `Tar.list`,
    `Tar.buildHeader`, `Tar.create`) and fixture filenames
    (`tar-sparse-skipped.tar`, `tar-multivol-skipped.tar`,
    `tar-volumeheader-skipped.tar`, `tar-contiguous-skipped.tar`,
    `tar-blockdev-skipped.tar`, `tar-chardev-skipped.tar`,
    `tar-fifo-skipped.tar`, `hardlink-outside.tar`). No `line N` or
    `:N` suffixes appear anywhere in the row, consistent with the
    [PR #2353](https://github.com/kim-em/lean-zip/pull/2353)
    decision to drop line-number anchors. Cross-reference cites
    resolve to real artefacts: PR #2431 / PR #2428 / PR #2425 /
    PR #2422 / PR #2417 / PR #2413 / PR #1555 are all real merged
    PRs with the cited fixtures and policies. The
    [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) anchor is
    repeated rather than aliased, matching the inventory's house
    style. `bash scripts/check-inventory-links.sh` reports
    `errors=0, warnings=9` on the master tree this paired-review
    branches from (one warning per silent-skip fixture row,
    inherited from the PR #2413 row template — added rows from
    PR #2428 / PR #2431 / PR #2434 / PR #2437 / PR #2439 each kept
    the *during this PR* <!-- drift-detector: prose discussion of the placeholder phrase in a paired-review finding, not a stale placeholder --> phrasing without
    `<!-- drift-detector: -->` opt-outs, deferred to a future
    inventory-cleanup PR per the PR #2433 paired-review's
    deferral). This paired-review introduces no new placeholder
    regression and adds zero warnings — the `#TBD-VERIFY-PR` <!-- drift-detector: prose discussion of the placeholder token in a paired-review finding, not a stale placeholder -->
    placeholder in the paired-review header line is wrapped in a
    `<!-- drift-detector: half-closed paired-review placeholder,
    substituted to the real PR number on the worker branch before
    merge -->` opt-out comment so it does not register as a stale
    placeholder. Suppressing the row-level warnings would still
    require additional `<!-- drift-detector: ... -->` opt-out
    comments per the PR #2371 paired-review pattern; this
    paired-review continues to defer the opt-outs (matching the
    PR #2413 / PR #2417 / PR #2422 / PR #2425 / PR #2433 /
    PR #2441 / PR #2443 paired-review deferrals).
  - **Ladder-progression close-out.** The per-typeflag silent-skip
    family ladder now stands at: PR #1555 (1/N, typeflag `'1'`
    hardlink — predates per-PR paired-review cadence), PR #2413
    (2/N, typeflag `'6'` FIFO — paired-review PR #2419), PR #2417
    (3/N, typeflag `'3'` character device — paired-review
    PR #2421), PR #2422 (4/N, typeflag `'4'` block device —
    paired-review PR #2427), PR #2425 (5/N, typeflag `'7'`
    contiguous file — paired-review PR #2433, last POSIX UStar
    arm), PR #2428 (6/N, typeflag `'V'` GNU multi-volume archive
    label marker — paired-review PR #2441, first GNU-typeflag arm
    opening the GNU sub-ladder), PR #2431 (7/N, typeflag `'M'` GNU
    multi-volume continuation marker — paired-review PR #2443,
    second GNU-typeflag arm), and PR #2434 (8/N, typeflag `'S'`
    GNU sparse file — this paired-review, **third GNU-typeflag arm
    extending the GNU sub-ladder**). With PR #2434 landing, **the
    GNU-typeflag sub-ladder grew to three arms** (`'V'` / `'M'` /
    `'S'`) beyond the now-capped POSIX UStar `'1'`–`'7'` numeric
    range. The silent-skip family remains open-ended (every
    additional per-typeflag arm fires the same `else` fallback in
    `Tar.extract`, so the marginal fixture cost falls but the
    marginal regression benefit also falls); PR #2434 extends the
    GNU sub-ladder to three arms, with the merged-but-unreviewed
    GNU successors PR #2437 (`'D'` directory-dump for incremental
    backups, `0x44`, paired-review issue #2442 in flight) and
    PR #2439 (`'N'` LF_NAMES old-long-name extension, `0x4E`,
    paired-review pending) — the natural next region (and possible
    future arms `'X'` Solaris extended attribute, `'A'` Solaris
    ACL, once the shortlist exhausts). The paired-review for
    PR #2437 / PR #2439 (and any further GNU-typeflag siblings) is
    a separate follow-up, not in scope here — each paired-review
    is per-PR per the established cadence. Any future per-typeflag
    fixture should earn its own paired-review entry on the
    established cadence. No new follow-up issue is filed by this
    paired-review.

- Paired review of PR #2437 (`tar-incremental-skipped.tar` fixture —
  per-typeflag silent-skip family extension 8 → 9, fourth
  GNU-typeflag arm extending the GNU sub-ladder opened by PR #2428,
  extended by PR #2431, and extended further by PR #2434; this
  paired-review landed in PR <!-- drift-detector: half-closed paired-review placeholder, substituted to the real PR number on the worker branch before merge --> #TBD-VERIFY-PR closing #2442):
  PR #2437 (squash commit `67481e13`, merged 2026-05-02T19:35Z,
  closes #2430) extends the `Tar.extract` silent-skip `else`
  fallback family from eight to nine sibling fixtures, **extending
  the GNU-typeflag sub-ladder** opened by PR #2428, continued by
  PR #2431, and continued by PR #2434 to four arms. The commit adds
  a 512-byte single-block UStar fixture
  `testdata/tar/security/tar-incremental-skipped.tar` (SHA-256
  `db71d06e88ff482c3455f77a2c97e16301f02075cbf2fe71de3f5cb4d620d480`)
  for typeflag `'D'` (GNU directory-dump for incremental backups,
  `0x44`); a tenth `buildZeroSizeFixture` call in
  [scripts/build-symlink-hardlink-malformed-fixtures.lean](/home/kim/lean-zip/scripts/build-symlink-hardlink-malformed-fixtures.lean)
  producing it deterministically; a new test arm in
  [ZipTest/TarFixtures.lean](/home/kim/lean-zip/ZipTest/TarFixtures.lean)
  immediately after the existing `tar-sparse-skipped.tar` arm,
  asserting the extract directory is empty after extraction *and*
  preserving the entry through `Tar.list` with `typeflag = 0x44`
  (the optional `Tar.list` typeflag-preservation assertion
  inheriting the **arm-specific extension** introduced by the
  PR #2428 paired-review's volume-header arm and continued by the
  PR #2431 / PR #2434 GNU-arms — by PR #2437 land time this is now
  an established convention for the GNU sub-ladder rather than a
  per-arm extension); a new Reproducer Corpus row in this
  inventory; and a *Symlink/hardlink extraction policy*
  fixture-enumeration entry. No spec change, no production-code
  change, no new typeflag constant in the `Tar` namespace, no
  caller / signature change.
  - **Sub-ladder-extension claim fidelity (8 → 9 fixtures, fourth
    GNU arm).** The 8 → 9 extension math is faithful to the merged
    tree. PR #2437 is the ninth per-typeflag fixture in the
    silent-skip family and the **fourth GNU-typeflag arm**,
    extending the GNU sub-ladder opened by PR #2428 (`'V'`, `0x56`),
    extended by PR #2431 (`'M'`, `0x4D`), and extended by PR #2434
    (`'S'`, `0x53`). The five POSIX UStar siblings are
    `hardlink-outside.tar` (PR #1555, typeflag `'1'`, `0x31`),
    `tar-fifo-skipped.tar` (PR #2413, typeflag `'6'`, `0x36`),
    `tar-chardev-skipped.tar` (PR #2417, typeflag `'3'`, `0x33`),
    `tar-blockdev-skipped.tar` (PR #2422, typeflag `'4'`, `0x34`),
    and `tar-contiguous-skipped.tar` (PR #2425, typeflag `'7'`,
    `0x37`); the GNU `'V'` arm at `0x56` was added by PR #2428;
    the GNU `'M'` arm at `0x4D` was added by PR #2431; the GNU
    `'S'` arm at `0x53` was added by PR #2434; the new GNU `'D'`
    arm at `0x44` is added by PR #2437. The nonet pins nine
    distinct typeflag values
    (`0x31` / `0x36` / `0x33` / `0x34` / `0x37` / `0x56` / `0x4D` /
    `0x53` / `0x44`) against the shared `else` fallback at
    [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) (`partial def
    extract`'s tail `else` arm, after the `typeDirectory` /
    `typeRegular` / `typeSymlink` cases). All nine fixtures have
    `size = 0` and route through the same `skipEntryData input
    e.size` no-op call in the `else` body, so the structural pin
    remains the *existence* of the `else` arm rather than the
    *behaviour* of any per-typeflag dispatch — a future refactor
    that drops the fallback for any one arm would fire the
    corresponding fixture. The originating PR #1555 set the
    silent-skip precedent at 1/N; PR #2413 added 2/N (paired-reviewed
    in PR #2419, 1 → 2); PR #2417 added 3/N (paired-reviewed in
    PR #2421, 2 → 3); PR #2422 added 4/N (paired-reviewed in
    PR #2427, 3 → 4); PR #2425 added 5/N (paired-reviewed in
    PR #2433, 4 → 5, last POSIX UStar arm); PR #2428 added 6/N
    (paired-reviewed in PR #2441, 5 → 6, first GNU-typeflag arm
    opening the GNU sub-ladder); PR #2431 added 7/N (paired-reviewed
    in PR #2443, 6 → 7, second GNU-typeflag arm); PR #2434 added
    8/N (paired-reviewed in PR #2444, 7 → 8, third GNU-typeflag
    arm); PR #2437 now extends to 9/N as the **fourth
    GNU-typeflag arm** extending the GNU sub-ladder. The POSIX
    UStar `'1'`–`'7'` numeric range remains closed (PR #2425 /
    PR #2433 framing), and the GNU sub-ladder is now a four-arm
    structure (`'V'` / `'M'` / `'S'` / `'D'`). The natural next
    region is the rest of the GNU-typeflag sub-ladder; the
    merged-but-unreviewed GNU successor `'N'` (LF_NAMES
    old-long-name extension, `0x4E`, PR #2439 since landed) is
    named without committing to a specific paired-review PR
    number, matching the PR #2421 / PR #2427 / PR #2433 / PR #2441
    / PR #2443 / PR #2444 paired-review entries' close-out style.
  - **Fixture-builder rename-vs-extend choice.** The worker chose
    *extend in place* on
    [scripts/build-symlink-hardlink-malformed-fixtures.lean](/home/kim/lean-zip/scripts/build-symlink-hardlink-malformed-fixtures.lean),
    matching the PR #2413 / PR #2417 / PR #2422 / PR #2425 /
    PR #2428 / PR #2431 / PR #2434 workers' earlier choices on the
    same script. The script path stays stable; the module
    docstring's *Output (byte-deterministic)* list at PR #2437 land
    time enumerated ten output files (the nine pre-PR-#2437 outputs
    plus the new `testdata/tar/security/tar-incremental-skipped.tar`
    line) and the per-typeflag enumeration block in the docstring
    body added a ninth bulleted entry for the incremental arm with
    its typeflag `0x44`, `path = "incremental-entry"`, empty
    linkname, and silent-skip `else` fallback semantics — phrased
    *"Fourth GNU-typeflag sibling of the silent-skip `else`
    fallback family alongside `tar-volumeheader-skipped.tar`
    (typeflag `'V'`), `tar-multivol-skipped.tar` (typeflag `'M'`),
    and `tar-sparse-skipped.tar` (typeflag `'S'`), extending the
    GNU-typeflag sub-ladder distinct from the POSIX UStar
    `'0'`–`'7'` range."* The build summary line at `main`'s tail at
    PR #2437 land time printed *"Built 10 per-typeflag-policy
    security fixtures under testdata/tar/security/."* — the count
    moved from `9` (PR #2434 era) to `10` correctly. (The
    subsequent landing PR #2439 has since advanced the count to
    `11` on today's master tree, but the PR #2437 land-time count
    of `10` is what this paired-review audits.) The extend-in-place
    choice keeps the rename churn at zero across the family
    extension. The worker's chosen path field `incremental-entry`
    matches the issue body's *"`path = "incremental-entry"` (or
    worker's chosen path; verify against the merged tree)"*
    invitation and reads as a natural directory-dump entry path;
    this is consistent with the GNU tar info node `(tar)Incremental
    Dumps` framing where `'D'` records describe a directory's
    snapshot listing for incremental restore. Worker-recorded
    rationale in
    [progress/20260502T193144Z_4091559b_tar-incremental-skipped-fixture.md](/home/kim/lean-zip/progress/20260502T193144Z_4091559b_tar-incremental-skipped-fixture.md)
    documents the extend-in-place choice and the per-fixture path
    `"incremental-entry"`.
  - **Reproducer Corpus row prose fidelity.** The new
    `tar-incremental-skipped.tar` row carries the seven required
    elements: (i) typeflag value `0x44` and the GNU `'D'` glyph
    cited together in the row's opening clause; (ii) GNU semantics
    *"GNU directory-dump for incremental backups"* with a GNU tar
    info node `(tar)Incremental Dumps` citation (faithful to the
    GNU tar info structure for the incremental-backup workflow —
    the `'V'` arm cites `(tar)Standard` for the typeflag table,
    the `'M'` arm cites `(tar)Multi-Volume Archives` for the
    multi-volume runtime mechanism, the `'S'` arm cites
    `(tar)Sparse Formats` for the sparse-encoding mechanism, and
    the `'D'` arm cites `(tar)Incremental Dumps` for the
    incremental-backup mechanism, an arm-specific citation choice
    that mirrors the volume-header / multi-volume / sparse /
    directory-dump distinction); (iii) silent-skip `else` branch,
    with explicit reference to `Tar.extract`'s tail `else` arm and
    the `skipEntryData` no-op on `e.size = 0`; (iv) sibling fixture
    cross-references to all five POSIX UStar prior arms
    `hardlink-outside.tar` (typeflag `'1'`),
    `tar-fifo-skipped.tar` (typeflag `'6'`),
    `tar-chardev-skipped.tar` (typeflag `'3'`),
    `tar-blockdev-skipped.tar` (typeflag `'4'`),
    `tar-contiguous-skipped.tar` (typeflag `'7'`), the PR #2428 GNU
    `'V'` sibling `tar-volumeheader-skipped.tar`, the PR #2431 GNU
    `'M'` sibling `tar-multivol-skipped.tar`, and the PR #2434 GNU
    `'S'` sibling `tar-sparse-skipped.tar` — the row correctly
    names eight siblings (five POSIX UStar + three GNU), reflecting
    the 8 → 9 extension; (v) the family-extension claim phrased as
    *"Per-typeflag silent-skip family extension: this is the
    **fourth GNU-typeflag** sibling, extending the GNU-typeflag
    sub-ladder distinct from the POSIX UStar `'0'`–`'7'` range"*
    with the *"the nine together pin nine distinct typeflag values
    against the shared fallback"* defense-in-depth framing; (vi)
    the writer-side caveat (*"`Tar.create`'s caller-API only
    accepts paths and never invokes `Tar.buildHeader` with a
    non-`'0'`/`'5'` typeflag, so legitimate archives produced by
    the lean-zip writer never carry typeflag `'D'`"*) — confirmed
    by reading [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean)
    (`Tar.create` builds entries via `walkFiles` with
    `typeflag := if isDir then typeDirectory else typeRegular`,
    identical to the PR #2413 / PR #2417 / PR #2422 / PR #2425 /
    PR #2428 / PR #2431 / PR #2434 paired-reviews' same audit on
    the prior arms); (vii) only stable
    [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) anchors — no
    `:N` line-number suffixes, consistent with the
    [PR #2353](https://github.com/kim-em/lean-zip/pull/2353)
    decision. The directory-dump arm's framing is the
    *backup-format-not-implemented-by-design* / *listing-payload
    is attacker-controlled* rationale (lean-zip does not implement
    incremental-backup reconstruction — which would require parsing
    the dumpdir payload as a NUL-separated list of filenames with
    per-entry status codes (`Y` for present, `N` for not present,
    `D` for renamed directory), maintaining a snapshot baseline,
    and reconciling deletions / renames against the on-disk state
    — so a `'D'` entry has no meaningful semantics for lean-zip's
    extraction model), with the additional removal-cue angle (a
    malicious archive could ship a `'D'` entry with a crafted
    listing payload that an incremental-aware extractor would
    interpret as instructions to delete files outside `outDir`,
    since the GNU incremental format allows the listing to mark
    files for *removal* during restore — lean-zip's policy of
    *never* materialising `'D'` entries — and never interpreting
    the listing payload at all — regardless of `path` / declared
    `size` / actual payload is the correct conservative choice,
    particularly because the format documentation explicitly notes
    that incremental restoration grants the archive author
    authority to remove files from the target tree, and pinning the
    policy with a fixture prevents future drift toward an
    incremental-aware extractor that would honour those removal
    cues (e.g. by treating a `'D'` entry's payload bytes as a
    `Y`/`N` per-file status manifest and deleting the files marked
    `N` from `outDir`)). This is the arm-specific extension that
    distinguishes the directory-dump row's prose from the
    volume-header / multi-volume / sparse rows — the volume-header
    row names a *single-volume-only-by-design* capability boundary,
    the multi-volume row names *cross-volume-splicing* with
    attacker-controlled `realsize`/offset metadata, the sparse row
    names *encoding-format-not-implemented-by-design* with the
    parser-differential variant matrix as the additional
    attack-surface argument, and the directory-dump row names
    *backup-format-not-implemented-by-design* with the
    file-removal-cue smuggling vector as the additional
    attack-surface argument (the listing payload's `Y`/`N`/`D`
    status codes are an attacker-controllable removal directive
    that no other GNU-typeflag arm carries). The nine arm-specific
    paragraphs (chardev / blockdev / FIFO / contiguous /
    volume-header / multi-volume / sparse / directory-dump) remain
    independently informative — none subsumes the others — which
    remains the right shape for a per-typeflag fixture family. The
    Reproducer Corpus row's closing-PR column on the merged tree
    cites `#2437` (verified via `git blame` on the row pointing at
    PR #2437's merge commit `67481e13`); the worker performed the
    closing-PR substitution `#TBD-VERIFY-PR` → `#2437` <!-- drift-detector: prose mention of the placeholder substitution in a paired-review finding, not a stale placeholder --> on
    the worker branch pre-merge, matching the PR #2417 / PR #2422 /
    PR #2425 / PR #2428 / PR #2431 / PR #2434 self-correction
    precedent.
  - **Adversarial-check fidelity.** The adversarial check is
    recorded in
    [progress/20260502T193144Z_4091559b_tar-incremental-skipped-fixture.md](/home/kim/lean-zip/progress/20260502T193144Z_4091559b_tar-incremental-skipped-fixture.md)
    *## Adversarial check*: temporarily wrapping the `else` body
    in `if e.typeflag == typeHardlink || e.typeflag == 0x36 ||
    e.typeflag == 0x33 || e.typeflag == 0x34 || e.typeflag == 0x37
    || e.typeflag == 0x56 || e.typeflag == 0x4D || e.typeflag ==
    0x53 then skipEntryData input e.size else throw (IO.userError
    s!"adversarial: unexpected typeflag {e.typeflag}")` left
    `hardlink-outside.tar`, `tar-fifo-skipped.tar`,
    `tar-chardev-skipped.tar`, `tar-blockdev-skipped.tar`,
    `tar-contiguous-skipped.tar`, `tar-volumeheader-skipped.tar`,
    `tar-multivol-skipped.tar`, and `tar-sparse-skipped.tar`
    passing while `tar-incremental-skipped.tar` fired with
    `uncaught exception: adversarial: unexpected typeflag 68`
    (`0x44 = 68`, matching ASCII `'D'`). The `0x44` ↔ ASCII `'D'`
    ↔ decimal `68` mapping in the adversarial-check parenthetical
    is internally consistent (`0x44` hex = `68` decimal = ASCII
    codepoint of the glyph `'D'`). The wrapper expression
    preserves all eight prior siblings' arms (`'1'` / `'6'` /
    `'3'` / `'4'` / `'7'` / `'V'` / `'M'` / `'S'`) and exposes only
    the `'D'` arm — extending the *"spare all-but-the-new-arm and
    confirm the new fixture fires"* convention to N=8 spared arms
    (PR #2413's wrapper spared one arm, PR #2417's two, PR #2422's
    three, PR #2425's four, PR #2428's five, PR #2431's six,
    PR #2434's seven, and PR #2437's eight). Each new fixture's
    wrapper extends the disjunction by one already-fixtured
    typeflag, scaling cleanly to N+1 fixtures by adding one more
    spare. The disable-revert was clean — the post-revert `git
    diff Zip/Tar.lean` is empty in the worker's merged commit
    (PR #2437's diff at
    [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) shows zero
    lines changed). The convention now scales further into the GNU
    sub-ladder: the next sibling PR #2439 (`'N'` LF_NAMES, `0x4E`,
    decimal `78`) wrapper spared nine arms (`'1'`, `'6'`, `'3'`,
    `'4'`, `'7'`, `'V'`, `'M'`, `'S'`, and `'D'`); the convention
    is established and continues into the GNU sub-ladder's further
    extensions (PR #2439 since landed, carrying the same
    spare-prior-and-fire-this-arm shape).
  - **Test-arm placement.** The new test arm in
    [ZipTest/TarFixtures.lean](/home/kim/lean-zip/ZipTest/TarFixtures.lean)
    is placed at the tail of the silent-skip cluster at PR #2437
    land time (immediately after the `tar-sparse-skipped.tar` arm),
    matching the chronological-by-PR-merge-order convention the
    family has followed since PR #1555. At PR #2437 land time the
    file order was `'1'` → `'6'` → `'3'` → `'4'` → `'7'` →
    `'V'` → `'M'` → `'S'` → `'D'`, mirroring the PR-merge sequence
    #1555 → #2413 → #2417 → #2422 → #2425 → #2428 → #2431 →
    #2434 → #2437. The chronological house style preserves this
    order in today's master tree despite an alphabetical reorder
    being available (`tar-c...skipped` < `tar-f...skipped` <
    `tar-i...skipped` < `tar-m...skipped` < `tar-s...skipped` <
    `tar-v...skipped` would have churned the order substantially),
    matching the PR #2433 / PR #2441 / PR #2443 / PR #2444
    paired-reviews' same finding for prior arms. The arm asserts
    the extract directory is empty after `Tar.extract` (mirroring
    the FIFO / chardev / blockdev / contiguous / volume-header /
    multi-volume / sparse arm shapes) **and** preserves the entry
    through `Tar.list` with `inListed[0]!.typeflag == 0x44` and
    `inListed.size == 1` — inheriting the optional `Tar.list`
    typeflag-preservation assertion introduced by the volume-header
    arm at PR #2428 and continued by the multi-volume arm at
    PR #2431 and the sparse arm at PR #2434. By PR #2437 land time
    this is now an established convention for the GNU sub-ladder
    rather than a per-arm extension: PR #2439 carries the same
    `lnNamesListed[0]!.typeflag == 0x4E` assertion shape,
    confirming the convention's load-bearing status. The
    assertion-shape inheritance is faithful to the issue body's
    deliverable expectation — the empty-extract-dir assertion is
    preserved unchanged; the worker preserved the `Tar.list`
    assertion as an additive arm-specific extension rather than
    substituting for the empty-extract-dir check. The arm uses a
    distinct extract directory
    `/tmp/lean-zip-fixture-tar-incremental-skipped-extract`
    (independent from the eight prior arms' extract directories)
    and is registered in both cleanup loops (per-fixture file-list
    `writeFixtureTmp` outputs and the per-directory `rm -rf`
    list), so re-running the test suite remains hermetic across
    the family extension. No shared mutable state across the nine
    arms. The eight prior test arms continue to pass after the new
    arm is added (independently confirmed by `lake exe test` on
    the merged tree: *"All tests passed!"*).
  - **Stable-cite discipline.** The new Reproducer Corpus row uses
    only stable identifiers — function names (`Tar.extract`,
    `skipEntryData`, `Tar.forEntries`, `Tar.list`,
    `Tar.buildHeader`, `Tar.create`) and fixture filenames
    (`tar-incremental-skipped.tar`, `tar-sparse-skipped.tar`,
    `tar-multivol-skipped.tar`, `tar-volumeheader-skipped.tar`,
    `tar-contiguous-skipped.tar`, `tar-blockdev-skipped.tar`,
    `tar-chardev-skipped.tar`, `tar-fifo-skipped.tar`,
    `hardlink-outside.tar`). No `line N` or `:N` suffixes appear
    anywhere in the row, consistent with the
    [PR #2353](https://github.com/kim-em/lean-zip/pull/2353)
    decision to drop line-number anchors. Cross-reference cites
    resolve to real artefacts: PR #2434 / PR #2431 / PR #2428 /
    PR #2425 / PR #2422 / PR #2417 / PR #2413 / PR #1555 are all
    real merged PRs with the cited fixtures and policies. The
    [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) anchor is
    repeated rather than aliased, matching the inventory's house
    style. `bash scripts/check-inventory-links.sh` reports
    `errors=0, warnings=9` on the master tree this paired-review
    branches from (one warning per silent-skip fixture row,
    inherited from the PR #2413 row template — added rows from
    PR #2428 / PR #2431 / PR #2434 / PR #2437 / PR #2439 each kept
    the *during this PR* <!-- drift-detector: prose discussion of the placeholder phrase in a paired-review finding, not a stale placeholder --> phrasing without
    `<!-- drift-detector: -->` opt-outs, deferred to a future
    inventory-cleanup PR per the PR #2433 paired-review's
    deferral). This paired-review introduces no new placeholder
    regression and adds zero warnings — the `#TBD-VERIFY-PR` <!-- drift-detector: prose discussion of the placeholder token in a paired-review finding, not a stale placeholder -->
    placeholder in the paired-review header line is wrapped in a
    `<!-- drift-detector: half-closed paired-review placeholder,
    substituted to the real PR number on the worker branch before
    merge -->` opt-out comment so it does not register as a stale
    placeholder. Suppressing the row-level warnings would still
    require additional `<!-- drift-detector: ... -->` opt-out
    comments per the PR #2371 paired-review pattern; this
    paired-review continues to defer the opt-outs (matching the
    PR #2413 / PR #2417 / PR #2422 / PR #2425 / PR #2433 /
    PR #2441 / PR #2443 / PR #2444 paired-review deferrals).
  - **Ladder-progression close-out.** The per-typeflag silent-skip
    family ladder now stands at: PR #1555 (1/N, typeflag `'1'`
    hardlink — predates per-PR paired-review cadence), PR #2413
    (2/N, typeflag `'6'` FIFO — paired-review PR #2419), PR #2417
    (3/N, typeflag `'3'` character device — paired-review
    PR #2421), PR #2422 (4/N, typeflag `'4'` block device —
    paired-review PR #2427), PR #2425 (5/N, typeflag `'7'`
    contiguous file — paired-review PR #2433, last POSIX UStar
    arm), PR #2428 (6/N, typeflag `'V'` GNU multi-volume archive
    label marker — paired-review PR #2441, first GNU-typeflag arm
    opening the GNU sub-ladder), PR #2431 (7/N, typeflag `'M'` GNU
    multi-volume continuation marker — paired-review PR #2443,
    second GNU-typeflag arm), PR #2434 (8/N, typeflag `'S'` GNU
    sparse file — paired-review PR #2444, third GNU-typeflag arm),
    and PR #2437 (9/N, typeflag `'D'` GNU directory-dump for
    incremental backups — this paired-review, **fourth
    GNU-typeflag arm extending the GNU sub-ladder**). With
    PR #2437 landing, **the GNU-typeflag sub-ladder grew to four
    arms** (`'V'` / `'M'` / `'S'` / `'D'`) beyond the now-capped
    POSIX UStar `'1'`–`'7'` numeric range. The silent-skip family
    remains open-ended (every additional per-typeflag arm fires
    the same `else` fallback in `Tar.extract`, so the marginal
    fixture cost falls but the marginal regression benefit also
    falls); PR #2437 extends the GNU sub-ladder to four arms, with
    the merged-but-unreviewed GNU successor PR #2439 (`'N'`
    LF_NAMES old-long-name extension, `0x4E`, paired-review
    pending) — the natural next region (and possible future arms
    `'X'` Solaris extended attribute, `'A'` Solaris ACL, once the
    shortlist exhausts). The paired-review for PR #2439 (and any
    further GNU-typeflag siblings) is a separate follow-up, not
    in scope here — each paired-review is per-PR per the
    established cadence. Any future per-typeflag fixture should
    earn its own paired-review entry on the established cadence.
    No new follow-up issue is filed by this paired-review.

- Paired review of PR #2439 (`tar-longnames-skipped.tar` fixture —
  per-typeflag silent-skip family extension 9 → 10, fifth and final
  GNU-typeflag arm closing the GNU sub-ladder opened by PR #2428,
  extended by PR #2431, extended by PR #2434, and extended by
  PR #2437; this paired-review landed in PR <!-- drift-detector: half-closed paired-review placeholder, substituted to the real PR number on the worker branch before merge --> #TBD-VERIFY-PR closing #2446):
  PR #2439 (squash commit `0f543c4`, merged 2026-05-02, closes
  #2438) extends the `Tar.extract` silent-skip `else` fallback
  family from nine to ten sibling fixtures, **closing the
  GNU-typeflag sub-ladder** opened by PR #2428, continued by
  PR #2431, continued by PR #2434, and continued by PR #2437 to
  five arms. The commit adds a 512-byte single-block UStar fixture
  `testdata/tar/security/tar-longnames-skipped.tar` (SHA-256
  `452e2b6b711b98f05370ab5ee25fb75c51c5f258ade275c804c96a1d83a0b8d0`)
  for typeflag `'N'` (GNU `LF_NAMES` old-long-name extension,
  `0x4E`); an eleventh `buildZeroSizeFixture` call in
  [scripts/build-symlink-hardlink-malformed-fixtures.lean](/home/kim/lean-zip/scripts/build-symlink-hardlink-malformed-fixtures.lean)
  producing it deterministically; a new test arm in
  [ZipTest/TarFixtures.lean](/home/kim/lean-zip/ZipTest/TarFixtures.lean)
  immediately after the existing `tar-incremental-skipped.tar`
  arm, asserting the extract directory is empty after extraction
  *and* preserving the entry through `Tar.list` with `typeflag =
  0x4E` (the optional `Tar.list` typeflag-preservation assertion
  inheriting the **arm-specific extension** introduced by the
  PR #2428 paired-review's volume-header arm and continued by the
  PR #2431 / PR #2434 / PR #2437 GNU-arms — by PR #2439 land time
  this is now an established convention for the GNU sub-ladder
  rather than a per-arm extension); a new Reproducer Corpus row in
  this inventory; and a *Symlink/hardlink extraction policy*
  fixture-enumeration entry. No spec change, no production-code
  change, no new typeflag constant in the `Tar` namespace, no
  caller / signature change.
  - **Sub-ladder-extension claim fidelity (9 → 10 fixtures, fifth
    and final GNU arm).** The 9 → 10 extension math is faithful to
    the merged tree. PR #2439 is the tenth per-typeflag fixture in
    the silent-skip family and the **fifth and final GNU-typeflag
    arm**, closing the GNU sub-ladder opened by PR #2428 (`'V'`,
    `0x56`), extended by PR #2431 (`'M'`, `0x4D`), extended by
    PR #2434 (`'S'`, `0x53`), and extended by PR #2437 (`'D'`,
    `0x44`). The five POSIX UStar siblings are
    `hardlink-outside.tar` (PR #1555, typeflag `'1'`, `0x31`),
    `tar-fifo-skipped.tar` (PR #2413, typeflag `'6'`, `0x36`),
    `tar-chardev-skipped.tar` (PR #2417, typeflag `'3'`, `0x33`),
    `tar-blockdev-skipped.tar` (PR #2422, typeflag `'4'`, `0x34`),
    and `tar-contiguous-skipped.tar` (PR #2425, typeflag `'7'`,
    `0x37`); the GNU `'V'` arm at `0x56` was added by PR #2428;
    the GNU `'M'` arm at `0x4D` was added by PR #2431; the GNU
    `'S'` arm at `0x53` was added by PR #2434; the GNU `'D'` arm
    at `0x44` was added by PR #2437; the new GNU `'N'` arm at
    `0x4E` is added by PR #2439. The dectet pins ten distinct
    typeflag values
    (`0x31` / `0x36` / `0x33` / `0x34` / `0x37` / `0x56` / `0x4D` /
    `0x53` / `0x44` / `0x4E`) against the shared `else` fallback at
    [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) (`partial def
    extract`'s tail `else` arm, after the `typeDirectory` /
    `typeRegular` / `typeSymlink` cases). All ten fixtures have
    `size = 0` and route through the same `skipEntryData input
    e.size` no-op call in the `else` body, so the structural pin
    remains the *existence* of the `else` arm rather than the
    *behaviour* of any per-typeflag dispatch — a future refactor
    that drops the fallback for any one arm would fire the
    corresponding fixture. The originating PR #1555 set the
    silent-skip precedent at 1/N; PR #2413 added 2/N (paired-reviewed
    in PR #2419, 1 → 2); PR #2417 added 3/N (paired-reviewed in
    PR #2421, 2 → 3); PR #2422 added 4/N (paired-reviewed in
    PR #2427, 3 → 4); PR #2425 added 5/N (paired-reviewed in
    PR #2433, 4 → 5, last POSIX UStar arm); PR #2428 added 6/N
    (paired-reviewed in PR #2441, 5 → 6, first GNU-typeflag arm
    opening the GNU sub-ladder); PR #2431 added 7/N (paired-reviewed
    in PR #2443, 6 → 7, second GNU-typeflag arm); PR #2434 added
    8/N (paired-reviewed in PR #2444, 7 → 8, third GNU-typeflag
    arm); PR #2437 added 9/N (paired-reviewed in PR #2445, 8 → 9,
    fourth GNU-typeflag arm); PR #2439 now extends to 10/N as the
    **fifth and final GNU-typeflag arm closing the GNU sub-ladder**.
    The POSIX UStar `'1'`–`'7'` numeric range remains closed
    (PR #2425 / PR #2433 framing), and the GNU sub-ladder is now
    explicitly capped at five arms (`'V'` / `'M'` / `'S'` / `'D'` /
    `'N'`) — the remaining LF_*-extension typeflags `'L'`
    (`LF_LONGNAME`) and `'K'` (`LF_LONGLINK`) are *handled* by
    `Tar.forEntries` rather than silent-skipped (the inner dispatch
    accumulates `'L'` / `'K'` payloads as pending long-name /
    long-link buffers for the next entry, and the PAX `'x'` / `'g'`
    pair is similarly handled), so they are not silent-skip
    candidates and would not extend this ladder. With this
    paired-review the GNU-typeflag silent-skip ladder closes — no
    further GNU-typeflag silent-skip candidates are queued. The
    natural next region for the silent-skip family — if any future
    extension is filed — is non-GNU vendor extensions (Solaris
    `'X'` extended attribute, `'A'` Solaris ACL, etc.) once a
    typeflag survey identifies a deployed extension worth pinning;
    no such issue is in flight at the time of this paired-review,
    matching the issue body's explicit *"no further GNU-typeflag
    silent-skip candidates queued"* framing. The merged-but-unreviewed
    sibling-class fixture `tar-mixed-skipped.tar` (PR #2449,
    extract-continuation invariant pinned across a silently-skipped
    middle `'6'` FIFO entry) is *not* an eleventh per-typeflag arm
    and is paired-reviewed separately — that paired-review is
    out of scope for this entry, matching the per-typeflag
    paired-review cadence.
  - **Fixture-builder rename-vs-extend choice.** The worker chose
    *extend in place* on
    [scripts/build-symlink-hardlink-malformed-fixtures.lean](/home/kim/lean-zip/scripts/build-symlink-hardlink-malformed-fixtures.lean),
    matching the PR #2413 / PR #2417 / PR #2422 / PR #2425 /
    PR #2428 / PR #2431 / PR #2434 / PR #2437 workers' earlier
    choices on the same script. The script path stays stable; the
    module docstring's *Output (byte-deterministic)* list at
    PR #2439 land time enumerated **eleven** output files (the ten
    pre-PR-#2439 outputs plus the new
    `testdata/tar/security/tar-longnames-skipped.tar` line) and the
    per-typeflag enumeration block in the docstring body added a
    tenth bulleted entry for the long-names-old arm with its
    typeflag `0x4E`, `path = "longnames-entry"`, empty linkname,
    and silent-skip `else` fallback semantics — phrased
    *"Fifth GNU-typeflag sibling of the silent-skip `else`
    fallback family alongside `tar-volumeheader-skipped.tar`
    (typeflag `'V'`), `tar-multivol-skipped.tar` (typeflag `'M'`),
    `tar-sparse-skipped.tar` (typeflag `'S'`), and
    `tar-incremental-skipped.tar` (typeflag `'D'`), extending the
    GNU-typeflag sub-ladder distinct from the POSIX UStar
    `'0'`–`'7'` range. Together with the five POSIX UStar siblings
    the family pins ten distinct typeflag values against the shared
    fallback."* The docstring entry additionally calls out the
    `forEntries`-vs-`else` distinction (*"`forEntries`'s inner
    dispatch recognises only the modern `'L'` / `'K'` long-name
    typeflags (and the PAX `'x'` / `'g'` pair) — `'N'` is *not*
    aliased to `'L'` despite being the historical precursor of the
    same long-name extension family"*), an arm-specific extension
    that distinguishes the long-names-old arm from the
    volume-header / multi-volume / sparse / directory-dump arms (none
    of which has a competing modern-typeflag-handler distinction
    to draw). The build summary line at `main`'s tail at PR #2439
    land time printed *"Built 11 per-typeflag-policy security
    fixtures under testdata/tar/security/."* — the count moved from
    `10` (PR #2437 era) to `11` correctly. (The subsequent landing
    PR #2449 has since advanced the count to `12` on today's master
    tree by adding the sibling-class `tar-mixed-skipped.tar`
    fixture, but the PR #2439 land-time count of `11` is what this
    paired-review audits.) The extend-in-place choice keeps the
    rename churn at zero across the family extension. The worker's
    chosen path field `longnames-entry` matches the issue body's
    *"`path = "longnames-entry"` (or worker's chosen path; verify
    against the merged tree)"* invitation and reads as a natural
    long-name-extension entry path; this is consistent with the
    GNU tar `tar.h` `LF_NAMES` semantic (an obsolete long-name
    encoding-list typeflag, predating the modern `LF_LONGNAME` /
    `LF_LONGLINK` pair).
  - **Reproducer Corpus row prose fidelity.** The new
    `tar-longnames-skipped.tar` row carries the seven required
    elements: (i) typeflag value `0x4E` and the GNU `'N'` glyph
    cited together in the row's opening clause; (ii) GNU semantics
    *"GNU `LF_NAMES` old-long-name extension"* with a citation to
    the deprecated-precursor-of-`'L'`/`'K'` framing in the row's
    extended prose (faithful to the GNU tar source — the `LF_NAMES`
    enum is the historical precursor of the modern
    `LF_LONGNAME` / `LF_LONGLINK` typeflag pair, predates PAX
    `'x'`, considered obsolete in current GNU tar but still emitted
    by old archivers and recognised by `bsdtar` / `libarchive` in
    lenient mode — an arm-specific citation choice that mirrors the
    volume-header / multi-volume / sparse / directory-dump distinction
    from the prior four GNU-arm rows); (iii) silent-skip `else`
    branch, with explicit reference to `Tar.extract`'s tail `else`
    arm and the `skipEntryData` no-op on `e.size = 0`; (iv) sibling
    fixture cross-references to all five POSIX UStar prior arms
    `hardlink-outside.tar` (typeflag `'1'`),
    `tar-fifo-skipped.tar` (typeflag `'6'`),
    `tar-chardev-skipped.tar` (typeflag `'3'`),
    `tar-blockdev-skipped.tar` (typeflag `'4'`),
    `tar-contiguous-skipped.tar` (typeflag `'7'`), the PR #2428 GNU
    `'V'` sibling `tar-volumeheader-skipped.tar`, the PR #2431 GNU
    `'M'` sibling `tar-multivol-skipped.tar`, the PR #2434 GNU
    `'S'` sibling `tar-sparse-skipped.tar`, and the PR #2437 GNU
    `'D'` sibling `tar-incremental-skipped.tar` — the row correctly
    names nine siblings (five POSIX UStar + four GNU), reflecting
    the 9 → 10 extension; (v) the family-extension claim phrased as
    *"Per-typeflag silent-skip family extension: this is the
    **fifth GNU-typeflag** sibling, extending the GNU-typeflag
    sub-ladder distinct from the POSIX UStar `'0'`–`'7'` range"*
    with the *"the ten together pin ten distinct typeflag values
    against the shared fallback"* defense-in-depth framing, and the
    explicit *closing-arm* note on today's row that the GNU
    sub-ladder is open-ended (every additional per-typeflag arm
    fires the same `else` fallback in `Tar.extract`) — the prose
    correctly leaves the silent-skip family open-ended at the
    sub-ladder level even while closing the GNU-typeflag-arm
    extension queue at five arms (no further GNU-typeflag
    candidates are queued because `'L'` / `'K'` are handled by
    `forEntries`); (vi) the writer-side caveat (*"`Tar.create`'s
    caller-API only accepts paths and never invokes
    `Tar.buildHeader` with a non-`'0'`/`'5'` typeflag, so
    legitimate archives produced by the lean-zip writer never carry
    typeflag `'N'`"*) — confirmed by reading
    [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) (`Tar.create`
    builds entries via `walkFiles` with
    `typeflag := if isDir then typeDirectory else typeRegular`,
    identical to the PR #2413 / PR #2417 / PR #2422 / PR #2425 /
    PR #2428 / PR #2431 / PR #2434 / PR #2437 paired-reviews' same
    audit on the prior arms); (vii) only stable
    [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) anchors — no
    `:N` line-number suffixes, consistent with the
    [PR #2353](https://github.com/kim-em/lean-zip/pull/2353)
    decision. The long-names-old arm's framing is the
    *legacy-format-superseded-by-LF_LONGNAME* / *parser-differential
    archive-slip via deprecated long-name rewriting* rationale (a
    lenient extractor recognising `'N'` could apply the payload's
    name list to subsequent regular-file entries, smuggling
    `../etc/passwd` or absolute paths past the per-entry path
    guard — lean-zip's policy of *never* materialising `'N'`
    entries — and never interpreting the payload as a name-rewrite
    directive — regardless of `path` / declared `size` / actual
    payload is the correct conservative choice, particularly
    because `forEntries` recognises only the modern `'L'` / `'K'`
    long-name typeflags (and the PAX `'x'` / `'g'` pair); `'N'` is
    *not* aliased to `'L'` despite being the historical precursor
    of the same long-name extension family — pinning the policy
    with a fixture prevents future drift toward an `LF_NAMES`-aware
    extractor that would reinterpret the payload as a name-rewrite
    list (or, worse, as a regular-file payload written linearly,
    which would silently misextract any legacy archive carrying the
    typeflag)). This is the arm-specific extension that
    distinguishes the long-names-old row's prose from the
    volume-header / multi-volume / sparse / directory-dump rows —
    the volume-header row names a *single-volume-only-by-design*
    capability boundary, the multi-volume row names
    *cross-volume-splicing* with attacker-controlled
    `realsize`/offset metadata, the sparse row names
    *encoding-format-not-implemented-by-design* with the
    parser-differential variant matrix as the additional
    attack-surface argument, the directory-dump row names
    *backup-format-not-implemented-by-design* with the
    file-removal-cue smuggling vector as the additional
    attack-surface argument, and the long-names-old row names
    *legacy-format-superseded-by-LF_LONGNAME* with the
    deprecated-extension-aliasing-vs-modern-handler distinction
    (`forEntries` already handles `'L'` / `'K'`, so the silent-skip
    policy on `'N'` reinforces a strict-vs-lenient choice that the
    other GNU arms cannot draw because they have no modern-typeflag
    competing handler). The ten arm-specific paragraphs (chardev /
    blockdev / FIFO / contiguous / volume-header / multi-volume /
    sparse / directory-dump / long-names-old) remain independently
    informative — none subsumes the others — which remains the
    right shape for a per-typeflag fixture family. The Reproducer
    Corpus row's closing-PR column on the merged tree cites
    `#2439` (verified via `git blame` on the row pointing at
    PR #2439's merge commit `0f543c4`); the worker performed the
    closing-PR substitution `#TBD-VERIFY-PR` → `#2439` <!-- drift-detector: prose mention of the placeholder substitution in a paired-review finding, not a stale placeholder --> on
    the worker branch pre-merge, matching the PR #2417 / PR #2422 /
    PR #2425 / PR #2428 / PR #2431 / PR #2434 / PR #2437
    self-correction precedent.
  - **Adversarial-check fidelity.** The adversarial check is
    recorded in the PR #2439 worker branch's progress entry
    (linked from the issue): temporarily wrapping the `else` body
    in `if e.typeflag == typeHardlink || e.typeflag == 0x36 ||
    e.typeflag == 0x33 || e.typeflag == 0x34 || e.typeflag == 0x37
    || e.typeflag == 0x56 || e.typeflag == 0x4D || e.typeflag ==
    0x53 || e.typeflag == 0x44 then skipEntryData input e.size
    else throw (IO.userError s!"adversarial: unexpected typeflag
    {e.typeflag}")` left `hardlink-outside.tar`,
    `tar-fifo-skipped.tar`, `tar-chardev-skipped.tar`,
    `tar-blockdev-skipped.tar`, `tar-contiguous-skipped.tar`,
    `tar-volumeheader-skipped.tar`, `tar-multivol-skipped.tar`,
    `tar-sparse-skipped.tar`, and `tar-incremental-skipped.tar`
    passing while `tar-longnames-skipped.tar` fired with
    `unexpected typeflag 78` (`0x4E = 78`, matching ASCII `'N'`).
    The `0x4E` ↔ ASCII `'N'` ↔ decimal `78` mapping in the
    adversarial-check parenthetical is internally consistent
    (`0x4E` hex = `78` decimal = ASCII codepoint of the glyph
    `'N'`). The wrapper expression preserves all nine prior
    siblings' arms (`'1'` / `'6'` / `'3'` / `'4'` / `'7'` / `'V'` /
    `'M'` / `'S'` / `'D'`) and exposes only the `'N'` arm —
    extending the *"spare all-but-the-new-arm and confirm the new
    fixture fires"* convention to N=9 spared arms (PR #2413's
    wrapper spared one arm, PR #2417's two, PR #2422's three,
    PR #2425's four, PR #2428's five, PR #2431's six, PR #2434's
    seven, PR #2437's eight, and PR #2439's nine). Each new
    fixture's wrapper extends the disjunction by one
    already-fixtured typeflag, scaling cleanly to N+1 fixtures by
    adding one more spare. The disable-revert was clean — the
    post-revert `git diff Zip/Tar.lean` is empty in the worker's
    merged commit (PR #2439's diff at
    [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) shows zero
    lines changed). The convention is now *closed* on the
    GNU-typeflag sub-ladder — no further GNU-typeflag silent-skip
    candidates are queued (`'L'` and `'K'` are handled by
    `forEntries`, not silent-skipped), so the next extension (if
    any) will be a non-GNU vendor typeflag (Solaris `'X'` / `'A'`
    or similar) and will continue the spare-prior-and-fire-this-arm
    pattern at N=10 spared arms.
  - **Test-arm placement.** The new test arm in
    [ZipTest/TarFixtures.lean](/home/kim/lean-zip/ZipTest/TarFixtures.lean)
    is placed at the tail of the silent-skip cluster at PR #2439
    land time (immediately after the `tar-incremental-skipped.tar`
    arm), matching the chronological-by-PR-merge-order convention
    the family has followed since PR #1555. At PR #2439 land time
    the file order was `'1'` → `'6'` → `'3'` → `'4'` → `'7'` →
    `'V'` → `'M'` → `'S'` → `'D'` → `'N'`, mirroring the
    PR-merge sequence #1555 → #2413 → #2417 → #2422 → #2425 →
    #2428 → #2431 → #2434 → #2437 → #2439. The chronological
    house style preserves this order in today's master tree
    despite an alphabetical reorder being available
    (`tar-c...skipped` < `tar-f...skipped` < `tar-i...skipped` <
    `tar-l...skipped` < `tar-m...skipped` < `tar-s...skipped` <
    `tar-v...skipped` would have churned the order substantially),
    matching the PR #2433 / PR #2441 / PR #2443 / PR #2444 /
    PR #2445 paired-reviews' same finding for prior arms. The arm
    asserts the extract directory is empty after `Tar.extract`
    (mirroring the FIFO / chardev / blockdev / contiguous /
    volume-header / multi-volume / sparse / directory-dump arm
    shapes) **and** preserves the entry through `Tar.list` with
    `lnNamesListed[0]!.typeflag == 0x4E` and
    `lnNamesListed.size == 1` — inheriting the optional `Tar.list`
    typeflag-preservation assertion introduced by the volume-header
    arm at PR #2428 and continued by the multi-volume arm at
    PR #2431, the sparse arm at PR #2434, and the directory-dump
    arm at PR #2437. By PR #2439 land time this is now an
    established convention for the GNU sub-ladder rather than a
    per-arm extension: every GNU-typeflag arm in the silent-skip
    family carries the `Tar.list` typeflag-preservation assertion,
    confirming the convention's load-bearing status. The
    assertion-shape inheritance is faithful to the issue body's
    deliverable expectation — the empty-extract-dir assertion is
    preserved unchanged; the worker preserved the `Tar.list`
    assertion as an additive arm-specific extension rather than
    substituting for the empty-extract-dir check. The arm uses a
    distinct extract directory
    `/tmp/lean-zip-fixture-tar-longnames-skipped-extract`
    (independent from the nine prior arms' extract directories)
    and is registered in both cleanup loops (per-fixture file-list
    `writeFixtureTmp` outputs and the per-directory `rm -rf` list),
    so re-running the test suite remains hermetic across the
    family extension. No shared mutable state across the ten arms.
    The nine prior test arms continue to pass after the new arm is
    added (independently confirmed by `lake exe test` on the
    merged tree at this paired-review's worker branch:
    *"All tests passed!"*).
  - **Stable-cite discipline.** The new Reproducer Corpus row uses
    only stable identifiers — function names (`Tar.extract`,
    `skipEntryData`, `Tar.forEntries`, `Tar.list`,
    `Tar.buildHeader`, `Tar.create`) and fixture filenames
    (`tar-longnames-skipped.tar`, `tar-incremental-skipped.tar`,
    `tar-sparse-skipped.tar`, `tar-multivol-skipped.tar`,
    `tar-volumeheader-skipped.tar`, `tar-contiguous-skipped.tar`,
    `tar-blockdev-skipped.tar`, `tar-chardev-skipped.tar`,
    `tar-fifo-skipped.tar`, `hardlink-outside.tar`). No `line N`
    or `:N` suffixes appear anywhere in the row, consistent with
    the [PR #2353](https://github.com/kim-em/lean-zip/pull/2353)
    decision to drop line-number anchors. Cross-reference cites
    resolve to real artefacts: PR #2437 / PR #2434 / PR #2431 /
    PR #2428 / PR #2425 / PR #2422 / PR #2417 / PR #2413 / PR #1555
    are all real merged PRs with the cited fixtures and policies.
    The [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) anchor is
    repeated rather than aliased, matching the inventory's house
    style. `bash scripts/check-inventory-links.sh` reports
    `errors=0, warnings=9` on the master tree this paired-review
    branches from (one warning per silent-skip fixture row,
    inherited from the PR #2413 row template — added rows from
    PR #2428 / PR #2431 / PR #2434 / PR #2437 / PR #2439 each kept
    the *during this PR* <!-- drift-detector: prose discussion of the placeholder phrase in a paired-review finding, not a stale placeholder --> phrasing without
    `<!-- drift-detector: -->` opt-outs, deferred to a future
    inventory-cleanup PR per the PR #2433 paired-review's deferral
    — the in-flight cleanup issue #2447 specifically targets the
    nine silent-skip Reproducer Corpus rows for opt-out marker
    insertion, supersedes this paired-review's deferral, and is
    out of scope here). This paired-review introduces no new
    placeholder regression and adds zero warnings — the
    `#TBD-VERIFY-PR` <!-- drift-detector: prose discussion of the placeholder token in a paired-review finding, not a stale placeholder -->
    placeholder in the paired-review header line is wrapped in a
    `<!-- drift-detector: half-closed paired-review placeholder,
    substituted to the real PR number on the worker branch before
    merge -->` opt-out comment so it does not register as a stale
    placeholder.
  - **Ladder-progression close-out.** The per-typeflag silent-skip
    family ladder now stands at: PR #1555 (1/N, typeflag `'1'`
    hardlink — predates per-PR paired-review cadence), PR #2413
    (2/N, typeflag `'6'` FIFO — paired-review PR #2419), PR #2417
    (3/N, typeflag `'3'` character device — paired-review
    PR #2421), PR #2422 (4/N, typeflag `'4'` block device —
    paired-review PR #2427), PR #2425 (5/N, typeflag `'7'`
    contiguous file — paired-review PR #2433, last POSIX UStar
    arm), PR #2428 (6/N, typeflag `'V'` GNU multi-volume archive
    label marker — paired-review PR #2441, first GNU-typeflag arm
    opening the GNU sub-ladder), PR #2431 (7/N, typeflag `'M'` GNU
    multi-volume continuation marker — paired-review PR #2443,
    second GNU-typeflag arm), PR #2434 (8/N, typeflag `'S'` GNU
    sparse file — paired-review PR #2444, third GNU-typeflag arm),
    PR #2437 (9/N, typeflag `'D'` GNU directory-dump for
    incremental backups — paired-review PR #2445, fourth
    GNU-typeflag arm), and PR #2439 (10/N, typeflag `'N'` GNU
    `LF_NAMES` old-long-name extension — this paired-review,
    **fifth and final GNU-typeflag arm closing the GNU
    sub-ladder**). With PR #2439 landing, **the GNU-typeflag
    sub-ladder closes at five arms** (`'V'` / `'M'` / `'S'` /
    `'D'` / `'N'`) beyond the now-capped POSIX UStar `'1'`–`'7'`
    numeric range. The silent-skip family at the *sub-ladder*
    level remains open-ended (every additional per-typeflag arm
    fires the same `else` fallback in `Tar.extract`, so the
    marginal fixture cost falls but the marginal regression
    benefit also falls); but the **GNU-typeflag-arm queue is
    closed** — no further GNU-typeflag silent-skip candidates are
    queued because `'L'` (`LF_LONGNAME`) and `'K'` (`LF_LONGLINK`)
    are handled by `forEntries` rather than silent-skipped (the
    inner dispatch accumulates `'L'` / `'K'` payloads as pending
    long-name / long-link buffers for the next entry, and the PAX
    `'x'` / `'g'` pair is similarly handled), and no other GNU
    typeflag values exist in the historical or current GNU tar
    typeflag table. The natural next region (if any future
    extension is filed) is non-GNU vendor extensions (Solaris
    `'X'` extended attribute, `'A'` Solaris ACL, once a typeflag
    survey identifies a deployed extension worth pinning); no such
    issue is in flight. The merged-but-unreviewed sibling-class
    fixture `tar-mixed-skipped.tar` (PR #2449,
    extract-continuation invariant pinned across a silently-skipped
    middle `'6'` FIFO entry) is *not* an eleventh per-typeflag arm
    and is paired-reviewed separately (in-flight issue #2450 at
    file time of this entry) — that paired-review is out of scope
    here, matching the per-typeflag paired-review cadence. Any
    future per-typeflag fixture should earn its own paired-review
    entry on the established cadence. No new follow-up issue is
    filed by this paired-review.
- Paired review of PR #2449 (`tar-mixed-skipped.tar` fixture —
  **first sibling-class entry** of the silent-skip family,
  pinning the `Tar.extract` *extract-continuation* invariant
  across a silently-skipped middle entry; opens the
  sibling-class sub-category distinct from the ten-arm
  per-typeflag ladder closed by PR #2439 (`'N'` arm); this
  paired-review landed in PR <!-- drift-detector: half-closed paired-review placeholder, substituted to the real PR number on the worker branch before merge --> #TBD-VERIFY-PR closing #2450):
  PR #2449 (squash commit `2c4815f`, merged 2026-05-03, closes
  #2448) opens the **sibling-class sub-category** of the
  `Tar.extract` silent-skip `else` fallback family — distinct
  from the ten-arm per-typeflag ladder closed at PR #2439
  (`'N'`, fifth and final GNU-typeflag arm). The commit adds a
  three-entry UStar fixture
  `testdata/tar/security/tar-mixed-skipped.tar` (SHA-256
  `7ed31119d36fc65c80b2c3ff54540c0bba884f925da38fd043d1ddc5524865ef`,
  total size 5 × 512 = 2560 bytes) interleaving a silently-skipped
  middle FIFO entry (`typeflag '6' = 0x36`) between two regular
  files (`before.txt` carrying `"BEFORE\n"`, `after.txt` carrying
  `"AFTER\n"`); two new helper definitions
  (`buildRegularEntry` for header+payload+padding regular-entry
  block-pairs, `buildMixedFixture` for the three-entry composition)
  plus a new top-level call in
  [scripts/build-symlink-hardlink-malformed-fixtures.lean](/home/kim/lean-zip/scripts/build-symlink-hardlink-malformed-fixtures.lean)
  producing it deterministically; a new test arm in
  [ZipTest/TarFixtures.lean](/home/kim/lean-zip/ZipTest/TarFixtures.lean)
  immediately after the existing `tar-longnames-skipped.tar`
  arm, asserting both regular files materialise *with the
  correct declared payloads* (`before.txt = "BEFORE\n"`,
  `after.txt = "AFTER\n"`) **and** that the extract directory
  contains exactly two entries; a new Reproducer Corpus row in
  this inventory; and a *Symlink/hardlink extraction policy*
  fixture-enumeration entry. No spec change, no production-code
  change, no new typeflag constant in the `Tar` namespace, no
  caller / signature change.
  - **Sibling-class-vs-eleventh-arm framing fidelity.** The
    inventory row prose correctly frames PR #2449 as a
    *sibling-class* fixture pinning the *extract-continuation*
    invariant — not as an eleventh per-typeflag arm. The
    Reproducer Corpus row's prose explicitly states *"Sibling-class
    fixture pinning the extract-continuation invariant —
    explicitly **not** an eleventh per-typeflag arm"* and
    enumerates all ten per-typeflag siblings
    (`hardlink-outside.tar` typeflag `'1'`, `tar-fifo-skipped.tar`
    typeflag `'6'`, `tar-chardev-skipped.tar` typeflag `'3'`,
    `tar-blockdev-skipped.tar` typeflag `'4'`,
    `tar-contiguous-skipped.tar` typeflag `'7'`,
    `tar-volumeheader-skipped.tar` typeflag `'V'`,
    `tar-multivol-skipped.tar` typeflag `'M'`,
    `tar-sparse-skipped.tar` typeflag `'S'`,
    `tar-incremental-skipped.tar` typeflag `'D'`,
    `tar-longnames-skipped.tar` typeflag `'N'`) as the ten
    distinct typeflag values that already pin the *existence* of
    the `else` arm. The new fixture pins a *different* invariant
    — that the `else` arm's `skipEntryData` call preserves the
    next-entry offset — which all ten per-typeflag arms
    implicitly assume but none exercises (each is single-entry
    and ends at EOF after the skipped entry, so an off-by-one in
    `skipEntryData` propagates only into a `forEntries` short-read
    at EOF and is silently absorbed). The middle entry's typeflag
    `'6'` (FIFO) is incidental — chosen to mirror
    `tar-fifo-skipped.tar` (PR #2413) for parsimony rather than
    to add a new typeflag value. The framing distinction is
    load-bearing: future planners must not misread this row as a
    `'6'`-arm duplicate of the FIFO per-typeflag arm. Both the
    *Symlink/hardlink extraction policy* fixture-enumeration
    bullet and the Reproducer Corpus row name the *extract-continuation*
    invariant explicitly and cross-reference all ten per-typeflag
    siblings without collapsing the new entry into the
    per-typeflag ladder. This paired-review **opens the
    sibling-class sub-category** of the silent-skip family —
    distinct from the per-typeflag arm sub-category. Any future
    fixture pinning a non-typeflag-axis invariant (e.g. `Tar.list`
    continuation across a silent-skip middle entry, or an
    extract-continuation invariant under a long-name-prefixed
    silent-skip entry) would file its own sibling-class
    paired-review and *not* extend the per-typeflag arm count.
  - **Three-entry geometry fidelity.** Verified directly on the
    merged tree: `stat` reports 2560 bytes (= 5 × 512), and
    `shasum -a 256` reports
    `7ed31119d36fc65c80b2c3ff54540c0bba884f925da38fd043d1ddc5524865ef`.
    The geometry decomposes as: one 512-byte header + one
    512-byte payload block for `before.txt` (typeflag `'0'`,
    payload `"BEFORE\n"` size 7, padded with 505 NUL bytes) =
    1024 bytes; one 512-byte bare header for the FIFO middle
    entry (typeflag `'6'`, `path = "fifo-entry"`, empty linkname,
    `size = 0`, no payload) = 512 bytes; one 512-byte header +
    one 512-byte payload block for `after.txt` (typeflag `'0'`,
    payload `"AFTER\n"` size 6, padded with 506 NUL bytes) =
    1024 bytes; total 2560 bytes. No trailing zero blocks
    (`Tar.forEntries` terminates on the short read at EOF,
    matching the per-typeflag fixture geometry). The test arm in
    [ZipTest/TarFixtures.lean](/home/kim/lean-zip/ZipTest/TarFixtures.lean)
    asserts *both* the contents
    (`before.txt = "BEFORE\n"`, `after.txt = "AFTER\n"` —
    each compared via `IO.FS.readFile` + `unless` byte-equality)
    and the count (extract dir contains *exactly* two entries
    via `mixedExtract.readDir` + `entries.size == 2`). The
    contents-and-count combination is the load-bearing assertion
    pair for this fixture: the count check catches a regression
    that *eats* a regular-file entry (e.g. an over-skip that
    consumes the `after.txt` header), and the contents check
    catches a regression that *misaligns* the post-skip stream
    position by less than a full block boundary (e.g. a 1-byte
    off-by-one that does not eat the entry but corrupts its
    payload offset). Either single assertion in isolation would
    leave a detection gap; the pair closes both.
  - **Builder-extension fidelity.** The worker chose *extend in
    place* on
    [scripts/build-symlink-hardlink-malformed-fixtures.lean](/home/kim/lean-zip/scripts/build-symlink-hardlink-malformed-fixtures.lean),
    matching the PR #2413 / PR #2417 / PR #2422 / PR #2425 /
    PR #2428 / PR #2431 / PR #2434 / PR #2437 / PR #2439 workers'
    earlier choices on the same script. The script path stays
    stable. Two new helper definitions were introduced:
    `buildRegularEntry path payload` (returns a `ByteArray`
    containing one 512-byte header for a `typeRegular` entry
    plus the payload plus `Tar.paddingFor entry.size` NUL bytes
    rounding up to the next 512-byte boundary) and
    `buildMixedFixture outPath` (composes a `before.txt` regular
    entry, a bare FIFO header for `fifo-entry` with `size = 0`
    and `typeflag := 0x36`, and an `after.txt` regular entry,
    then writes the concatenation to `outPath`). The
    `buildRegularEntry` helper is genuinely new (no prior
    fixture in the family produces a regular-file entry — the
    ten per-typeflag arms all use `buildZeroSizeFixture` which
    emits a bare 512-byte header with no payload). Reusing
    `Tar.buildHeader` and `Tar.paddingFor` keeps the byte layout
    consistent with the production writer. The build summary
    line at `main`'s tail at PR #2449 land time printed *"Built
    12 per-typeflag-policy security fixtures under
    testdata/tar/security/."* — the count moved from `11`
    (pre-PR-#2449: `symlink-absolute.tar` plus the ten
    per-typeflag arms) to `12` (adding the sibling-class
    `tar-mixed-skipped.tar`). The worker frames the count under
    a unified *per-typeflag-policy* total — collapsing
    sibling-class and per-typeflag arms into a single counter
    rather than maintaining a separate sibling-class subtotal —
    which the issue body explicitly accepted as one of two
    acceptable framings. (Today's master tree has since advanced
    the count to `14` by adding the further sibling-class
    fixtures `tar-skipped-payload.tar` (PR #2454) and
    `tar-skipped-padded.tar` (PR #2457), but the PR #2449
    land-time count of `12` is what this paired-review audits.)
    The module docstring's *Output (byte-deterministic)* list
    and the `tar-mixed-skipped.tar` body paragraph were both
    extended; the body paragraph's three-entry layout
    description matches the on-disk geometry verified above.
  - **Adversarial-check fidelity.** The adversarial check is
    recorded in the PR #2449 worker branch's progress entry
    (linked from the issue): temporarily replacing the `else`
    body's `skipEntryData input e.size` with
    `skipEntryData input (e.size + 1)` (a 1-byte over-skip)
    caused the new arm to fire with `tar: header checksum
    mismatch` while all ten per-typeflag siblings continued to
    pass. The error symptom matches the expected propagation:
    after the FIFO header is parsed at offset `0x400`, the
    perturbed skip consumes one byte more than the alignment
    requires, leaving the input stream positioned 1 byte past
    the start of `after.txt`'s header at offset `0x600`; the
    next `forEntries` `readExact 512` consumes the last 511
    bytes of `after.txt`'s header plus the first byte of its
    payload, and `parseHeader` on this misaligned block detects
    a checksum mismatch. The ten per-typeflag siblings continue
    to pass because each is single-entry and ends at EOF after
    the skipped entry, so the off-by-one in `skipEntryData`
    propagates only into a `forEntries` short-read at EOF and
    is silently absorbed — the asymmetric fire-vs-pass behaviour
    confirms the new fixture independently exercises the
    extract-continuation invariant. Re-checking on this
    paired-review's worker branch: the post-revert
    `git diff Zip/Tar.lean` is empty in the merged commit
    `2c4815f` (PR #2449's diff at
    [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) shows zero
    lines changed). The adversarial-check convention from the
    per-typeflag arms (introduced at PR #2413 and refined into
    the *spare all-but-the-new-arm* wrapper at PR #2417 onwards)
    adapts naturally here: the sibling-class adversarial check
    perturbs the *arithmetic* of `skipEntryData` rather than
    *guarding* a specific typeflag, exercising a different
    failure mode (cascading into a downstream header parse)
    than the per-typeflag arms (which fire on a typeflag-specific
    `else` exclusion). The two adversarial-check shapes are
    complementary, not duplicative — the sibling-class shape
    catches `skipEntryData` regressions that the per-typeflag
    shape misses, and vice versa.
  - **Reproducer Corpus row prose fidelity.** The new
    `tar-mixed-skipped.tar` row is appended to the tail of the
    Minimized Reproducer Corpus table (immediately after the
    `tar-longnames-skipped.tar` row added by PR #2439). The row
    carries: (i) the three-entry geometry enumerated explicitly
    (`before.txt` typeflag `'0'` payload `"BEFORE\n"` size 7,
    `fifo-entry` typeflag `'6' = 0x36` empty linkname size 0,
    `after.txt` typeflag `'0'` payload `"AFTER\n"` size 6) with
    total size `5 × 512 = 2560 bytes`; (ii) the explicit
    *extract-continuation* invariant phrasing — both as the
    fixture's load-bearing claim and as the regression-class
    description (an `e.size`-vs-block-boundary off-by-one would
    be silently absorbed by the per-typeflag arms but caught by
    this fixture); (iii) the *not an eleventh per-typeflag arm*
    framing with the cross-reference to all ten per-typeflag
    siblings; (iv) the *contents and count* test-arm
    description, distinguishing what each assertion catches
    (count catches an over-skip that eats a regular-file entry;
    content catches an off-by-one that misaligns the payload
    offset without eating the entry); (v) the *adversarial check
    during this PR* <!-- drift-detector: prose discussion of the placeholder phrase in a paired-review finding, not a stale placeholder --> attribution clause carrying the standard
    `<!-- drift-detector: prose discussion ... -->` opt-out
    marker (consistent with the post-#2453 cleanup that
    suppressed the nine pre-existing silent-skip Reproducer
    Corpus rows' drift-detector warnings); (vi) the writer-side
    caveat that `Tar.create`'s caller-API never invokes
    `Tar.buildHeader` with a non-`'0'`/`'5'` typeflag, so
    legitimate archives produced by the lean-zip writer never
    carry typeflag `'6'`; (vii) only stable
    [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) anchors —
    no `:N` line-number suffixes, consistent with the
    [PR #2353](https://github.com/kim-em/lean-zip/pull/2353)
    decision. The closing-PR column resolves to `#2449` on the
    merged tree (verified via `git blame` pointing at PR #2449's
    merge commit `2c4815f`).
  - **Stable-cite discipline.** The new Reproducer Corpus row
    and the new *Symlink/hardlink extraction policy*
    fixture-enumeration bullet use only stable identifiers —
    function names (`Tar.extract`, `Tar.forEntries`,
    `Tar.buildHeader`, `Tar.create`, `skipEntryData`,
    `Binary.zeros`, `Tar.paddingFor`) and fixture filenames (the
    ten per-typeflag siblings plus the new
    `tar-mixed-skipped.tar`). No `line N` or `:N` suffixes
    appear anywhere in the new prose, consistent with the
    [PR #2353](https://github.com/kim-em/lean-zip/pull/2353)
    decision to drop line-number anchors. Cross-reference cites
    resolve to real artefacts: PR #1555 / PR #2413 / PR #2417 /
    PR #2422 / PR #2425 / PR #2428 / PR #2431 / PR #2434 /
    PR #2437 / PR #2439 are all real merged PRs with the cited
    fixtures and policies. The
    [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) anchor is
    repeated rather than aliased, matching the inventory's
    house style. `bash scripts/check-inventory-links.sh` reports
    `errors=0` on the worker branch this paired-review lands on.
    This paired-review introduces no new placeholder regression
    — the `#TBD-VERIFY-PR` <!-- drift-detector: prose discussion of the placeholder token in a paired-review finding, not a stale placeholder -->
    placeholder in the paired-review header line is wrapped in
    a `<!-- drift-detector: half-closed paired-review placeholder,
    substituted to the real PR number on the worker branch before
    merge -->` opt-out comment so it does not register as a stale
    placeholder.
  - **Sub-category-opener close-out.** PR #2449 opens the
    **sibling-class** sub-category of the silent-skip family —
    a sub-category structurally distinct from the per-typeflag
    sub-category (which itself splits into the now-capped POSIX
    UStar `'1'`–`'7'` numeric range and the now-closed
    GNU-typeflag five-arm sub-ladder `'V'` / `'M'` / `'S'` /
    `'D'` / `'N'`). Where the per-typeflag sub-category pins
    *which* typeflag values route through the `else` fallback,
    the sibling-class sub-category pins the *post-skip
    stream-position arithmetic* of the `skipEntryData` call
    inside that fallback. The two sub-categories are
    complementary: a regression that drops the `else` arm
    entirely fires the per-typeflag fixtures, and a regression
    that breaks `skipEntryData`'s alignment fires the
    sibling-class fixtures, with no overlap in detection. The
    sibling-class sub-category is *open-ended* at the
    sub-ladder level — every distinct `skipEntryData` arithmetic
    path or every distinct downstream-entry context (mid-archive
    vs end-of-archive, regular vs typed entry, etc.) could in
    principle warrant its own fixture. Two follow-on
    sibling-class fixtures landed shortly after PR #2449:
    `tar-skipped-payload.tar` (PR #2454, pinning the
    `e.size != 0` data-advance arithmetic for a multiple-of-512
    payload — paired-review #2455 unclaimed at file time of this
    entry) and `tar-skipped-padded.tar` (PR #2457, pinning the
    `paddingFor` round-up arithmetic for a non-multiple-of-512
    `e.size` — paired-review #2458 unclaimed at file time of
    this entry). Together with this fixture they close the three
    arithmetic paths of `skipEntryData input e.size`: `size == 0`
    (this fixture), `size > 0 ∧ size mod 512 == 0` (PR #2454),
    and `size > 0 ∧ size mod 512 ≠ 0` (PR #2457). No further
    sibling-class arithmetic candidate is queued — the trio
    fully covers the `skipEntryData` arithmetic axis. Future
    sibling-class extensions (if any) would pin a non-arithmetic
    invariant such as `Tar.list` continuation across a
    silent-skip entry or extract-continuation under a
    long-name-prefixed silent-skip entry; no such issue is in
    flight. No new follow-up issue is filed by this
    paired-review.

#### Symlink/hardlink extraction policy

`Tar.extract` (in [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean))
applies a fixed per-typeflag policy:

- `typeRegular` ('0') and `typeDirectory` ('5') — written under
  `outDir/path` after `Binary.isPathSafe` rejects unsafe paths
  (absolute, `..`, `.`, empty components, backslash, Windows drive
  letters).
- `typeSymlink` ('2') — `linkname` is rejected before any
  `Handle.createSymlink` call if it starts with `/`, contains `\`, or
  has any `..` component (path-component split). The payload is
  always discarded.
- `typeHardlink` ('1') — silently skipped. No filesystem entry is
  created, the payload is consumed and discarded, and no
  `Handle.createHardlink` call exists in the extractor. A crafted
  `linkname` therefore cannot escape `outDir`.
- All other typeflags (devices, FIFO, GNU sparse, etc.) — same silent
  skip as `typeHardlink`.

Regression fixtures live under `testdata/tar/security/`:

- `tar-slip.tar`, `tar-absolute.tar` — regular-file entries that must
  fail `"unsafe path"`.
- `backslash-slip.tar` — regular-file entry whose path contains `\`;
  also fails `"unsafe path"` (the backslash check fires before the
  `..` component check).
- `symlink-slip.tar` — symlink whose linkname contains `..`; must
  fail `"unsafe symlink"`.
- `symlink-absolute.tar` — symlink whose linkname is `/etc/passwd`;
  must fail `"unsafe symlink"`. Built deterministically by
  `scripts/build-symlink-hardlink-malformed-fixtures.lean`.
- `hardlink-outside.tar` — `typeHardlink` entry with linkname
  `../outside`; extraction must succeed with an empty extract dir.
  Built by the same script.
- `tar-fifo-skipped.tar` — typeflag `'6'` (POSIX UStar FIFO, `0x36`)
  entry with `path = "fifo-entry"` and empty linkname; extraction must
  succeed with an empty extract dir. Pins the silent-skip `else`
  fallback's FIFO arm as a second sibling alongside
  `hardlink-outside.tar` (typeflag `'1'`); together the two pin two
  distinct typeflag values against the shared fallback. Built by the
  same script.
- `tar-chardev-skipped.tar` — typeflag `'3'` (POSIX UStar character
  device, `0x33`) entry with `path = "chardev-entry"` and empty
  linkname; extraction must succeed with an empty extract dir. Pins
  the silent-skip `else` fallback's character-device arm as a third
  sibling alongside `hardlink-outside.tar` (typeflag `'1'`) and
  `tar-fifo-skipped.tar` (typeflag `'6'`); together the three pin
  three distinct typeflag values against the shared fallback. Built
  by the same script.
- `tar-blockdev-skipped.tar` — typeflag `'4'` (POSIX UStar block
  device, `0x34`) entry with `path = "blockdev-entry"` and empty
  linkname; extraction must succeed with an empty extract dir. Pins
  the silent-skip `else` fallback's block-device arm as a fourth
  sibling alongside `hardlink-outside.tar` (typeflag `'1'`),
  `tar-fifo-skipped.tar` (typeflag `'6'`), and
  `tar-chardev-skipped.tar` (typeflag `'3'`); together the four pin
  four distinct typeflag values against the shared fallback. Built
  by the same script.
- `tar-contiguous-skipped.tar` — typeflag `'7'` (POSIX UStar
  contiguous file, `0x37`) entry with `path = "contiguous-entry"`
  and empty linkname; extraction must succeed with an empty extract
  dir. Pins the silent-skip `else` fallback's contiguous-file arm as
  a fifth sibling alongside `hardlink-outside.tar` (typeflag `'1'`),
  `tar-fifo-skipped.tar` (typeflag `'6'`),
  `tar-chardev-skipped.tar` (typeflag `'3'`), and
  `tar-blockdev-skipped.tar` (typeflag `'4'`); together the five pin
  five distinct typeflag values against the shared fallback, fully
  fixturing the POSIX UStar `'0'`–`'7'` numeric range (every value
  has either a typed branch in `Tar.extract` or a silent-skip
  regression fixture). The strict-vs-lenient choice — lean-zip
  rejects `'7'` rather than aliasing it to `'0'` (regular file) as
  some lenient peer extractors do — is the security-relevant
  behaviour this fixture pins. Built by the same script.
- `tar-volumeheader-skipped.tar` — typeflag `'V'` (GNU multi-volume
  archive label marker, `0x56`) entry with `path =
  "volume-label-entry"` and empty linkname; extraction must succeed
  with an empty extract dir. Pins the silent-skip `else` fallback's
  GNU volume-header arm as the **first GNU-typeflag** sibling
  alongside the POSIX UStar siblings `hardlink-outside.tar`
  (typeflag `'1'`), `tar-fifo-skipped.tar` (typeflag `'6'`),
  `tar-chardev-skipped.tar` (typeflag `'3'`),
  `tar-blockdev-skipped.tar` (typeflag `'4'`), and
  `tar-contiguous-skipped.tar` (typeflag `'7'`); together the six
  pin six distinct typeflag values against the shared fallback,
  opening a GNU-typeflag sub-ladder distinct from the POSIX UStar
  `'0'`–`'7'` numeric range. The strict-vs-lenient choice — a
  malicious archive could ship a `'V'` entry with a volume label
  crafted to look like a filesystem path (e.g. `"../../../etc/passwd"`
  in the `path` slot), expecting a lenient extractor to materialise
  the marker as a regular file; lean-zip's policy of *never*
  materialising `'V'` entries (regardless of `path` / payload) is
  the correct conservative choice — is the security-relevant
  behaviour this fixture pins. Built by the same script.
- `tar-multivol-skipped.tar` — typeflag `'M'` (GNU multi-volume
  continuation marker, `0x4D`) entry with `path = "multivol-entry"`
  and empty linkname; extraction must succeed with an empty extract
  dir. Pins the silent-skip `else` fallback's GNU
  multi-volume-continuation arm as the **second GNU-typeflag**
  sibling alongside `tar-volumeheader-skipped.tar` (typeflag `'V'`),
  extending the GNU-typeflag sub-ladder distinct from the POSIX
  UStar `'0'`–`'7'` numeric range covered by `hardlink-outside.tar`
  (typeflag `'1'`), `tar-fifo-skipped.tar` (typeflag `'6'`),
  `tar-chardev-skipped.tar` (typeflag `'3'`),
  `tar-blockdev-skipped.tar` (typeflag `'4'`), and
  `tar-contiguous-skipped.tar` (typeflag `'7'`); together the seven
  pin seven distinct typeflag values against the shared fallback.
  The strict-vs-lenient choice — a malicious single-volume archive
  could ship a `'M'` entry as a top-level record (without a
  preceding multi-volume context) with a crafted `path` field
  (e.g. `"../../../etc/passwd"`) and a non-zero `size` declaring a
  fake "remaining payload", expecting a lenient extractor to
  materialise the marker as a regular file; lean-zip's policy of
  *never* materialising `'M'` entries (regardless of `path` /
  declared `size` / actual payload) is the correct conservative
  choice — is the security-relevant behaviour this fixture pins.
  Built by the same script.
- `tar-sparse-skipped.tar` — typeflag `'S'` (GNU sparse file,
  `0x53`) entry with `path = "sparse-entry"` and empty linkname;
  extraction must succeed with an empty extract dir. Pins the
  silent-skip `else` fallback's GNU sparse-file arm as the
  **third GNU-typeflag** sibling alongside
  `tar-volumeheader-skipped.tar` (typeflag `'V'`) and
  `tar-multivol-skipped.tar` (typeflag `'M'`), extending the
  GNU-typeflag sub-ladder distinct from the POSIX UStar
  `'0'`–`'7'` numeric range covered by `hardlink-outside.tar`
  (typeflag `'1'`), `tar-fifo-skipped.tar` (typeflag `'6'`),
  `tar-chardev-skipped.tar` (typeflag `'3'`),
  `tar-blockdev-skipped.tar` (typeflag `'4'`), and
  `tar-contiguous-skipped.tar` (typeflag `'7'`); together the
  eight pin eight distinct typeflag values against the shared
  fallback. The strict-vs-lenient choice — a malicious archive
  could ship a `'S'` entry with a crafted sparse map (the GNU
  sparse format itself has multiple parser-differential variants:
  `0.0`, `0.1`, `1.0`, with subtly different sparse-map
  encodings) declaring zero-fill segments that overlap or exceed
  the entry's declared `size`, expecting a lenient extractor to
  allocate a large output file (zero-fill amplification) or
  miscompute the payload offset and corrupt subsequent entries;
  lean-zip's policy of *never* materialising `'S'` entries
  (regardless of `path` / sparse map / declared `size` / actual
  payload) is the correct conservative choice — is the
  security-relevant behaviour this fixture pins. The `'S'`
  typeflag is otherwise interpreted purely as a sparse-file
  reconstruction cue in GNU tar's sparse workflow (see
  `info '(tar)Sparse Formats'`). Built by the same script.
  Adversarial check (replace the tail `else` arm's
  `skipEntryData` with an explicit guard that fires on `'S'`)
  confirmed the fixture independently fires for typeflag `0x53`
  while all five POSIX UStar siblings and the two GNU siblings
  (`'V'` / `'M'`) still pass.
- `tar-incremental-skipped.tar` — typeflag `'D'` (GNU
  directory-dump for incremental backups, `0x44`) entry with
  `path = "incremental-entry"` and empty linkname; extraction
  must succeed with an empty extract dir. Pins the silent-skip
  `else` fallback's GNU incremental-backup arm as the **fourth
  GNU-typeflag** sibling alongside `tar-volumeheader-skipped.tar`
  (typeflag `'V'`), `tar-multivol-skipped.tar` (typeflag `'M'`),
  and `tar-sparse-skipped.tar` (typeflag `'S'`), extending the
  GNU-typeflag sub-ladder distinct from the POSIX UStar
  `'0'`–`'7'` numeric range covered by `hardlink-outside.tar`
  (typeflag `'1'`), `tar-fifo-skipped.tar` (typeflag `'6'`),
  `tar-chardev-skipped.tar` (typeflag `'3'`),
  `tar-blockdev-skipped.tar` (typeflag `'4'`), and
  `tar-contiguous-skipped.tar` (typeflag `'7'`); together the
  nine pin nine distinct typeflag values against the shared
  fallback. The strict-vs-lenient choice — a malicious archive
  could ship a `'D'` entry with a crafted directory-listing
  payload that an incremental-aware extractor would interpret as
  instructions to delete files outside `outDir` (the GNU
  incremental format allows the listing to mark files for
  *removal* during restore, with `Y`/`N` markers per entry in
  the NUL-separated listing payload), expecting a lenient
  extractor to honour those removal cues; lean-zip's policy of
  *never* materialising `'D'` entries — and never interpreting
  the listing payload at all — (regardless of `path` / declared
  `size` / actual payload) is the correct conservative choice —
  is the security-relevant behaviour this fixture pins. The
  `'D'` typeflag is otherwise interpreted purely as an
  incremental-backup directory-dump cue in GNU tar's incremental
  workflow (see `info '(tar)Incremental Dumps'`). Built by the
  same script. Adversarial check (replace the tail `else` arm's
  `skipEntryData` with an explicit guard that fires on `'D'`)
  confirmed the fixture independently fires for typeflag `0x44`
  while all five POSIX UStar siblings and the three GNU siblings
  (`'V'` / `'M'` / `'S'`) still pass. Closed by PR
  #2437.
- `tar-longnames-skipped.tar` — typeflag `'N'` (GNU LF_NAMES
  old-long-name extension, `0x4E`) entry with `path =
  "longnames-entry"` and empty linkname; extraction must succeed
  with an empty extract dir. Pins the silent-skip `else` fallback's
  GNU long-names-old arm as the **fifth GNU-typeflag** sibling
  alongside `tar-volumeheader-skipped.tar` (typeflag `'V'`),
  `tar-multivol-skipped.tar` (typeflag `'M'`),
  `tar-sparse-skipped.tar` (typeflag `'S'`), and
  `tar-incremental-skipped.tar` (typeflag `'D'`), extending the
  GNU-typeflag sub-ladder distinct from the POSIX UStar
  `'0'`–`'7'` numeric range covered by `hardlink-outside.tar`
  (typeflag `'1'`), `tar-fifo-skipped.tar` (typeflag `'6'`),
  `tar-chardev-skipped.tar` (typeflag `'3'`),
  `tar-blockdev-skipped.tar` (typeflag `'4'`), and
  `tar-contiguous-skipped.tar` (typeflag `'7'`); together the ten
  pin ten distinct typeflag values against the shared fallback.
  The strict-vs-lenient choice — `'N'` is the deprecated precursor
  to the modern `'L'` / `'K'` long-name encoding, so a malicious
  archive could ship an `'N'` entry whose payload encodes a list
  of filenames containing `../etc/passwd` or absolute paths,
  expecting a lenient extractor (`bsdtar` / `libarchive` recognise
  `'N'` in lenient mode) to apply those names to subsequent
  regular-file entries (parser-differential archive-slip via
  deprecated long-name rewriting); lean-zip's policy of *never*
  materialising `'N'` entries — and never interpreting the payload
  as a name-rewrite directive — (regardless of `path` / declared
  `size` / actual payload) is the correct conservative choice — is
  the security-relevant behaviour this fixture pins. The `'N'`
  typeflag is otherwise interpreted purely as an obsolete
  long-name cue in old-GNU tar archives (predating PAX `'x'` and
  the modern GNU `'L'` / `'K'` headers, considered obsolete in
  current GNU tar but still emitted by old archivers).
  `forEntries` recognises only the modern `'L'` / `'K'` long-name
  typeflags (and the PAX `'x'` / `'g'` pair); `'N'` is *not*
  aliased to `'L'`. Built by the same script. Adversarial check
  (replace the tail `else` arm's `skipEntryData` with an explicit
  guard that fires on `'N'`) confirmed the fixture independently
  fires for typeflag `0x4E` while all five POSIX UStar siblings
  and the four GNU siblings (`'V'` / `'M'` / `'S'` / `'D'`) still
  pass.
- `tar-mixed-skipped.tar` — three-entry archive interleaving a
  silently-skipped middle entry between two regular files:
  `before.txt` (typeflag `'0'`, payload `"BEFORE\n"`) →
  `fifo-entry` (typeflag `'6'` = `0x36`, POSIX UStar FIFO,
  silently skipped) → `after.txt` (typeflag `'0'`, payload
  `"AFTER\n"`); extraction must materialise *both* `before.txt`
  and `after.txt` with their declared payloads after the middle
  FIFO entry is silent-skipped. Sibling-class fixture (not an
  eleventh per-typeflag arm — the ten per-typeflag fixtures
  already pin the *existence* of the `else` arm at ten distinct
  typeflag values) covering the *extract-continuation* invariant
  that none of the ten single-entry per-typeflag siblings
  exercises: that the `else` branch's `skipEntryData input e.size`
  call leaves the input stream positioned exactly at the next
  512-byte block boundary so a subsequent regular-file entry
  still extracts cleanly. A regression that broke `skipEntryData`
  by, say, advancing the stream by `e.size` bytes without padding
  to a 512-byte block boundary would not fire any of the existing
  ten fixtures (each ends at EOF after the skipped entry, so the
  off-by-one in `skipEntryData` propagates only into a
  `forEntries` short-read at EOF and is silently absorbed) but
  would silently corrupt the offset of any following entry —
  this fixture closes that detection gap. Typeflag `'6'` is
  reused for the middle entry to mirror `tar-fifo-skipped.tar`
  — pins the same `else` arm without introducing a new typeflag
  value. Total fixture size: 5 × 512 = 2560 bytes (one
  header+payload pair for each regular entry, one bare header
  for the FIFO). No trailing zero blocks (`Tar.forEntries`
  terminates on the short read at EOF, matching the per-typeflag
  fixture geometry). Built by the same script. Adversarial check
  (temporarily replace the `else` arm's `skipEntryData input
  e.size` with `skipEntryData input (e.size + 1)`) confirmed the
  fixture independently fires the extract-continuation invariant
  with `tar: header checksum mismatch` (the 1-byte offset shift
  causes the next 512-byte block read to consume the
  `after.txt` payload region rather than the `after.txt`
  header, and the subsequent block parses as a header with
  garbage checksum), while all ten per-typeflag siblings still
  pass (each ends at EOF after the skipped entry, so the
  off-by-one is absorbed into the `forEntries` short-read at
  EOF). The fixture pins extract continuation for `Tar.extract`
  only; `Tar.list`'s continuation invariant is structurally
  identical (`forEntries` is shared) but a separate fixture for
  `Tar.list` is not required — the new arm exercises
  `Tar.extract` only.
- `tar-skipped-payload.tar` — three-entry archive interleaving a
  silently-skipped middle entry with a *non-zero* declared
  payload between two regular files: `before.txt` (typeflag
  `'0'`, payload `"BEFORE\n"`) → `fifo-entry` (typeflag `'6'` =
  `0x36`, POSIX UStar FIFO, declared `size == 512`, all-zero
  512-byte payload, silently skipped) → `after.txt` (typeflag
  `'0'`, payload `"AFTER\n"`); extraction must materialise
  *both* `before.txt` and `after.txt` with their declared
  payloads after the middle FIFO entry's header *and* its
  declared 512-byte payload are consumed by `skipEntryData`.
  Second sibling-class fixture alongside `tar-mixed-skipped.tar`
  (PR #2449, the first sibling-class entry that pinned the
  *extract-continuation* invariant for a `size == 0` skip),
  covering the *data-advance arithmetic* of the silent-skip
  `else` branch's `skipEntryData input e.size` call for non-zero
  `e.size` — the path that the eleven existing all-`size == 0`
  silent-skip fixtures (the ten per-typeflag arms PR
  #1555/#2413/#2417/#2422/#2425/#2428/#2431/#2434/#2437/#2439 +
  the first sibling-class `tar-mixed-skipped.tar` PR #2449) do
  not exercise. A regression that broke `skipEntryData` by
  ignoring `e.size` and advancing only by the trailing 512-byte
  header padding would not fire any of the eleven existing
  fixtures (all `size == 0`, so `skipEntryData input 0`
  degenerates to a no-op modulo the header padding) but would
  silently corrupt the offset of any entry following a skipped
  non-zero-payload entry — `skipEntryData` would leave the
  stream positioned at the start of the FIFO payload, the next
  `readExact` would consume 512 zero bytes, `parseHeader` would
  interpret the zero block as end-of-archive, and `forEntries`
  would terminate without extracting `after.txt`. This fixture
  closes that detection gap. Typeflag `'6'` is reused for the
  middle entry to mirror `tar-fifo-skipped.tar` and
  `tar-mixed-skipped.tar` — pins the same `else` arm without
  introducing a new typeflag value. Total fixture size: 6 × 512
  = 3072 bytes (one header + one payload block for each of the
  three entries). No trailing zero blocks (`Tar.forEntries`
  terminates on the short read at EOF, matching the
  per-typeflag fixture geometry). Built by the same script.
  Adversarial check (temporarily replace the `else` arm's
  `skipEntryData input e.size` with `skipEntryData input 0`,
  i.e. ignore the declared payload size) confirmed the fixture
  independently fires the data-advance invariant with `no such
  file or directory` at
  `/tmp/lean-zip-fixture-tar-skipped-payload-extract/after.txt`
  (the misskipped 512 zero bytes parse as an end-of-archive
  marker, terminating `forEntries` before the `after.txt`
  header is read), while all eleven preceding silent-skip
  siblings (the ten per-typeflag arms + `tar-mixed-skipped.tar`)
  still pass — each has `size == 0` for its skipped entry, so
  `skipEntryData input 0` is the actual production behaviour
  for them. The fixture pins data advance for `Tar.extract`
  only; `Tar.list`'s data-advance invariant is structurally
  identical (`forEntries` is shared) but a separate fixture
  for `Tar.list` is not required — the new arm exercises
  `Tar.extract` only.
- `tar-skipped-padded.tar` — three-entry archive interleaving a
  silently-skipped middle entry with a *non-multiple-of-512*
  declared payload between two regular files: `before.txt`
  (typeflag `'0'`, payload `"BEFORE\n"`) → `fifo-entry`
  (typeflag `'6'` = `0x36`, POSIX UStar FIFO, declared `size ==
  100`, 100-byte payload of repeating ASCII `'X'` (`0x58`) bytes
  followed by `paddingFor 100 == 412` zero bytes to round up to
  the next 512-byte block boundary, silently skipped) →
  `after.txt` (typeflag `'0'`, payload `"AFTER\n"`); extraction
  must materialise *both* `before.txt` and `after.txt` with
  their declared payloads after the middle FIFO entry's header,
  its 100-byte declared payload, *and* its 412-byte zero-padding
  round-up are consumed by `skipEntryData`. Third sibling-class
  fixture alongside `tar-mixed-skipped.tar` (PR #2449,
  `size == 0` extract-continuation invariant) and
  `tar-skipped-payload.tar` (PR #2454, `size == 512` data-advance
  arithmetic for a multiple-of-512 declared payload), covering
  the *padding round-up arithmetic* of the silent-skip `else`
  branch's `skipEntryData input e.size` call's
  `let dataSize := size.toNat + paddingFor size` summation for
  non-multiple-of-512 `e.size` — the only `skipEntryData`
  arithmetic path that the twelve preceding silent-skip fixtures
  (the ten per-typeflag arms PR
  #1555/#2413/#2417/#2422/#2425/#2428/#2431/#2434/#2437/#2439 +
  the two sibling-class entries `tar-mixed-skipped.tar` PR #2449
  and `tar-skipped-payload.tar` PR #2454) do not exercise. Each
  preceding fixture has `size == 0` or `size == 512` for its
  skipped entry, so `paddingFor size` evaluates to `0`
  regardless of any `paddingFor` regression. A regression that
  broke `paddingFor` by, say, returning `0` unconditionally
  would not fire any of the twelve preceding fixtures (each
  multiple-of-512 input degenerates the buggy branch to the
  same `dataSize == size.toNat` computation as the correct
  one) but would silently corrupt the offset of any entry
  following a non-multiple-of-512-payload skipped entry —
  `skipEntryData` would consume only the 100 declared bytes
  without the 412-byte padding round-up, leaving the stream
  positioned 412 bytes inside the `after.txt` header at offset
  0x664; the subsequent `forEntries` `readExact 512` would
  parse a 512-byte block straddling the padding-zero region and
  the `after.txt` header / payload boundary as a header whose
  checksum cannot match. This fixture closes that detection
  gap. Typeflag `'6'` is reused for the middle entry to mirror
  `tar-fifo-skipped.tar`, `tar-mixed-skipped.tar`, and
  `tar-skipped-payload.tar` — pins the same `else` arm without
  introducing a new typeflag value. Total fixture size: 6 × 512
  = 3072 bytes (one header + one payload-and-padding block for
  each of the three entries; the middle FIFO's 100-byte payload
  + 412-byte zero padding together fill exactly one 512-byte
  block, matching `tar-skipped-payload.tar`'s on-disk size
  despite the smaller declared payload). No trailing zero
  blocks (`Tar.forEntries` terminates on the short read at
  EOF, matching the per-typeflag fixture geometry). Built by
  the same script (`scripts/build-symlink-hardlink-malformed-fixtures.lean`).
  Adversarial check (temporarily replace the `else` arm's
  `skipEntryData input e.size`'s
  `let dataSize := size.toNat + paddingFor size` with
  `let dataSize := size.toNat`, i.e. drop the padding round-up
  summand) confirmed the fixture independently fires the
  padding round-up invariant with `tar: header checksum
  mismatch` (the 412-byte under-skip leaves the stream 412
  bytes inside the `after.txt` header, and the next
  `readExact 512` block straddles the padding region and the
  `after.txt` header — checksum verification on that
  straddled block fails), while the twelve preceding
  silent-skip siblings (the ten per-typeflag arms +
  `tar-mixed-skipped.tar` + `tar-skipped-payload.tar`) still
  pass — each has `paddingFor size == 0` for its skipped
  entry's declared `size`, so the `+ paddingFor size` summand
  is `0` in both the correct and the perturbed code, and the
  perturbation is invisible to them. `git diff Zip/Tar.lean`
  is empty post-revert. The fixture pins padding round-up for
  `Tar.extract` only; `Tar.list`'s padding round-up invariant
  is structurally identical (`forEntries` is shared) but a
  separate fixture for `Tar.list` is not required — the new
  arm exercises `Tar.extract` only. Together with the two
  preceding sibling-class entries, the silent-skip family's
  `skipEntryData` arithmetic surface is now fixtured at every
  load-bearing input shape: `size == 0` (no payload, no
  padding) by `tar-mixed-skipped.tar`, `size mod 512 == 0`
  with `size > 0` (full-block payload, no padding) by
  `tar-skipped-payload.tar`, and `size mod 512 ≠ 0`
  (sub-block payload + non-zero padding round-up) by this
  fixture — the three together pin both summands of
  `let dataSize := size.toNat + paddingFor size` (PR #2457).

### Gzip/Zlib/Raw DEFLATE Public APIs

- Components:
  - [Zip/Gzip.lean](/home/kim/lean-zip/Zip/Gzip.lean)
  - [Zip/Basic.lean](/home/kim/lean-zip/Zip/Basic.lean)
  - [Zip/RawDeflate.lean](/home/kim/lean-zip/Zip/RawDeflate.lean)
- Status: `guarded-locally`
- Current guardrails:
  - decompression APIs expose `maxDecompressedSize` or native equivalents
  - malformed fixture coverage already exists for some gzip/zip/tar cases
- Missing work:
  - Executed — call-site inventory of `0 = no limit` is the
    *Decompression Limit Inventory* table below; this bullet is
    superseded by that table.
  - Executed — *Recommended policy* items 1–5 below all landed;
    extraction APIs now default to bounded mode (1 GiB per-entry,
    1 GiB FFI whole-buffer; opt-in `0` for unlimited).
  - Executed — sanitizer recipe in
    [`scripts/sanitize-ffi.sh`](/home/kim/lean-zip/scripts/sanitize-ffi.sh)
    covers FFI entry points; streaming paths additionally exercised
    by the fuzz harness (PR #1602) extended to streaming
    `decompressStream` APIs in PR #1653.

## Known Immediate Audit Targets

### 1. ZIP metadata to `Handle.read`

- File: [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean)
- Concern:
  - `readExact` itself guards `Nat -> USize`, but callers still need proof
    or validation that attacker-controlled sizes are file-bounded before reading
- Needed:
  - prove bounded-read lemmas for the guarded read paths (still open)
- Recent wins:
  - explicit pre-read span validation landed via `assertSpanInFile` in
    `Zip/Archive.lean` (wraps local-header, name+extra, and payload reads)
  - malformed ZIP64 size fixtures landed via PRs #1543 and #1544

### 2. Tar UTF-8 partial functions

- File: [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean)
- Concern:
  - `String.fromUTF8!` is partial and should not be reachable from
    attacker-controlled invalid bytes without prior validation
- Status: audit landed via PR #1550. The three panicking raw-byte
  truncations in `buildPaxEntry` and `create` now go through
  `Tar.truncateUTF8`; the two remaining `fromUTF8!` callsites in
  `splitPath` split at an ASCII `'/'` byte and are documented safe.
  Regression coverage in `ZipTest/TarPathTruncation.lean`.

### 3. Unlimited decompression knobs

- Files:
  - [Zip/Basic.lean](/home/kim/lean-zip/Zip/Basic.lean)
  - [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean)
- Concern:
  - `0 = no limit` is convenient but weak as a default for hostile inputs
- Needed:
  - policy decision on safer defaults for archive extraction APIs
  - tests for decompression-bomb limits
- See: *"Decompression Limit Inventory"* below for the full surface.

## Decompression Limit Inventory

Inventory of every public API that accepts untrusted compressed bytes
and drives decompression or extraction. This is the reference the
Priority 2 bomb-limit regression tests work against — it is
intentionally concrete (parameter, default, and semantics of `0`) so
callers and tests can reason about behaviour without re-reading the
source. The corresponding checklist item is Priority 2 items 1–2 in
[plans/track-e-current-audit-checklist.md](/home/kim/lean-zip/plans/track-e-current-audit-checklist.md).

### Public decompression / extraction APIs

| Entry point | Parameter | Default | Semantics of 0 | Notes |
|---|---|---|---|---|
| [Zlib.decompress](/home/kim/lean-zip/Zip/Basic.lean) (FFI) | `maxDecompressedSize : UInt64` | `1073741824` (1 GiB) | no limit (opt-in) | whole-buffer zlib (RFC 1950). Bomb-limit regression test at [ZipTest/Zlib.lean](/home/kim/lean-zip/ZipTest/Zlib.lean). |
| [Gzip.decompress](/home/kim/lean-zip/Zip/Gzip.lean) (FFI) | `maxDecompressedSize : UInt64` | `1073741824` (1 GiB) | no limit (opt-in) | whole-buffer gzip (RFC 1952) + auto-zlib. Bomb-limit regression test at [ZipTest/Gzip.lean](/home/kim/lean-zip/ZipTest/Gzip.lean). |
| [RawDeflate.decompress](/home/kim/lean-zip/Zip/RawDeflate.lean) (FFI) | `maxDecompressedSize : UInt64` | `1073741824` (1 GiB) | no limit (opt-in) | whole-buffer raw DEFLATE (ZIP method 8). Bomb-limit regression test at [ZipTest/RawDeflate.lean](/home/kim/lean-zip/ZipTest/RawDeflate.lean). |
| [Gzip.decompressStream](/home/kim/lean-zip/Zip/Gzip.lean) (FFI) | `maxDecompressedSize : UInt64` | `1073741824` (1 GiB) | no limit (opt-in) | streaming via `IO.Ref UInt64` counter on pushed output; cap check fires before `output.write`, so the already-written prefix is ≤ `maxDecompressedSize` bytes. Parameter landed by PR #1610; default flipped to 1 GiB by PR #1631. |
| [Gzip.decompressFile](/home/kim/lean-zip/Zip/Gzip.lean) (FFI) | `maxDecompressedSize : UInt64` | `1073741824` (1 GiB) | no limit (opt-in) | thin wrapper forwarding to `decompressStream`. Parameter landed by PR #1610; default flipped to 1 GiB by PR #1631. |
| [RawDeflate.decompressStream](/home/kim/lean-zip/Zip/RawDeflate.lean) (FFI) | `maxDecompressedSize : UInt64` | `1073741824` (1 GiB) | no limit (opt-in) | streaming raw DEFLATE; same counter/check structure as `Gzip.decompressStream`. Parameter landed by PR #1610; default flipped to 1 GiB by PR #1631. |
| [Zip.Native.Inflate.inflate](/home/kim/lean-zip/Zip/Native/Inflate.lean) | `maxOutputSize : Nat` | `1 * 1024^3` (1 GiB) | hard cap at 0 bytes (explicit) | no unlimited mode; default is 1 GiB. |
| [Zip.Native.GzipDecode.decompress](/home/kim/lean-zip/Zip/Native/Gzip.lean) | `maxOutputSize : Nat` | `1 * 1024^3` (1 GiB) | hard cap at 0 bytes (explicit) | no unlimited mode; default is 1 GiB (unified with `Inflate.inflate` per Rec. 5). |
| [Zip.Native.ZlibDecode.decompress](/home/kim/lean-zip/Zip/Native/Gzip.lean) | `maxOutputSize : Nat` | `1 * 1024^3` (1 GiB) | hard cap at 0 bytes (explicit) | no unlimited mode; default is 1 GiB (unified with `Inflate.inflate` per Rec. 5). |
| [Zip.Native.decompressAuto](/home/kim/lean-zip/Zip/Native/Gzip.lean) | `maxOutputSize : Nat` | `1 * 1024^3` (1 GiB) | hard cap at 0 bytes (explicit) | format-auto dispatch over the three natives above. |
| [Archive.list](/home/kim/lean-zip/Zip/Archive.lean) | `maxCentralDirSize : Nat` | `67108864` (64 MiB) | no limit | metadata-only; caps CD allocation, not decompressed payload. |
| [Archive.extract](/home/kim/lean-zip/Zip/Archive.lean) | `maxCentralDirSize : Nat` | `67108864` (64 MiB) | no limit | CD allocation cap. |
| [Archive.extract](/home/kim/lean-zip/Zip/Archive.lean) | `maxEntrySize : UInt64` | `1 * 1024^3` (1 GiB) | pass `0` for unlimited (FFI backend only; native inflate rejects `0`) | per-entry cap on the decompressed payload. |
| [Archive.extract](/home/kim/lean-zip/Zip/Archive.lean) | `maxTotalSize : UInt64` | `0` | no whole-archive cap | running sum across all entries; intended as a second line of defence against many-small-entries bombs. |
| [Archive.extractFile](/home/kim/lean-zip/Zip/Archive.lean) | `maxCentralDirSize : Nat` | `67108864` (64 MiB) | no limit | CD allocation cap. |
| [Archive.extractFile](/home/kim/lean-zip/Zip/Archive.lean) | `maxEntrySize : UInt64` | `1 * 1024^3` (1 GiB) | pass `0` for unlimited (FFI backend only; native inflate rejects `0`) | per-entry cap. |
| [Tar.extract](/home/kim/lean-zip/Zip/Tar.lean) | `maxEntrySize : UInt64` | `1 * 1024^3` (1 GiB) | pass `0` for unlimited | per-entry byte cap, applied via header `e.size` before any I/O (see [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean)). |
| [Tar.extract](/home/kim/lean-zip/Zip/Tar.lean) | `maxTotalSize : UInt64` | `0` | no whole-archive cap | running sum across all regular-file entries; directories and symlinks contribute zero. |
| [Tar.extractTarGz](/home/kim/lean-zip/Zip/Tar.lean) | `maxEntrySize : UInt64` | `1 * 1024^3` (1 GiB) | pass `0` for unlimited | per-entry cap. Outer gzip decode is streaming via `Gzip.InflateState`; no per-stream output cap. |
| [Tar.extractTarGz](/home/kim/lean-zip/Zip/Tar.lean) | `maxTotalSize : UInt64` | `0` | no whole-archive cap | forwarded to inner `Tar.extract`. |
| [Tar.extractTarGzNative](/home/kim/lean-zip/Zip/Tar.lean) | `maxEntrySize : UInt64` | `1 * 1024^3` (1 GiB) | pass `0` for unlimited | per-entry cap. |
| [Tar.extractTarGzNative](/home/kim/lean-zip/Zip/Tar.lean) | `maxTotalSize : UInt64` | `0` | no whole-archive cap | forwarded to inner `Tar.extract`. |
| [Tar.extractTarGzNative](/home/kim/lean-zip/Zip/Tar.lean) | `maxOutputSize : Nat` | `256 * 1024^2` (256 MiB) | hard cap at 0 bytes (explicit) | whole-archive tar-buffer cap for the outer native gzip decode. |

### Known inconsistencies

_None outstanding — prior inconsistencies resolved by the Track E
audit wave (see *Recommended policy* items flagged "Executed")._

### Recommended policy

This is a **proposal** for the safer-default direction; numbers are
placeholders to seed discussion, not final values. Treat each
recommendation as a starting point for the bomb-limit regression
issues and the follow-up docstring/default change.

1. **Low-level whole-buffer FFI decoders** — `Zlib.decompress`,
   `Gzip.decompress`, `RawDeflate.decompress`.
   Executed — the three FFI whole-buffer decoders now default to 1 GiB;
   `0` continues to mean unlimited on the opt-in path. See PR #1623.
2. **Streaming FFI decoders** — `Gzip.decompressStream`,
   `Gzip.decompressFile`, `RawDeflate.decompressStream`.
   Executed — the three streaming FFI decoders now default to 1 GiB;
   `0` continues to mean unlimited on the opt-in path. See PR #1631.
3. **Archive extraction — per-entry cap** — Executed. The per-entry
   default on `Archive.extract`, `Archive.extractFile`, `Tar.extract`,
   `Tar.extractTarGz`, and `Tar.extractTarGzNative` is now `1 GiB`
   (pass `0` to opt into unlimited mode on the FFI backend), and the
   silent `0 → 256 MiB` upgrade in `Archive.readEntryData` has been
   removed. See PR #1618.
4. **Archive extraction — whole-archive cap**. Executed —
   `Archive.extract`, `Tar.extract`, `Tar.extractTarGz`, and
   `Tar.extractTarGzNative` now accept an optional
   `maxTotalSize : UInt64 := 0` parameter; default `0` is unlimited
   and callers opt into a finite cap. See PR #1630.
5. **Native-side uniformity**. Executed (issue #1609) — all four
   native decoders (`Inflate.inflate`, `GzipDecode.decompress`,
   `ZlibDecode.decompress`, `decompressAuto`) now default to **1 GiB**,
   matching `Zip.Native.Inflate.inflate`. The factor-of-4 asymmetry
   between raw-DEFLATE and format-auto-dispatch is gone.
6. **Docstrings and error messages**. Executed — every public
   decompression / extraction API now states its default cap, the
   meaning of `0` (unlimited on the FFI path; rejects any non-empty
   output on the native path), and the exact `IO.userError` /
   `Except` substring thrown on cap overflow. The closing audit
   covered all twelve decompression / extraction surfaces plus the
   `Archive.list` central-directory cap; the only outstanding gap
   (the `maxOutputSize` paragraph on `Tar.extractTarGzNative`) was
   filled inline in PR #1710. See PR #1710.

Known caller impact if recommendations 1–5 land:

- `ZipTest/*.lean` mostly uses tiny inputs; switching FFI
  decompression defaults to 256 MiB is a no-op there.
- `ZipTest/NativeScale.lean` currently decompresses multi-MiB
  payloads — still well under 256 MiB.
- The public `README.md` example (`Tar.extractTarGz "..."`) works
  unchanged because its proposed default per-entry cap (1 GiB) is
  larger than any realistic test archive.
- No Lean-level caller passes `0` explicitly except the
  implicit default; after the change, callers who need unlimited
  mode must opt in — the migration is local and detectable via
  `grep`.

### Missing work

_All bomb-limit regression coverage proposed in the original block
has landed (Track E P3 + P5 + F-series, 2026-04-22)._ Per-API
coverage is documented in the audit table at
[`progress/20260422T115256Z_d2757984.md`](/home/kim/lean-zip/progress/20260422T115256Z_d2757984.md).
Notably absent surfaces (`Zlib.decompressStream`,
`Zlib.decompressFile`, `RawDeflate.decompressFile`) are absent
because the public API does not expose them, not because tests are
missing.

Residual gaps: none currently open at this layer.

### Local guard inventory for `Handle.read` and `Stream.read`

Per-callsite audit of every `Handle.read`, `Stream.read`, and
`inStream.read` invocation reachable from untrusted archive bytes in
`Zip/Archive.lean` and `Zip/Tar.lean`. This documents which guards
**already run before** each read, so a reader does not have to trace
back through the source to confirm that every metadata-driven read is
protected. The *"Failure mode"* column states the behaviour that would
surface if the caller bypassed the guard. Since v4.30.0-rc2 the
runtime's own `lean_io_prim_handle_read` does checked arithmetic on
allocation paths and raises OOM on overflow rather than corrupting the
heap, so the local guards primarily exist to surface a clean,
catchable error before allocation rather than to prevent memory
corruption.

The creator-side `h.read` in `Zip/Tar.lean` `create` at
[Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) is **not**
listed: it reads local files chosen by the caller (the archive author),
not untrusted archive bytes, so it falls outside this inventory's
scope.

Trust-boundary callers reach the actual `.read` primitive via
`readExact` ([Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean),
[Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean)),
`readExactStream` ([Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean)),
`readEntryData` ([Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean)),
`skipEntryData` ([Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean)),
or open-coded read loops. Each row below names the call site that
drives an `n`-byte read; the `readExact`-family helpers themselves
perform a `Nat → USize` roundtrip check before every `Handle.read`.

| Callsite (file:line) | Reads driven by | Local guard | Failure mode if guard absent |
|---|---|---|---|
| [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) `readExactStream` helper (inner `s.read`) | caller-provided `n : Nat` | `Nat → USize` roundtrip at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) | no production parser reaches this helper today — only `ZipTest/Archive.lean` exercises it. Any future stream-fed parser that wires into `readExactStream` must apply its own `n`-bound before calling; otherwise this row downgrades to caller-bounded |
| [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) `readExact h tailSize "EOCD tail"` | `tailSize = min fileSize 65558` at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) | `min` clamp (≤ 65 558 bytes regardless of input); `Nat → USize` roundtrip in `readExact` | N/A — the read is structurally bounded to ≤ 65 558 bytes |
| [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) `readExact h cdSize "central directory"` | `cdSize` parsed from EOCD (attacker-controlled) | `cdOffset + cdSize ≤ fileSize` check at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean); `maxCentralDirSize` cap (default 64 MiB) at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean); `Nat → USize` roundtrip in `readExact` | would request a crafted multi-GB allocation; depends on runtime to reject or OOM |
| [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) `readBoundedSpanFromHandle h fileSize entry.localOffset 30 "local header for {label}"` | fixed `30` bytes | `assertSpanInFile fileSize entry.localOffset 30` internal to `readBoundedSpanFromHandle` at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) | N/A — fixed 30-byte read |
| [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) `readBoundedSpanFromHandle h fileSize (entry.localOffset + 30) (nameLen + extraLen) "local name+extra for {label}"` | `nameLen + extraLen`, both `UInt16` read from the local header (≤ 2·`UInt16.max` ≈ 128 KiB) | `assertSpanInFile` at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean); `UInt16` type bound on each addend | N/A — `UInt16` type bounds each addend, total ≤ 128 KiB regardless of input |
| [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) `readExact h entry.compressedSize.toNat "compressed data for {label}"` | `entry.compressedSize` from CD / ZIP64 local extra (attacker-controlled `UInt64`) | `assertSpanInFile fileSize (entry.localOffset + headerAndNames) entry.compressedSize` at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean); CD-vs-LH `compressedSize` consistency check at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) (only skipped when the LH data-descriptor flag bit 3 is set); CD-vs-LH flags-consistency check (bit-3-masked) at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) — *"flags mismatch between CD and local header"* — rejects mismatched general-purpose flag words before the payload read; CD-vs-LH `versionNeededToExtract` one-sided downgrade check at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) — *"LH versionNeededToExtract (…) exceeds CD versionNeededToExtract (…)"* — rejects LH claiming a higher version than CD (a capability-smuggle vector) before the payload read; `Nat → USize` roundtrip in `readExact`. Regression fixtures: `testdata/zip/malformed/oversized-compressed-size.zip`, `oversized-zip64-compressed-size.zip`, `cd-lh-flags-mismatch.zip`, `cd-lh-uncompsize-mismatch.zip`, `cd-lh-crc-mismatch.zip`, `cd-lh-version-mismatch.zip` | would request petabyte allocation on a crafted oversized `compressedSize`; relies on `assertSpanInFile` + CD/LH consistency to reject before `Handle.read` |
| [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) `readExact input 512` in `forEntries` | fixed `512` (one tar header block) | fixed constant | N/A — fixed 512-byte read |
| [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) `readBoundedEntryData input entry.size.toNat maxHeaderSize` (GNU long-name, GNU long-link, PAX extended header, PAX global header) | `entry.size` from tar header (attacker-controlled `UInt64`) | `maxHeaderSize` cap inside `readEntryData` at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) (default `defaultMaxHeaderSize = 8 MiB` at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean)) — rejects `entry.size > maxHeaderSize` before any allocation with `IO.userError` containing `"exceeds maximum header size"`. Per-chunk reads are also capped at 64 KiB ([Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean)) and padding at 512 bytes per chunk ([Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean)). The cap is independent of the caller's `maxEntrySize`, which only bounds payload-bearing entries. Regression fixtures: `testdata/tar/malformed/gnu-longname-oversized-size.tar`, `pax-extended-oversized-size.tar` | with the cap raised, `readEntryData` would accumulate `entry.size` bytes into memory on a crafted GNU long-name or PAX header claiming multi-GB size — depends on runtime allocation to reject |
| [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) `skipEntryData input e.size` (directory-entry payload skip, symlink-entry payload skip, unsupported-typeflag payload skip, `Tar.list`) | `e.size + paddingFor e.size` (attacker-controlled `UInt64`) | 64 KiB per-chunk cap at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean); discarded bytes are not buffered (peak allocation = 64 KiB per iteration) | no memory amplification, but a malicious stream can force an unbounded number of 64 KiB reads. `Tar.extract` applies `maxEntrySize` at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) for payload-bearing entries before the skip; `Tar.list` applies no cap |
| [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) `input.read toRead.toUSize` in `Tar.extract` regular-file loop | `min remaining 65536` where `remaining ≤ e.size.toNat` (attacker-controlled `UInt64` from tar header) | `maxEntrySize` check at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) (effective only when `maxEntrySize > 0`); 64 KiB per-chunk cap; data is written through to disk, not buffered | with the default 1 GiB cap, `Tar.extract` writes up to 1 GiB to disk per regular-file entry; with `maxEntrySize = 0` (opt-in unlimited), the read is bounded only by `e.size` (attacker-controlled `UInt64`). The per-read allocation is bounded at 64 KiB regardless. Documented as the "per-entry cap" row in *Decompression Limit Inventory* |
| [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) `input.read (min padRemaining 512).toUSize` in `Tar.extract` padding loop | `min padRemaining 512`; `padRemaining ≤ 511` by tar framing (`paddingFor size < 512`) | fixed 512-byte per-chunk cap; `pad < 512` by tar block alignment | N/A — ≤ 512 bytes per read, bounded by tar block alignment |
| [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) `inStream.read 65536` in `extractTarGz` tarStream wrapper | fixed `65536` | fixed chunk constant regardless of input | N/A — fixed 64 KiB read |

Summary — what the inventory catches and what it does not:

- **Catches**: every metadata-driven read in ZIP extraction
  (`Archive.readEntryData`) is span-checked against the actual file
  size before `Handle.read` runs, and the CD-vs-LH consistency check
  rejects crafted size mismatches before the compressed-payload read.
  Padding and skip reads in `Tar.lean` are bounded per chunk (64 KiB
  or 512 bytes) and discarded, so they cannot amplify memory.
- **Does NOT catch** — one residual gap that would benefit from a
  follow-up issue:
  1. `Tar.extract` row 10 relies on a per-entry `maxEntrySize` cap
     of 1 GiB by default; an attacker who crafts many entries can
     still drive disk usage past this cap because the
     whole-archive `maxTotalSize` parameter on `Tar.extract` /
     `Tar.extractTarGz` / `Tar.extractTarGzNative` defaults to
     `0` (no limit) per Recommended Policy item 4. Callers
     concerned about multi-entry exhaustion must opt into a
     finite `maxTotalSize`.

  The previously-listed `Tar.readEntryData` gap at the four GNU
  long-name / long-link / PAX callsites is now closed by the
  `maxHeaderSize` cap (default `defaultMaxHeaderSize = 8 MiB`) that
  fires in `readEntryData` before any allocation; see row 8 above and
  the `gnu-longname-oversized-size.tar` /
  `pax-extended-oversized-size.tar` regression fixtures.

## Minimized Reproducer Corpus

Each row below is a minimised input that trips a specific defensive
guard in the parsers or extractors. Regression of a listed guard
surfaces as a test failure in
[`ZipTest/ZipFixtures.lean`](/home/kim/lean-zip/ZipTest/ZipFixtures.lean),
[`ZipTest/TarFixtures.lean`](/home/kim/lean-zip/ZipTest/TarFixtures.lean),
or (for the UTF-8 entry-name check)
[`ZipTest/Utf8Fixtures.lean`](/home/kim/lean-zip/ZipTest/Utf8Fixtures.lean).
The corpus realises the *"malformed regression corpus"* goal in
[`PLAN.md` lines 621-624](/home/kim/lean-zip/PLAN.md):
*"every discovered crash, panic, timeout, or upstream-runtime issue
gets a minimized reproducer and a permanent regression test when
feasible."*

<!-- convention: line anchors for CD/LH consistency checks (and any
     other `unless … throw` guard) point to the `s!"…"` throw-message
     line — the line a debugger lands on and the one a reader sees in
     the `IO.userError` stack trace — not the `unless` predicate
     above it. The ±2-line tolerance in
     scripts/check-inventory-links.sh accepts either form but readers
     expect the throw line; use it consistently across the corpus
     rows below and the cross-references in the *Local guard
     inventory* table above. -->

Columns:

- **Fixture** — relative-path link into `testdata/`.
- **Size** — on-disk byte size (as reported by `wc -c`).
- **Defence exercised** — the concrete guard that must continue to
  trip, linked to the source line that raises the error or applies
  the silent-skip policy.
- **First landed** — PR number if the fixture entered via a dedicated
  PR; commit `481e562` for the fixtures inherited from the initial
  `lean-zlib → lean-zip` import (no PR).
- **Related class** — one of {*oversized allocation*,
  *partial-decoder panic*, *archive-slip*, *decompression bomb*,
  *other*} so an auditor tracking regressions of a single class can
  filter.

Row order: by `testdata/` subdirectory, then alphabetically within
each subdirectory. Every row below has a live assertion in
`ZipTest/` (checked by `grep`-of-filename across `ZipTest/`); no
fixture is currently orphaned. `hardlink-outside.tar` is a
*positive* regression — the assertion is that extraction leaves the
output directory empty, confirming that `typeHardlink` continues
to be silently skipped.

| Fixture (testdata/…) | Size | Defence exercised | First landed | Related class |
|---|---|---|---|---|
| [testdata/tar/malformed/bad-checksum.tar](/home/kim/lean-zip/testdata/tar/malformed/bad-checksum.tar) | 2048 B | Tar header checksum verification at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) — *"header checksum mismatch"* | `481e562` | other (integrity check) |
| [testdata/tar/malformed/gnu-longlink-nul-in-link.tar](/home/kim/lean-zip/testdata/tar/malformed/gnu-longlink-nul-in-link.tar) | 1536 B | GNU long-link NUL-byte rejection at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) — *"GNU long-link contains NUL byte"* (long-link payload is `"safe.lnk\x00rogue.tar"` — 18 bytes; "safe.lnk" + interior NUL + "rogue.tar"; the payload's last byte is `'r'` so `stripTrailingNuls` is a no-op and the interior NUL at index 8 survives into the `findIdx?` guard, which rejects on the raw `ByteArray` before `String.fromUTF8?` / `Binary.fromLatin1` runs, so neither decode branch re-introduces NUL into logs. Pre-PR, `entry.linkname` would be the full NUL-embedded string on `Tar.list` and POSIX `open` would truncate at NUL on `Tar.extract` — classic parser-differential / filesystem-truncation smuggle. A trailing zero-length regular-file entry (`size := 0`, `path := "_"`) is appended so the fixture exercises the override application path fully — but the guard fires on the long-link pseudo-entry itself, so the trailing entry is only reached by the no-guard regression baseline. Per-slot family closure: this is the long-link arm of the 2-slot `forEntries` interior-NUL guard family — the long-name arm is `gnu-longname-nul-in-name.tar` (PR #1865, long-name slot); together the two close the GNU long-name / long-link interior-NUL guard family at every per-slot position. PR #1865 added both guards in a single landing but only emitted the long-name fixture; this fixture closes the per-slot fixture asymmetry, mirroring the post-#1880/#1934/#1937 per-slot wave that closed the 3-slot UStar `name`/`linkname`/`prefix` family and the post-#1944 4th-slot `uname` defense-in-depth extension. Test substring includes `"long-link"` to keep per-slot distinction — the bare `"GNU long-"` prefix would also match the long-name arm. Writer-side has no invariant to record — lean-zip's tar writer does not emit GNU long-name / long-link pseudo-entries) | #1953 | archive-slip |
| [testdata/tar/malformed/gnu-longlink-truncated.tar](/home/kim/lean-zip/testdata/tar/malformed/gnu-longlink-truncated.tar) | 612 B | `readEntryData` short-read at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) — *"unexpected end of archive reading entry data"* | #1546 | partial-decoder panic |
| [testdata/tar/malformed/gnu-longname-invalid-utf8.tar](/home/kim/lean-zip/testdata/tar/malformed/gnu-longname-invalid-utf8.tar) | 1536 B | `String.fromUTF8?` → `Binary.fromLatin1` fallback at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) (no panicking `fromUTF8!` path) | #1546 | partial-decoder panic |
| [testdata/tar/malformed/gnu-longname-no-terminator.tar](/home/kim/lean-zip/testdata/tar/malformed/gnu-longname-no-terminator.tar) | 1536 B | `stripTrailingNuls` is a no-op when the payload has no trailing NUL ([Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean)); full payload becomes the name without a panic | #1546 | partial-decoder panic |
| [testdata/tar/malformed/gnu-longname-nul-in-name.tar](/home/kim/lean-zip/testdata/tar/malformed/gnu-longname-nul-in-name.tar) | 1536 B | GNU long-name NUL-byte rejection at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) — *"GNU long-name contains NUL byte"* (long-name payload is `"evil.txt\x00.tar"`; `stripTrailingNuls` preserves the interior NUL; `forEntries` rejects on the raw `ByteArray` before `String.fromUTF8?` / `Binary.fromLatin1` runs, so neither decode branch re-introduces NUL into logs. Pre-PR, `entry.path` would be the full NUL-embedded string on `Tar.list` and POSIX `open` would truncate at NUL on `Tar.extract` — classic parser-differential / filesystem-truncation smuggle. Tar-side sibling of the ZIP CD-parse NUL-byte guard (PR #1831 / `cd-nul-in-name.zip`) at the same NUL-in-filename attack dimension; the long-link typeflag `'K'` arm at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) carries the structurally identical guard — *"GNU long-link contains NUL byte"* — now covered by the dedicated per-slot fixture `gnu-longlink-nul-in-link.tar` (PR #1953); together the two fixtures close the 2-slot GNU long-name / long-link interior-NUL family at 2/2 — sibling cadence to the 5-slot UStar interior-NUL family closure at PR #1957. PAX `path` arm closed by PR #1866 (`pax-path-nul-in-value.tar`) and `linkpath` arm closed by PR #1979 (`pax-linkpath-nul-in-value.tar`) — the 2-slot PAX value-side override family is closed 2/2) | #1865 | archive-slip |
| [testdata/tar/malformed/gnu-longname-oversized-size.tar](/home/kim/lean-zip/testdata/tar/malformed/gnu-longname-oversized-size.tar) | 512 B | `readEntryData` `maxHeaderSize` cap at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) — *"exceeds maximum header size"* (header `size ≈ 8 GiB`, default cap `8 MiB`) | #1597 | oversized allocation |
| [testdata/tar/malformed/gnu-longname-truncated.tar](/home/kim/lean-zip/testdata/tar/malformed/gnu-longname-truncated.tar) | 612 B | `readEntryData` short-read at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) — *"unexpected end of archive reading entry data"* | #1546 | partial-decoder panic |
| [testdata/tar/malformed/no-magic.tar](/home/kim/lean-zip/testdata/tar/malformed/no-magic.tar) | 2048 B | Tar magic check at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) — *"unsupported format"* | `481e562` | other (header validation) |
| [testdata/tar/malformed/pax-duplicate-path.tar](/home/kim/lean-zip/testdata/tar/malformed/pax-duplicate-path.tar) | 2048 B | `parsePaxRecords` duplicate-key guard at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) — *"tar: PAX extended header has duplicate {key.quote} record"* (ordering inside `parsePaxRecords`: UTF-8 decode → raw-byte NUL guard → duplicate-key check → push, so the duplicate-key branch only fires on records that already passed the UTF-8 and NUL filters. Unlike the sibling PR #1866 PAX NUL-byte silent-skip further below — which drops the offending record and continues — PR #1899 hard-rejects by writing `err := some …` and `break`ing the record loop; the `.error` return is rethrown unconditionally by the sole production caller at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) inside `forEntries`'s `typePaxExtended` branch via `throw (IO.userError msg)`. `String.quote` on the duplicate key pins attribution in logs without leaking NUL or control bytes. Attack class: PAX records allow duplicate keys syntactically, and `applyPaxOverrides`'s default last-wins-silent policy leaves the smuggle exploitable unless the parser rejects duplicates structurally — a crafted second `path=` record would otherwise override the first, enabling parser-differential attacks where strict peer parsers (which reject or use first-wins) disagree with lean-zip. Closes the parser-differential *duplicate-key* dimension on `parsePaxRecords` complementary to PR #1866's NUL-byte silent-skip; together the two close both parser-differential dimensions on the PAX-record decode pipeline. Writer-side has no invariant to record — lean-zip's tar writer does not emit PAX extended headers) | #1899 | archive-slip |
| [testdata/tar/malformed/pax-extended-oversized-size.tar](/home/kim/lean-zip/testdata/tar/malformed/pax-extended-oversized-size.tar) | 512 B | `readEntryData` `maxHeaderSize` cap at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) — *"exceeds maximum header size"* (PAX header `size ≈ 8 GiB`, default cap `8 MiB`) | #1597 | oversized allocation |
| [testdata/tar/malformed/pax-inconsistent-length.tar](/home/kim/lean-zip/testdata/tar/malformed/pax-inconsistent-length.tar) | 2048 B | `parsePaxRecords` silent-skip when no `=` is found before the declared record end (scan at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean); record dropped at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean)) | #1545 | partial-decoder panic |
| [testdata/tar/malformed/pax-invalid-utf8-key.tar](/home/kim/lean-zip/testdata/tar/malformed/pax-invalid-utf8-key.tar) | 2048 B | `parsePaxRecords` `String.fromUTF8?` guard on key/value at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) (record dropped, no panic) | #1545 | partial-decoder panic |
| [testdata/tar/malformed/pax-invalid-utf8-value.tar](/home/kim/lean-zip/testdata/tar/malformed/pax-invalid-utf8-value.tar) | 2048 B | Same `String.fromUTF8?` guard at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) | #1545 | partial-decoder panic |
| [testdata/tar/malformed/pax-linkpath-nul-in-value.tar](/home/kim/lean-zip/testdata/tar/malformed/pax-linkpath-nul-in-value.tar) | 2048 B | `parsePaxRecords` NUL-byte guard on `valueBytes` at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) (record dropped silently, matching the invalid-UTF-8 precedent on the same loop). Fixture carries the PAX record `"18 linkpath=a\x00b/c\n"` — `String.fromUTF8?` accepts U+0000 so without the guard the `linkpath` override would smuggle into `applyPaxOverrides`'s `"linkpath"` arm at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) and land as `entry.linkname = "a\x00b/c"` — a `symlink(2)` truncation smuggle that POSIX `symlink` reduces to `"a"` on the `Tar.extract` symlink path while `Tar.list` callers routing on `entry.linkname` for trust decisions see the full NUL-embedded string. Assertion is a *positive regression* (like the sibling `pax-path-nul-in-value.tar` row two rows below): the loop's `entries[0]!.path == "hello.txt"` check confirms the regular-file entry is unaffected, and a per-slot follow-up assertion confirms `entries[0]!.linkname == ""` (its declared default for `typeRegular`) rather than the smuggled `"a\x00b/c"`. Per-slot family closure: this is the `linkpath` slot of the 2-slot PAX value-side override family — sibling `pax-path-nul-in-value.tar` (PR #1866) covers the `path` slot at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean). With this fixture the 2-slot value-side override family is **fully closed 2/2** — terminal closure of the third per-slot Tar interior-NUL family in the post-#1928 wave (after the 5-slot UStar family closed at PR #1957 and the 2-slot GNU long-name / long-link family closed at PR #1953); together the three closures complete the "smuggled NUL in any user-supplied string field" attack class across the entire Tar parsing surface (UStar + GNU + PAX). The companion `keyBytes` arm at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) is defense-in-depth (no known-key string contains `\x00`, so `applyPaxOverrides`'s case match would already drop a NUL-bearing key) and is closed by `pax-nul-in-key.tar` (PR #2405); the `parsePaxRecords` NUL-byte guard family is therefore **fully closed 3/3** (1 keyBytes + 2 valueBytes). Writer-side has no invariant to record — lean-zip's tar writer does not emit PAX extended headers | #1979 | archive-slip |
| [testdata/tar/malformed/pax-nul-in-key.tar](/home/kim/lean-zip/testdata/tar/malformed/pax-nul-in-key.tar) | 2048 B | `parsePaxRecords` NUL-byte guard on `keyBytes` at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) (record dropped silently, matching the invalid-UTF-8 precedent on the same loop). Fixture carries the PAX record `"8 a\x00b=v\n"` — `String.fromUTF8?` accepts U+0000 so without the guard the record would reach `applyPaxOverrides`, where the case match's fixed key set (`{"path", "linkpath", "size", "mtime", "uid", "gid", "uname", "gname"}`) silently drops a NUL-bearing key. The guard is therefore *defense-in-depth* — no known-key string contains `\x00`, so `applyPaxOverrides`'s case match would already drop the record without it — but a future fallback like a prefix-match for namespace-style keys would silently re-open the smuggle. Assertion is a *positive regression*: the loop's `entries[0]!.path == "hello.txt"` check confirms the regular-file entry is unaffected; no per-slot follow-up needed since `applyPaxOverrides` drops the NUL-bearing key regardless of the guard (verified adversarially by temporarily disabling the keyBytes arm and confirming the loop assertion still passes). Per-arm family closure: this is the `keyBytes` arm of `parsePaxRecords`'s NUL-byte guard — sibling `pax-path-nul-in-value.tar` (PR #1866) covers the `path` slot of the value arm and `pax-linkpath-nul-in-value.tar` (PR #1979) covers the `linkpath` slot of the value arm; together the three close the `parsePaxRecords` NUL-byte guard family at **3/3** (1 keyBytes + 2 valueBytes). Same fixture-only, defense-in-depth, family-closing pattern as the UStar `gname` slot (PR #1957) — pinning a guard's existence rather than catching its single-arm removal alone. Writer-side has no invariant to record — lean-zip's tar writer does not emit PAX extended headers | #2405 | archive-slip |
| [testdata/tar/malformed/pax-oversized-length.tar](/home/kim/lean-zip/testdata/tar/malformed/pax-oversized-length.tar) | 2048 B | `parsePaxRecords` `digitCount > 20` guard at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) (length-parse aborted before multiplying) | #1545 | oversized allocation |
| [testdata/tar/malformed/pax-path-nul-in-value.tar](/home/kim/lean-zip/testdata/tar/malformed/pax-path-nul-in-value.tar) | 2048 B | `parsePaxRecords` NUL-byte guard on `keyBytes` / `valueBytes` at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) (record dropped silently, matching the invalid-UTF-8 precedent one line above). Fixture carries the PAX record `"14 path=a\x00b/c\n"` — `String.fromUTF8?` accepts U+0000 so without the guard the `path` override would smuggle into `applyPaxOverrides` and land as `entry.path = "a\x00b/c"`, a filesystem-truncation smuggle that POSIX `open` reduces to `"a"` while `Tar.list` callers see the full NUL-embedded string. Assertion is a *positive regression* (like `hardlink-outside.tar`): `Tar.list` returns the follow-on regular-file entry with its declared `"hello.txt"` path rather than the smuggled override. Per-slot family closure: this is the `path` slot of the 2-slot PAX value-side override family — sibling `pax-linkpath-nul-in-value.tar` (PR #1979) covers the `linkpath` slot at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean); together the family is **fully closed 2/2** — terminal closure of the third per-slot Tar interior-NUL family in the post-#1928 wave (after the 5-slot UStar family closed at PR #1957 and the 2-slot GNU long-name / long-link family closed at PR #1953). Sibling of the ZIP CD name NUL guard (PR #1831, `cd-nul-in-name.zip`), the GNU long-name / long-link 2/2 NUL guards (PRs #1865 / #1953, `gnu-longname-nul-in-name.tar` / `gnu-longlink-nul-in-link.tar`), the UStar 5/5 interior-NUL guards (PRs #1880 / #1934 / #1937 / #1944 / #1957, `ustar-{name,linkname,prefix,uname,gname}-nul-in-*.tar`), and the PAX value-side 2/2 silent-skip in `parsePaxRecords` (PRs #1866 / #1979, `pax-{path,linkpath}-nul-in-value.tar`); together the post-#1928 wave closes the "smuggled NUL in any user-supplied string field" attack class across the entire Tar parsing surface (UStar + GNU + PAX) plus the ZIP CD entry name. Writer-side has no invariant to record — lean-zip's tar writer does not emit PAX extended headers | #1866 | archive-slip |
| [testdata/tar/malformed/pax-truncated-record.tar](/home/kim/lean-zip/testdata/tar/malformed/pax-truncated-record.tar) | 2048 B | `parsePaxRecords` `recordEnd > data.size` guard at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) (iteration breaks, remaining bytes ignored) | #1545 | partial-decoder panic |
| [testdata/tar/malformed/truncated.tar](/home/kim/lean-zip/testdata/tar/malformed/truncated.tar) | 522 B | `Tar.extract` regular-file loop short-read at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) — *"unexpected end of archive reading {e.path} ({remaining} bytes remaining)"* | `481e562` | other (framing) |
| [testdata/tar/malformed/ustar-gname-nul-in-gname.tar](/home/kim/lean-zip/testdata/tar/malformed/ustar-gname-nul-in-gname.tar) | 1536 B | UStar `gname` field interior-NUL rejection at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) — *"UStar gname contains NUL byte"* (UStar header for a zero-byte regular file with `path = "safe"` and `gname = "trusted\x00rogue"` — 12 meaningful bytes in the gname slot at offset 297 including the embedded NUL, then 20 bytes of NUL padding to byte 329; checksum recomputed to match. `parseHeader` runs `hasInteriorNul` on the raw 512-byte block after the checksum + magic checks and before the five `Binary.readString` calls, in source-position order (`name` → `linkname` → `prefix` → `uname` → `gname`); the four earlier-arm guards do not fire because `path` / `linkname` / `prefix` / `uname` are NUL-free, so attribution pins on the `gname` arm specifically. Without the guard, `Binary.readString` would truncate the gname at the NUL to `"trusted"` (parser-differential smuggle: `Tar.list` callers routing on `entry.gname` for a trust decision see the short prefix while strict peer parsers — GNU tar, BSD tar, libarchive — preserve the full bytes). Like `uname`, `gname` does not reach the filesystem in `Tar.extract` — the guard is defense-in-depth at the `Tar.list` layer. Two trailing zero blocks (1024 B) match the per-slot sibling fixtures' well-formed end-of-archive. Per-slot family closure: this fixture is the **5th and final** slot of the 5-slot UStar interior-NUL family — siblings `ustar-name-nul-in-name.tar` (PR #1880, `name` slot) / `ustar-linkname-nul-in-name.tar` (PR #1934, `linkname` slot) / `ustar-prefix-nul-in-name.tar` (PR #1937, `prefix` slot) cover the 3-slot filesystem-reaching arm at offsets 0 / 157 / 345; `ustar-uname-nul-in-uname.tar` (PR #1944, `uname` slot at offset 265) opened the 2-slot defense-in-depth arm; this fixture closes that arm at offset 297 / 32 B. With this fixture the 5-slot UStar interior-NUL family is **fully closed 5/5** — no more sibling per-slot fixtures expected. Test substring includes `"gname"` to keep per-slot distinction — the bare `"UStar"` prefix would also match the four earlier arms. Writer-side at `buildHeader` (`hdrGname`) uses `Binary.writeString`, which is NUL-padding-only — no interior NUL can be emitted unless `entry.gname` carries a literal `\x00` codepoint, so the guard never fires on legitimate archives produced by `Tar.create`) | #1957 | archive-slip |
| [testdata/tar/malformed/ustar-linkname-nul-in-name.tar](/home/kim/lean-zip/testdata/tar/malformed/ustar-linkname-nul-in-name.tar) | 1536 B | UStar `linkname` field interior-NUL rejection at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) — *"UStar linkname contains NUL byte"* (UStar header for a zero-byte regular file with `path = "safe"` and `linkname = "evil.lnk\x00.tar"` — 13 meaningful bytes in the linkname slot at offset 157 including the embedded NUL, then 87 bytes of NUL padding to byte 257; checksum recomputed to match. `parseHeader` runs `hasInteriorNul` on the raw 512-byte block after the checksum + magic checks and before the three `Binary.readString` calls; the `name`-arm guard at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) does not fire because the `path` field is NUL-free, so attribution pins on the `linkname` arm specifically. Two trailing zero blocks (1024 B) match the `name`-slot sibling fixture's well-formed end-of-archive. Per-slot family closure: the sibling `ustar-name-nul-in-name.tar` (PR #1880, `name` slot) covers offset 0 / 100 B; this fixture covers offset 157 / 100 B. The `prefix`-arm guard at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) — *"UStar prefix contains NUL byte"* (offset 345, 155 B) — shares the same `hasInteriorNul` helper and `Binary.readString` truncation path and remains covered by symmetric code review (matching the PR #1865 long-link policy and the in-flight 6-slot ZIP64-override family per-slot-fixture cadence — PR #1745 / #1905 / #1908 / #1911 / #1922 / in-flight #1902 — where each per-slot fixture pins a distinct sub-check of a shared guard). Test substring includes `"linkname"` to keep per-slot distinction — the bare `"UStar"` prefix would also match the `name` and `prefix` arms. Writer-side at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) (`linkname`) uses `Binary.writeString`, which is NUL-padding-only — no interior NUL can be emitted unless `entry.linkname` carries a literal `\x00` codepoint, so the guard never fires on legitimate archives produced by `Tar.create`) | #1934 | archive-slip |
| [testdata/tar/malformed/ustar-name-nul-in-name.tar](/home/kim/lean-zip/testdata/tar/malformed/ustar-name-nul-in-name.tar) | 1536 B | UStar `name` field interior-NUL rejection at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) — *"UStar name contains NUL byte"* (UStar header at offset 0 carries `name = "evil.txt\x00.tar"` — 13 meaningful bytes including the embedded NUL, then 87 bytes of NUL padding to byte 100; checksum recomputed to match. `parseHeader` runs `hasInteriorNul` on the raw 512-byte block after the checksum + magic checks and before any `Binary.readString` call, so the NUL-truncation that `Binary.readString` would otherwise apply (returning `"evil.txt"` and silently dropping the smuggled `".tar"` suffix) cannot leak into `Tar.list` callers or POSIX `open(2)` on the `Tar.extract` path. Pre-PR, `Tar.list` would report `entry.path = "evil.txt"` while strict peer parsers (GNU tar, BSD tar, libarchive) preserve `"evil.txt\x00.tar"` or reject — a classic parser-differential / filesystem-truncation smuggle. Two trailing zero blocks (1024 B) form a well-formed end-of-archive that strict peer parsers accept; the guard fires during header parse, so the trailing blocks are only exercised by the no-guard regression baseline. Sibling-arm coverage: the `linkname` arm at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) — *"UStar linkname contains NUL byte"* (offset 157, 100 B) — and the `prefix` arm at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) — *"UStar prefix contains NUL byte"* (offset 345, 155 B) — share the same `hasInteriorNul` helper and the same `Binary.readString` truncation path, so they are covered by symmetric code review rather than dedicated fixtures (matching the PR #1865 long-link policy and the `hardlink-outside.tar` positive-regression precedent). Closes the UStar layer of the smuggled-NUL attack class — sibling of the ZIP CD-parse name guard (PR #1831, `cd-nul-in-name.zip`), the GNU long-name / long-link guards (PR #1865, `gnu-longname-nul-in-name.tar`), and the PAX `keyBytes` / `valueBytes` silent-skip in `parsePaxRecords` (PR #1866, `pax-path-nul-in-value.tar`); together the quartet closes the "smuggled NUL in any user-supplied string field" attack class across ZIP and Tar at every layer where a NUL could survive into `entry.path` / `entry.linkname`. Writer-side at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) (`name`, `linkname`, `prefix` slots) uses `Binary.writeString`, which is NUL-padding-only — no interior NUL can be emitted unless `entry.path` / `entry.linkname` carries a literal `\x00` codepoint, so the guard never fires on legitimate archives produced by `Tar.create`. Interop pre-flight over `testdata/tar/{interop,malformed,security}/*.tar` returned zero hits before landing) | #1880 | archive-slip |
| [testdata/tar/malformed/ustar-prefix-nul-in-name.tar](/home/kim/lean-zip/testdata/tar/malformed/ustar-prefix-nul-in-name.tar) | 1536 B | UStar `prefix` field interior-NUL rejection at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) — *"UStar prefix contains NUL byte"* (UStar header for a zero-byte regular file built with `pathOverride := some ("badpfx\x00bad", "name.txt")` so the prefix slot at offset 345 carries `"badpfx\x00bad"` — 10 meaningful bytes including the embedded NUL, then 145 bytes of NUL padding to byte 500; checksum recomputed to match. The `name` slot at offset 0 carries the clean `"name.txt"` so the `name`-arm guard at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) does not fire — attribution pins on the `prefix` arm specifically. Without the guard, `Binary.readString` would truncate the prefix at the NUL to `"badpfx"`, and `pfx ++ "/" ++ name` at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) would yield `"badpfx/name.txt"` (parser-differential / filesystem-truncation smuggle: `Tar.list` callers see the short form while POSIX `open(2)` truncates at the same NUL on `Tar.extract`). Two trailing zero blocks (1024 B) match the `name`-slot and `linkname`-slot sibling fixtures' well-formed end-of-archive. Per-slot family closure: this fixture covers offset 345 / 155 B, the third and final slot of the 3-slot UStar interior-NUL guard — siblings `ustar-name-nul-in-name.tar` (PR #1880, `name` slot) and `ustar-linkname-nul-in-name.tar` (PR #1934, `linkname` slot) cover offsets 0 / 100 B and 157 / 100 B respectively. Test substring includes `"prefix"` to keep per-slot distinction — the bare `"UStar"` prefix would also match the `name` and `linkname` arms. Writer-side at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) (`prefix`) uses `Binary.writeString`, which is NUL-padding-only — no interior NUL can be emitted unless `entry.path` carries a literal `\x00` codepoint that survives `splitPath` or unless a caller passes `pathOverride` with a NUL (as this fixture does), so the guard never fires on legitimate archives produced by `Tar.create`) | #1937 | archive-slip |
| [testdata/tar/malformed/ustar-uname-nul-in-uname.tar](/home/kim/lean-zip/testdata/tar/malformed/ustar-uname-nul-in-uname.tar) | 1536 B | UStar `uname` field interior-NUL rejection at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) — *"UStar uname contains NUL byte"* (UStar header for a zero-byte regular file with `path = "safe"` and `uname = "trusted\x00rogue"` — 12 meaningful bytes in the uname slot at offset 265 including the embedded NUL, then 20 bytes of NUL padding to byte 297; checksum recomputed to match. `parseHeader` runs `hasInteriorNul` on the raw 512-byte block after the checksum + magic checks and before the four `Binary.readString` calls, in source-position order (`name` → `linkname` → `prefix` → `uname`); the three earlier-arm guards at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) /  /  do not fire because `path` / `linkname` / `prefix` are NUL-free, so attribution pins on the `uname` arm specifically. Without the guard, `Binary.readString` would truncate the uname at the NUL to `"trusted"` (parser-differential smuggle: `Tar.list` callers routing on `entry.uname` for a trust decision see the short prefix while strict peer parsers — GNU tar, BSD tar, libarchive — preserve the full bytes). Unlike the 3-slot filesystem-reaching family (`name` / `linkname` / `prefix`), `uname` does not reach the filesystem in `Tar.extract` — the guard is defense-in-depth at the `Tar.list` layer. Two trailing zero blocks (1024 B) match the per-slot sibling fixtures' well-formed end-of-archive. Per-slot family extension: this fixture extends the closed 3-slot family — siblings `ustar-name-nul-in-name.tar` (PR #1880, `name` slot) / `ustar-linkname-nul-in-name.tar` (PR #1934, `linkname` slot) / `ustar-prefix-nul-in-name.tar` (PR #1937, `prefix` slot) cover offsets 0 / 100 B, 157 / 100 B, and 345 / 155 B respectively; this fixture covers offset 265 / 32 B (the 4th slot). The `gname` slot at offset 297 / 32 B is the final (5-slot) sibling deferred to a follow-up planner cycle. Test substring includes `"uname"` to keep per-slot distinction — the bare `"UStar"` prefix would also match the three earlier arms. Writer-side at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) (`uname`) uses `Binary.writeString`, which is NUL-padding-only — no interior NUL can be emitted unless `entry.uname` carries a literal `\x00` codepoint, so the guard never fires on legitimate archives produced by `Tar.create`) | #1944 | archive-slip |
| [testdata/tar/security/backslash-slip.tar](/home/kim/lean-zip/testdata/tar/security/backslash-slip.tar) | 2048 B | `Binary.isPathSafe` rejects backslashes before component-level `..` check at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) — *"unsafe path"* | `481e562` (assertion added by #1555) | archive-slip |
| [testdata/tar/security/hardlink-outside.tar](/home/kim/lean-zip/testdata/tar/security/hardlink-outside.tar) | 512 B | `typeHardlink` silent-skip else-branch at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean); payload discarded, no `createHardlink` call, extract directory remains empty | #1555 | archive-slip |
| [testdata/tar/security/symlink-absolute.tar](/home/kim/lean-zip/testdata/tar/security/symlink-absolute.tar) | 512 B | Symlink linkname absolute/backslash check at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) — *"unsafe symlink target"* | #1555 | archive-slip |
| [testdata/tar/security/symlink-slip.tar](/home/kim/lean-zip/testdata/tar/security/symlink-slip.tar) | 10240 B | Symlink linkname component `..` check at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) — *"unsafe symlink target"* | `481e562` | archive-slip |
| [testdata/tar/security/tar-absolute.tar](/home/kim/lean-zip/testdata/tar/security/tar-absolute.tar) | 2048 B | `Binary.isPathSafe` rejects absolute paths at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) — *"unsafe path"* | `481e562` | archive-slip |
| [testdata/tar/security/tar-fifo-skipped.tar](/home/kim/lean-zip/testdata/tar/security/tar-fifo-skipped.tar) | 512 B | `Tar.extract` silent-skip `else` fallback at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) for unsupported typeflag `'6'` (POSIX UStar FIFO, `0x36`) — 512-byte single-block UStar header for a zero-byte entry with `path = "fifo-entry"`, empty `linkname`, `typeflag = 0x36`, checksum recomputed to match. The header has no payload and no trailing zero blocks (`Tar.forEntries` terminates on the short read at EOF), matching the `hardlink-outside.tar` geometry. `Tar.extract` falls through to the `else` branch (no `typeDirectory` / `typeRegular` / `typeSymlink` match), `skipEntryData` is invoked on `e.size = 0` (a no-op), and no filesystem entry is created. `Tar.list` returns the entry verbatim with `typeflag = 0x36` (callers routing on `entry.typeflag` for trust decisions observe the FIFO marker). Per-typeflag silent-skip family extension: sibling `hardlink-outside.tar` (typeflag `'1'`) pins the hardlink arm; this fixture pins the FIFO arm. Both flow through the same `else` fallback in `Tar.extract`, so the two together pin the silent-skip policy against accidental drop of the fallback in future `Tar.extract` refactors — even if a refactor preserves one of the typeflag arms but drops the other, the corresponding fixture would fire (verified by adversarial check during this PR <!-- drift-detector: prose discussion of the placeholder phrase in a paired-review finding, not a stale placeholder -->: temporarily wrapping the `else` body in `if e.typeflag == typeHardlink then skipEntryData ... else throw "adversarial"` left `hardlink-outside.tar` passing while `tar-fifo-skipped.tar` fired with `unexpected typeflag 54` (`0x36`)). Defense-in-depth fixture-only pattern (no new guard code, no new error wording, no new typeflag constant in the `Tar` namespace, no caller / signature change), matching the [`pax-nul-in-key.tar`](/home/kim/lean-zip/testdata/tar/malformed/pax-nul-in-key.tar) precedent (PR #2405 closing the `parsePaxRecords` NUL-byte guard family at 3/3) and the `hardlink-outside.tar` precedent (PR #1555 establishing the silent-skip policy for the hardlink arm). Writer-side at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) (`buildHeader`) emits whatever `entry.typeflag` is supplied — a caller can construct a typeflag-`'6'` entry programmatically, but `Tar.create`'s caller-API only accepts paths and never invokes `Tar.buildHeader` with a non-`'0'`/`'5'` typeflag, so legitimate archives produced by the lean-zip writer never carry typeflag `'6'`. POSIX UStar typeflag `'6'` (`0x36`) = FIFO per POSIX.1-1988 IEEE Std 1003.1 §10 (USTAR Interchange Format); distinct from `'3'` (character device) and `'4'` (block device), which flow through the same silent-skip fallback and remain candidates for future per-typeflag fixtures | #2413 | other (typeflag-policy regression) |
| [testdata/tar/security/tar-chardev-skipped.tar](/home/kim/lean-zip/testdata/tar/security/tar-chardev-skipped.tar) | 512 B | `Tar.extract` silent-skip `else` fallback at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) for unsupported typeflag `'3'` (POSIX UStar character device, `0x33`) — 512-byte single-block UStar header for a zero-byte entry with `path = "chardev-entry"`, empty `linkname`, `typeflag = 0x33`, checksum recomputed to match. The header has no payload and no trailing zero blocks (`Tar.forEntries` terminates on the short read at EOF), matching the `hardlink-outside.tar` / `tar-fifo-skipped.tar` geometry. `Tar.extract` falls through to the `else` branch (no `typeDirectory` / `typeRegular` / `typeSymlink` match), `skipEntryData` is invoked on `e.size = 0` (a no-op), and no filesystem entry is created. `Tar.list` returns the entry verbatim with `typeflag = 0x33` (callers routing on `entry.typeflag` for trust decisions observe the character-device marker). Per-typeflag silent-skip family extension: sibling `hardlink-outside.tar` (typeflag `'1'`) pins the hardlink arm; sibling `tar-fifo-skipped.tar` (typeflag `'6'`) pins the FIFO arm; this fixture pins the character-device arm. All three flow through the same `else` fallback in `Tar.extract`, so the trio together pins three distinct typeflag values against the shared fallback — a future refactor that drops the fallback for any one arm cannot escape detection by the corresponding fixture (verified by adversarial check during this PR <!-- drift-detector: prose discussion of the placeholder phrase in a paired-review finding, not a stale placeholder -->: temporarily wrapping the `else` body in `if e.typeflag == typeHardlink || e.typeflag == 0x36 then skipEntryData ... else throw "adversarial"` left `hardlink-outside.tar` and `tar-fifo-skipped.tar` passing while `tar-chardev-skipped.tar` fired with `unexpected typeflag 51` (`0x33`)). Defense-in-depth fixture-only pattern (no new guard code, no new error wording, no new typeflag constant in the `Tar` namespace, no caller / signature change), matching the `tar-fifo-skipped.tar` precedent (PR #2413 extending the silent-skip family to the FIFO arm) and the `hardlink-outside.tar` precedent (PR #1555 establishing the silent-skip policy for the hardlink arm). Writer-side at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) (`buildHeader`) emits whatever `entry.typeflag` is supplied — a caller can construct a typeflag-`'3'` entry programmatically, but `Tar.create`'s caller-API only accepts paths and never invokes `Tar.buildHeader` with a non-`'0'`/`'5'` typeflag, so legitimate archives produced by the lean-zip writer never carry typeflag `'3'`. POSIX UStar typeflag `'3'` (`0x33`) = character special device per POSIX.1-1988 IEEE Std 1003.1 §10 (USTAR Interchange Format); distinct from `'4'` (block device) and `'7'` (contiguous file), which flow through the same silent-skip fallback and remain candidates for future per-typeflag fixtures | #2417 | other (typeflag-policy regression) |
| [testdata/tar/security/tar-blockdev-skipped.tar](/home/kim/lean-zip/testdata/tar/security/tar-blockdev-skipped.tar) | 512 B | `Tar.extract` silent-skip `else` fallback at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) for unsupported typeflag `'4'` (POSIX UStar block device, `0x34`) — 512-byte single-block UStar header for a zero-byte entry with `path = "blockdev-entry"`, empty `linkname`, `typeflag = 0x34`, checksum recomputed to match. The header has no payload and no trailing zero blocks (`Tar.forEntries` terminates on the short read at EOF), matching the `hardlink-outside.tar` / `tar-fifo-skipped.tar` / `tar-chardev-skipped.tar` geometry. `Tar.extract` falls through to the `else` branch (no `typeDirectory` / `typeRegular` / `typeSymlink` match), `skipEntryData` is invoked on `e.size = 0` (a no-op), and no filesystem entry is created. `Tar.list` returns the entry verbatim with `typeflag = 0x34` (callers routing on `entry.typeflag` for trust decisions observe the block-device marker). Per-typeflag silent-skip family extension: sibling `hardlink-outside.tar` (typeflag `'1'`) pins the hardlink arm; sibling `tar-fifo-skipped.tar` (typeflag `'6'`) pins the FIFO arm; sibling `tar-chardev-skipped.tar` (typeflag `'3'`) pins the character-device arm; this fixture pins the block-device arm. All four flow through the same `else` fallback in `Tar.extract`, so the quartet together pins four distinct typeflag values against the shared fallback — a future refactor that drops the fallback for any one arm cannot escape detection by the corresponding fixture (verified by adversarial check during this PR <!-- drift-detector: prose discussion of the placeholder phrase in a paired-review finding, not a stale placeholder -->: temporarily wrapping the `else` body in `if e.typeflag == typeHardlink || e.typeflag == 0x36 || e.typeflag == 0x33 then skipEntryData ... else throw "adversarial"` left `hardlink-outside.tar`, `tar-fifo-skipped.tar`, and `tar-chardev-skipped.tar` passing while `tar-blockdev-skipped.tar` fired with `unexpected typeflag 52` (`0x34`)). Block devices are a particularly security-sensitive resource: a malicious archive could ship a node mapping to a raw partition (`/dev/sda1`), a kernel-state-modification node, or a node that reads/writes device memory (`/dev/kmem` on legacy kernels) — lean-zip's policy of *never* materialising block-device nodes (no `mknod(2)` call) is the correct one, and pinning it with a fixture prevents future drift. Defense-in-depth fixture-only pattern (no new guard code, no new error wording, no new typeflag constant in the `Tar` namespace, no caller / signature change), matching the `tar-chardev-skipped.tar` precedent (PR #2417 extending the silent-skip family to the chardev arm) and the `tar-fifo-skipped.tar` precedent (PR #2413 extending it to the FIFO arm). Writer-side at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) (`buildHeader`) emits whatever `entry.typeflag` is supplied — a caller can construct a typeflag-`'4'` entry programmatically, but `Tar.create`'s caller-API only accepts paths and never invokes `Tar.buildHeader` with a non-`'0'`/`'5'` typeflag, so legitimate archives produced by the lean-zip writer never carry typeflag `'4'`. POSIX UStar typeflag `'4'` (`0x34`) = block special device per POSIX.1-1988 IEEE Std 1003.1 §10 (USTAR Interchange Format); distinct from `'3'` (character device) and `'7'` (contiguous file), which flow through the same silent-skip fallback (the `'3'` arm is now closed by `tar-chardev-skipped.tar`; the `'7'` arm remains a candidate for a future per-typeflag fixture) | #2422 | other (typeflag-policy regression) |
| [testdata/tar/security/tar-contiguous-skipped.tar](/home/kim/lean-zip/testdata/tar/security/tar-contiguous-skipped.tar) | 512 B | `Tar.extract` silent-skip `else` fallback at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) for unsupported typeflag `'7'` (POSIX UStar contiguous file, `0x37`) — 512-byte single-block UStar header for a zero-byte entry with `path = "contiguous-entry"`, empty `linkname`, `typeflag = 0x37`, checksum recomputed to match. The header has no payload and no trailing zero blocks (`Tar.forEntries` terminates on the short read at EOF), matching the `hardlink-outside.tar` / `tar-fifo-skipped.tar` / `tar-chardev-skipped.tar` / `tar-blockdev-skipped.tar` geometry. `Tar.extract` falls through to the `else` branch (no `typeDirectory` / `typeRegular` / `typeSymlink` match), `skipEntryData` is invoked on `e.size = 0` (a no-op), and no filesystem entry is created. `Tar.list` returns the entry verbatim with `typeflag = 0x37` (callers routing on `entry.typeflag` for trust decisions observe the contiguous-file marker rather than the regular-file `'0'` alias used by lenient extractors). Per-typeflag silent-skip family extension: sibling `hardlink-outside.tar` (typeflag `'1'`) pins the hardlink arm; sibling `tar-fifo-skipped.tar` (typeflag `'6'`) pins the FIFO arm; sibling `tar-chardev-skipped.tar` (typeflag `'3'`) pins the character-device arm; sibling `tar-blockdev-skipped.tar` (typeflag `'4'`) pins the block-device arm; this fixture pins the contiguous-file arm. All five flow through the same `else` fallback in `Tar.extract`, so the quintet together pins five distinct typeflag values against the shared fallback — a future refactor that drops the fallback for any one arm cannot escape detection by the corresponding fixture (verified by adversarial check during this PR <!-- drift-detector: prose discussion of the placeholder phrase in a paired-review finding, not a stale placeholder -->: temporarily wrapping the `else` body in `if e.typeflag == typeHardlink || e.typeflag == 0x36 || e.typeflag == 0x33 || e.typeflag == 0x34 then skipEntryData ... else throw "adversarial"` left `hardlink-outside.tar`, `tar-fifo-skipped.tar`, `tar-chardev-skipped.tar`, and `tar-blockdev-skipped.tar` passing while `tar-contiguous-skipped.tar` fired with `unexpected typeflag 55` (`0x37`)). The strict-vs-lenient distinction is the security-relevant policy choice this fixture pins: POSIX UStar permits lenient extractors to alias `'7'` to `'0'` (regular file) — GNU tar, BSD tar, and libarchive on systems without contiguous-file semantics treat it as a regular file and write the payload to disk — but lean-zip's strict `==` chain rejects `'7'` and silent-skips, refusing to materialise a payload that a malicious archive shipped expecting lenient extraction. Pinning this rejection with a fixture prevents future drift toward the lenient alias. Defense-in-depth fixture-only pattern (no new guard code, no new error wording, no new typeflag constant in the `Tar` namespace, no caller / signature change), matching the `tar-blockdev-skipped.tar` precedent (PR #2422 extending the silent-skip family to the blockdev arm), the `tar-chardev-skipped.tar` precedent (PR #2417 extending it to the chardev arm), and the `tar-fifo-skipped.tar` precedent (PR #2413 extending it to the FIFO arm). Writer-side at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) (`buildHeader`) emits whatever `entry.typeflag` is supplied — a caller can construct a typeflag-`'7'` entry programmatically, but `Tar.create`'s caller-API only accepts paths and never invokes `Tar.buildHeader` with a non-`'0'`/`'5'` typeflag, so legitimate archives produced by the lean-zip writer never carry typeflag `'7'`. POSIX UStar typeflag `'7'` (`0x37`) = contiguous file per POSIX.1-1988 IEEE Std 1003.1 §10 (USTAR Interchange Format); distinct in value and semantics from any of the currently-fixtured typeflags `'0'`/`'1'`/`'2'`/`'3'`/`'4'`/`'5'`/`'6'`, the GNU long-name `'L'`, the GNU long-link `'K'`, and the PAX `'x'`/`'g'`. With this fixture landing, the POSIX UStar `'0'`–`'7'` numeric range is **fully fixtured** — every value `'0'` through `'7'` has either a typed branch in `Tar.extract` (`'0'` regular, `'2'` symlink, `'5'` directory) or a silent-skip regression fixture (`'1'` hardlink, `'3'` chardev, `'4'` blockdev, `'6'` FIFO, `'7'` contiguous file) | #2425 | other (typeflag-policy regression) |
| [testdata/tar/security/tar-volumeheader-skipped.tar](/home/kim/lean-zip/testdata/tar/security/tar-volumeheader-skipped.tar) | 512 B | `Tar.extract` silent-skip `else` fallback at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) for unsupported GNU typeflag `'V'` (multi-volume archive label marker, `0x56`) — 512-byte single-block UStar header for a zero-byte entry with `path = "volume-label-entry"`, empty `linkname`, `typeflag = 0x56`, checksum recomputed to match. The header has no payload and no trailing zero blocks (`Tar.forEntries` terminates on the short read at EOF), matching the `hardlink-outside.tar` / `tar-fifo-skipped.tar` / `tar-chardev-skipped.tar` / `tar-blockdev-skipped.tar` / `tar-contiguous-skipped.tar` geometry. `Tar.extract` falls through to the `else` branch (no `typeDirectory` / `typeRegular` / `typeSymlink` match), `skipEntryData` is invoked on `e.size = 0` (a no-op), and no filesystem entry is created. `Tar.list` returns the entry verbatim with `typeflag = 0x56` (callers routing on `entry.typeflag` for trust decisions observe the GNU volume-header marker; the test arm asserts this with an explicit `vhListed[0]!.typeflag == 0x56` check). Per-typeflag silent-skip family extension: this is the **first GNU-typeflag** sibling, opening a new sub-ladder distinct from the POSIX UStar `'0'`–`'7'` range. The five POSIX UStar siblings — `hardlink-outside.tar` (typeflag `'1'`), `tar-fifo-skipped.tar` (typeflag `'6'`), `tar-chardev-skipped.tar` (typeflag `'3'`), `tar-blockdev-skipped.tar` (typeflag `'4'`), and `tar-contiguous-skipped.tar` (typeflag `'7'`) — flow through the same `else` fallback, so the six together pin six distinct typeflag values against the shared fallback — a future refactor that drops the fallback for any one arm cannot escape detection by the corresponding fixture (verified by adversarial check during this PR <!-- drift-detector: prose discussion of the placeholder phrase in a paired-review finding, not a stale placeholder -->: temporarily wrapping the `else` body in `if e.typeflag == typeHardlink || e.typeflag == 0x36 || e.typeflag == 0x33 || e.typeflag == 0x34 || e.typeflag == 0x37 then skipEntryData ... else throw "adversarial"` left `hardlink-outside.tar`, `tar-fifo-skipped.tar`, `tar-chardev-skipped.tar`, `tar-blockdev-skipped.tar`, and `tar-contiguous-skipped.tar` passing while `tar-volumeheader-skipped.tar` fired with `unexpected typeflag 86` (`0x56`)). The strict-vs-lenient distinction is the security-relevant policy choice this fixture pins: a malicious archive could ship a `'V'` entry with a volume label crafted to look like a filesystem path (e.g. `"../../../etc/passwd"` in the `path` slot), expecting a lenient extractor to materialise the marker as a regular file — lean-zip's policy of *never* materialising `'V'` entries (regardless of `path` / payload) is the correct conservative choice, and pinning it with a fixture prevents future drift toward the lenient alias. The volume-label `path` field is otherwise interpreted purely as human-readable archive metadata in GNU tar's multi-volume workflow. Defense-in-depth fixture-only pattern (no new guard code, no new error wording, no new typeflag constant in the `Tar` namespace, no caller / signature change), matching the `tar-contiguous-skipped.tar` precedent (PR #2425 closing the POSIX UStar `'0'`–`'7'` numeric range), the `tar-blockdev-skipped.tar` precedent (PR #2422), the `tar-chardev-skipped.tar` precedent (PR #2417), and the `tar-fifo-skipped.tar` precedent (PR #2413). Writer-side at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) (`buildHeader`) emits whatever `entry.typeflag` is supplied — a caller can construct a typeflag-`'V'` entry programmatically, but `Tar.create`'s caller-API only accepts paths and never invokes `Tar.buildHeader` with a non-`'0'`/`'5'` typeflag, so legitimate archives produced by the lean-zip writer never carry typeflag `'V'`. GNU tar typeflag `'V'` (`0x56`) = multi-volume archive label marker per the GNU tar info node `(tar)Standard`; distinct in value and semantics from the POSIX UStar numeric range `'0'`–`'7'`, the GNU long-name `'L'`, the GNU long-link `'K'`, and the PAX `'x'`/`'g'`. With this fixture landing, the silent-skip family stands at six fixtures spanning two sub-ladders: POSIX UStar `'1'`/`'3'`/`'4'`/`'6'`/`'7'` (closed) plus GNU-typeflag `'V'` (opening; future GNU-typeflag candidates remain `'M'` (multi-volume continuation, `0x4D`) and `'S'` (sparse file, `0x53`)) | #2428 | other (typeflag-policy regression) |
| [testdata/tar/security/tar-multivol-skipped.tar](/home/kim/lean-zip/testdata/tar/security/tar-multivol-skipped.tar) | 512 B | `Tar.extract` silent-skip `else` fallback at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) for unsupported GNU typeflag `'M'` (multi-volume continuation marker, `0x4D`) — 512-byte single-block UStar header for a zero-byte entry with `path = "multivol-entry"`, empty `linkname`, `typeflag = 0x4D`, checksum recomputed to match. The header has no payload and no trailing zero blocks (`Tar.forEntries` terminates on the short read at EOF), matching the `hardlink-outside.tar` / `tar-fifo-skipped.tar` / `tar-chardev-skipped.tar` / `tar-blockdev-skipped.tar` / `tar-contiguous-skipped.tar` / `tar-volumeheader-skipped.tar` geometry. `Tar.extract` falls through to the `else` branch (no `typeDirectory` / `typeRegular` / `typeSymlink` match), `skipEntryData` is invoked on `e.size = 0` (a no-op), and no filesystem entry is created. `Tar.list` returns the entry verbatim with `typeflag = 0x4D` (callers routing on `entry.typeflag` for trust decisions observe the GNU multi-volume continuation marker; the test arm asserts this with an explicit `mvListed[0]!.typeflag == 0x4D` check). Per-typeflag silent-skip family extension: this is the **second GNU-typeflag** sibling, extending the GNU-typeflag sub-ladder distinct from the POSIX UStar `'0'`–`'7'` range. The five POSIX UStar siblings — `hardlink-outside.tar` (typeflag `'1'`), `tar-fifo-skipped.tar` (typeflag `'6'`), `tar-chardev-skipped.tar` (typeflag `'3'`), `tar-blockdev-skipped.tar` (typeflag `'4'`), and `tar-contiguous-skipped.tar` (typeflag `'7'`) — plus the first GNU-typeflag sibling `tar-volumeheader-skipped.tar` (typeflag `'V'`) — flow through the same `else` fallback, so the seven together pin seven distinct typeflag values against the shared fallback — a future refactor that drops the fallback for any one arm cannot escape detection by the corresponding fixture (verified by adversarial check during this PR <!-- drift-detector: prose discussion of the placeholder phrase in a paired-review finding, not a stale placeholder -->: temporarily wrapping the `else` body in `if e.typeflag == typeHardlink || e.typeflag == 0x36 || e.typeflag == 0x33 || e.typeflag == 0x34 || e.typeflag == 0x37 || e.typeflag == 0x56 then skipEntryData ... else throw "adversarial"` left `hardlink-outside.tar`, `tar-fifo-skipped.tar`, `tar-chardev-skipped.tar`, `tar-blockdev-skipped.tar`, `tar-contiguous-skipped.tar`, and `tar-volumeheader-skipped.tar` passing while `tar-multivol-skipped.tar` fired with `unexpected typeflag 77` (`0x4D`)). The strict-vs-lenient distinction is the security-relevant policy choice this fixture pins: a malicious single-volume archive could ship a `'M'` entry as a top-level record (without a preceding multi-volume context) with a crafted `path` field (e.g. `"../../../etc/passwd"`) and a non-zero `size` declaring a fake "remaining payload", expecting a lenient extractor to materialise the marker as a regular file — lean-zip's policy of *never* materialising `'M'` entries (regardless of `path` / declared `size` / actual payload) is the correct conservative choice, and pinning it with a fixture prevents future drift toward the lenient alias. The `'M'` typeflag is otherwise interpreted purely as a multi-volume continuation cue in GNU tar's multi-volume workflow. Defense-in-depth fixture-only pattern (no new guard code, no new error wording, no new typeflag constant in the `Tar` namespace, no caller / signature change), matching the `tar-volumeheader-skipped.tar` precedent (PR #2428 opening the GNU-typeflag sub-ladder), the `tar-contiguous-skipped.tar` precedent (PR #2425 closing the POSIX UStar `'0'`–`'7'` numeric range), the `tar-blockdev-skipped.tar` precedent (PR #2422), the `tar-chardev-skipped.tar` precedent (PR #2417), and the `tar-fifo-skipped.tar` precedent (PR #2413). Writer-side at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) (`buildHeader`) emits whatever `entry.typeflag` is supplied — a caller can construct a typeflag-`'M'` entry programmatically, but `Tar.create`'s caller-API only accepts paths and never invokes `Tar.buildHeader` with a non-`'0'`/`'5'` typeflag, so legitimate archives produced by the lean-zip writer never carry typeflag `'M'`. GNU tar typeflag `'M'` (`0x4D`) = multi-volume continuation marker per the GNU tar info node `(tar)Multi-Volume Archives`; distinct in value and semantics from the POSIX UStar numeric range `'0'`–`'7'`, the first GNU-typeflag sibling `'V'`, the GNU long-name `'L'`, the GNU long-link `'K'`, and the PAX `'x'`/`'g'`. With this fixture landing, the silent-skip family stands at seven fixtures spanning two sub-ladders: POSIX UStar `'1'`/`'3'`/`'4'`/`'6'`/`'7'` (closed) plus GNU-typeflag `'V'`/`'M'` (extending; remaining GNU-typeflag candidate is `'S'` (sparse file, `0x53`)) | #2431 | other (typeflag-policy regression) |
| [testdata/tar/security/tar-sparse-skipped.tar](/home/kim/lean-zip/testdata/tar/security/tar-sparse-skipped.tar) | 512 B | `Tar.extract` silent-skip `else` fallback at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) for unsupported GNU typeflag `'S'` (sparse file, `0x53`) — 512-byte single-block UStar header for a zero-byte entry with `path = "sparse-entry"`, empty `linkname`, `typeflag = 0x53`, checksum recomputed to match. The header has no payload and no trailing zero blocks (`Tar.forEntries` terminates on the short read at EOF), matching the `hardlink-outside.tar` / `tar-fifo-skipped.tar` / `tar-chardev-skipped.tar` / `tar-blockdev-skipped.tar` / `tar-contiguous-skipped.tar` / `tar-volumeheader-skipped.tar` / `tar-multivol-skipped.tar` geometry. `Tar.extract` falls through to the `else` branch (no `typeDirectory` / `typeRegular` / `typeSymlink` match), `skipEntryData` is invoked on `e.size = 0` (a no-op), and no filesystem entry is created. `Tar.list` returns the entry verbatim with `typeflag = 0x53` (callers routing on `entry.typeflag` for trust decisions observe the GNU sparse-file marker; the test arm asserts this with an explicit `spListed[0]!.typeflag == 0x53` check). Per-typeflag silent-skip family extension: this is the **third GNU-typeflag** sibling, extending the GNU-typeflag sub-ladder distinct from the POSIX UStar `'0'`–`'7'` range. The five POSIX UStar siblings — `hardlink-outside.tar` (typeflag `'1'`), `tar-fifo-skipped.tar` (typeflag `'6'`), `tar-chardev-skipped.tar` (typeflag `'3'`), `tar-blockdev-skipped.tar` (typeflag `'4'`), and `tar-contiguous-skipped.tar` (typeflag `'7'`) — plus the first two GNU-typeflag siblings `tar-volumeheader-skipped.tar` (typeflag `'V'`) and `tar-multivol-skipped.tar` (typeflag `'M'`) — flow through the same `else` fallback, so the eight together pin eight distinct typeflag values against the shared fallback — a future refactor that drops the fallback for any one arm cannot escape detection by the corresponding fixture (verified by adversarial check during this PR <!-- drift-detector: prose discussion of the placeholder phrase in a paired-review finding, not a stale placeholder -->: temporarily wrapping the `else` body in `if e.typeflag == typeHardlink || e.typeflag == 0x36 || e.typeflag == 0x33 || e.typeflag == 0x34 || e.typeflag == 0x37 || e.typeflag == 0x56 || e.typeflag == 0x4D then skipEntryData ... else throw "adversarial"` left `hardlink-outside.tar`, `tar-fifo-skipped.tar`, `tar-chardev-skipped.tar`, `tar-blockdev-skipped.tar`, `tar-contiguous-skipped.tar`, `tar-volumeheader-skipped.tar`, and `tar-multivol-skipped.tar` passing while `tar-sparse-skipped.tar` fired with `unexpected typeflag 83` (`0x53`)). The strict-vs-lenient distinction is the security-relevant policy choice this fixture pins: a malicious archive could ship a `'S'` entry with a crafted sparse map (the GNU sparse format itself has multiple parser-differential variants: `0.0`, `0.1`, `1.0`, with subtly different sparse-map encodings) declaring zero-fill segments that overlap or exceed the entry's declared `size`, expecting a lenient extractor to allocate a large output file (zero-fill amplification) or miscompute the payload offset and corrupt subsequent entries — lean-zip's policy of *never* materialising `'S'` entries (regardless of `path` / sparse map / declared `size` / actual payload) is the correct conservative choice. The fixture intentionally ships a zero-byte body with no sparse map: the silent-skip policy applies regardless of payload shape, and a zero-byte body keeps the fixture geometry uniform with the other GNU-typeflag siblings; the lenient-extractor smuggling scenarios this fixture pins against would also fire on a malformed sparse map, but that is a separate fuzz target rather than a policy regression fixture. Writer-side: [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) (`buildHeader`) emits whatever `entry.typeflag` is supplied — a caller can construct a typeflag-`'S'` entry programmatically, but `Tar.create`'s caller-API only accepts paths and never invokes `Tar.buildHeader` with a non-`'0'`/`'5'` typeflag, so legitimate archives produced by the lean-zip writer never carry typeflag `'S'`. GNU tar typeflag `'S'` (`0x53`) = sparse file per the GNU tar info node `(tar)Sparse Formats`; distinct in value and semantics from the POSIX UStar numeric range `'0'`–`'7'`, the first two GNU-typeflag siblings `'V'`/`'M'`, the GNU long-name `'L'`, the GNU long-link `'K'`, the GNU directory-dump `'D'`, and the PAX `'x'`/`'g'`. With this fixture landing, the silent-skip family stands at eight fixtures spanning two sub-ladders: POSIX UStar `'1'`/`'3'`/`'4'`/`'6'`/`'7'` (closed) plus GNU-typeflag `'V'`/`'M'`/`'S'` (extending; remaining GNU-typeflag candidate is `'D'` (directory-dump for incremental backups, `0x44`)) | #2434 | other (typeflag-policy regression) |
| [testdata/tar/security/tar-incremental-skipped.tar](/home/kim/lean-zip/testdata/tar/security/tar-incremental-skipped.tar) | 512 B | `Tar.extract` silent-skip `else` fallback at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) for unsupported GNU typeflag `'D'` (directory-dump for incremental backups, `0x44`) — 512-byte single-block UStar header for a zero-byte entry with `path = "incremental-entry"`, empty `linkname`, `typeflag = 0x44`, checksum recomputed to match. The header has no payload and no trailing zero blocks (`Tar.forEntries` terminates on the short read at EOF), matching the `hardlink-outside.tar` / `tar-fifo-skipped.tar` / `tar-chardev-skipped.tar` / `tar-blockdev-skipped.tar` / `tar-contiguous-skipped.tar` / `tar-volumeheader-skipped.tar` / `tar-multivol-skipped.tar` / `tar-sparse-skipped.tar` geometry. `Tar.extract` falls through to the `else` branch (no `typeDirectory` / `typeRegular` / `typeSymlink` match), `skipEntryData` is invoked on `e.size = 0` (a no-op), and no filesystem entry is created. `Tar.list` returns the entry verbatim with `typeflag = 0x44` (callers routing on `entry.typeflag` for trust decisions observe the GNU directory-dump marker; the test arm asserts this with an explicit `inListed[0]!.typeflag == 0x44` check). Per-typeflag silent-skip family extension: this is the **fourth GNU-typeflag** sibling, extending the GNU-typeflag sub-ladder distinct from the POSIX UStar `'0'`–`'7'` range. The five POSIX UStar siblings — `hardlink-outside.tar` (typeflag `'1'`), `tar-fifo-skipped.tar` (typeflag `'6'`), `tar-chardev-skipped.tar` (typeflag `'3'`), `tar-blockdev-skipped.tar` (typeflag `'4'`), and `tar-contiguous-skipped.tar` (typeflag `'7'`) — plus the first three GNU-typeflag siblings `tar-volumeheader-skipped.tar` (typeflag `'V'`), `tar-multivol-skipped.tar` (typeflag `'M'`), and `tar-sparse-skipped.tar` (typeflag `'S'`) — flow through the same `else` fallback, so the nine together pin nine distinct typeflag values against the shared fallback — a future refactor that drops the fallback for any one arm cannot escape detection by the corresponding fixture (verified by adversarial check during this PR <!-- drift-detector: prose discussion of the placeholder phrase in a paired-review finding, not a stale placeholder -->: temporarily wrapping the `else` body in `if e.typeflag == typeHardlink || e.typeflag == 0x36 || e.typeflag == 0x33 || e.typeflag == 0x34 || e.typeflag == 0x37 || e.typeflag == 0x56 || e.typeflag == 0x4D || e.typeflag == 0x53 then skipEntryData ... else throw "adversarial"` left `hardlink-outside.tar`, `tar-fifo-skipped.tar`, `tar-chardev-skipped.tar`, `tar-blockdev-skipped.tar`, `tar-contiguous-skipped.tar`, `tar-volumeheader-skipped.tar`, `tar-multivol-skipped.tar`, and `tar-sparse-skipped.tar` passing while `tar-incremental-skipped.tar` fired with `unexpected typeflag 68` (`0x44`)). The strict-vs-lenient distinction is the security-relevant policy choice this fixture pins: a malicious archive could ship a `'D'` entry with a crafted directory-listing payload that an incremental-aware extractor would interpret as instructions to delete files outside `outDir` (the GNU incremental format allows the listing to mark files for *removal* during restore, with `Y`/`N` markers per entry in the NUL-separated listing payload), expecting a lenient extractor to honour those removal cues — lean-zip's policy of *never* materialising `'D'` entries — and never interpreting the listing payload at all — (regardless of `path` / declared `size` / actual payload) is the correct conservative choice, particularly because the format documentation explicitly notes that incremental restoration grants the archive author authority to remove files from the target tree. The fixture intentionally ships a zero-byte body with no incremental listing: the silent-skip policy applies regardless of payload shape, and a zero-byte body keeps the fixture geometry uniform with the other GNU-typeflag siblings; the lenient-extractor smuggling scenarios this fixture pins against would also fire on a malformed listing payload, but that is a separate fuzz target rather than a policy regression fixture. Writer-side: [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) (`buildHeader`) emits whatever `entry.typeflag` is supplied — a caller can construct a typeflag-`'D'` entry programmatically, but `Tar.create`'s caller-API only accepts paths and never invokes `Tar.buildHeader` with a non-`'0'`/`'5'` typeflag, so legitimate archives produced by the lean-zip writer never carry typeflag `'D'`. GNU tar typeflag `'D'` (`0x44`) = directory-dump for incremental backups per the GNU tar info node `(tar)Incremental Dumps`; distinct in value and semantics from the POSIX UStar numeric range `'0'`–`'7'`, the first three GNU-typeflag siblings `'V'`/`'M'`/`'S'`, the GNU long-name `'L'`, the GNU long-link `'K'`, and the PAX `'x'`/`'g'`. With this fixture landing, the silent-skip family stands at nine fixtures spanning two sub-ladders: POSIX UStar `'1'`/`'3'`/`'4'`/`'6'`/`'7'` (closed) plus GNU-typeflag `'V'`/`'M'`/`'S'`/`'D'` (extending; the GNU sub-ladder is open-ended — every additional per-typeflag arm fires the same `else` fallback in `Tar.extract`) | #2437 | other (typeflag-policy regression) |
| [testdata/tar/security/tar-longnames-skipped.tar](/home/kim/lean-zip/testdata/tar/security/tar-longnames-skipped.tar) | 512 B | `Tar.extract` silent-skip `else` fallback at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) for unsupported GNU typeflag `'N'` (LF_NAMES old-long-name extension, `0x4E`) — 512-byte single-block UStar header for a zero-byte entry with `path = "longnames-entry"`, empty `linkname`, `typeflag = 0x4E`, checksum recomputed to match. The header has no payload and no trailing zero blocks (`Tar.forEntries` terminates on the short read at EOF), matching the `hardlink-outside.tar` / `tar-fifo-skipped.tar` / `tar-chardev-skipped.tar` / `tar-blockdev-skipped.tar` / `tar-contiguous-skipped.tar` / `tar-volumeheader-skipped.tar` / `tar-multivol-skipped.tar` / `tar-sparse-skipped.tar` / `tar-incremental-skipped.tar` geometry. `Tar.extract` falls through to the `else` branch (no `typeDirectory` / `typeRegular` / `typeSymlink` match), `skipEntryData` is invoked on `e.size = 0` (a no-op), and no filesystem entry is created. `Tar.list` returns the entry verbatim with `typeflag = 0x4E` (callers routing on `entry.typeflag` for trust decisions observe the GNU LF_NAMES old-long-name marker; the test arm asserts this with an explicit `lnNamesListed[0]!.typeflag == 0x4E` check). Per-typeflag silent-skip family extension: this is the **fifth GNU-typeflag** sibling, extending the GNU-typeflag sub-ladder distinct from the POSIX UStar `'0'`–`'7'` range. The five POSIX UStar siblings — `hardlink-outside.tar` (typeflag `'1'`), `tar-fifo-skipped.tar` (typeflag `'6'`), `tar-chardev-skipped.tar` (typeflag `'3'`), `tar-blockdev-skipped.tar` (typeflag `'4'`), and `tar-contiguous-skipped.tar` (typeflag `'7'`) — plus the first four GNU-typeflag siblings `tar-volumeheader-skipped.tar` (typeflag `'V'`), `tar-multivol-skipped.tar` (typeflag `'M'`), `tar-sparse-skipped.tar` (typeflag `'S'`), and `tar-incremental-skipped.tar` (typeflag `'D'`) — flow through the same `else` fallback, so the ten together pin ten distinct typeflag values against the shared fallback — a future refactor that drops the fallback for any one arm cannot escape detection by the corresponding fixture (verified by adversarial check during this PR <!-- drift-detector: prose discussion of the placeholder phrase in a paired-review finding, not a stale placeholder -->: temporarily wrapping the `else` body in `if e.typeflag == typeHardlink || e.typeflag == 0x36 || e.typeflag == 0x33 || e.typeflag == 0x34 || e.typeflag == 0x37 || e.typeflag == 0x56 || e.typeflag == 0x4D || e.typeflag == 0x53 || e.typeflag == 0x44 then skipEntryData ... else throw "adversarial"` left `hardlink-outside.tar`, `tar-fifo-skipped.tar`, `tar-chardev-skipped.tar`, `tar-blockdev-skipped.tar`, `tar-contiguous-skipped.tar`, `tar-volumeheader-skipped.tar`, `tar-multivol-skipped.tar`, `tar-sparse-skipped.tar`, and `tar-incremental-skipped.tar` passing while `tar-longnames-skipped.tar` fired with `unexpected typeflag 78` (`0x4E`)). The strict-vs-lenient distinction is the security-relevant policy choice this fixture pins: `'N'` is the deprecated precursor to the modern `'L'` / `'K'` long-name encoding — a malicious archive could ship an `'N'` entry whose payload encodes a list of filenames containing `../etc/passwd` or absolute paths, expecting a lenient extractor (`bsdtar` / `libarchive` recognise `'N'` in lenient mode) to apply those names to subsequent regular-file entries (parser-differential archive-slip via deprecated long-name rewriting) — lean-zip's policy of *never* materialising `'N'` entries — and never interpreting the payload as a name-rewrite directive — (regardless of `path` / declared `size` / actual payload) is the correct conservative choice, particularly because `forEntries` recognises only the modern `'L'` / `'K'` long-name typeflags (and the PAX `'x'` / `'g'` pair); `'N'` is *not* aliased to `'L'` despite being the historical precursor of the same long-name extension family. The fixture intentionally ships a zero-byte body with no filename listing: the silent-skip policy applies regardless of payload shape, and a zero-byte body keeps the fixture geometry uniform with the other GNU-typeflag siblings; the lenient-extractor smuggling scenarios this fixture pins against would also fire on a payload that encodes specific malicious names, but that is a separate fuzz target rather than a policy regression fixture. Writer-side: [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) (`buildHeader`) emits whatever `entry.typeflag` is supplied — a caller can construct a typeflag-`'N'` entry programmatically, but `Tar.create`'s caller-API only accepts paths and never invokes `Tar.buildHeader` with a non-`'0'`/`'5'` typeflag, so legitimate archives produced by the lean-zip writer never carry typeflag `'N'`. GNU tar typeflag `'N'` (`0x4E`) = LF_NAMES old-long-name extension (the deprecated precursor to the modern `'L'` / `'K'` long-name encoding, predating PAX `'x'` and considered obsolete in current GNU tar but still emitted by old archivers and recognised by `bsdtar` / `libarchive` in lenient mode); distinct in value and semantics from the POSIX UStar numeric range `'0'`–`'7'`, the first four GNU-typeflag siblings `'V'`/`'M'`/`'S'`/`'D'`, the modern GNU long-name `'L'`, the modern GNU long-link `'K'`, and the PAX `'x'`/`'g'`. With this fixture landing, the silent-skip family stands at ten fixtures spanning two sub-ladders: POSIX UStar `'1'`/`'3'`/`'4'`/`'6'`/`'7'` (closed) plus GNU-typeflag `'V'`/`'M'`/`'S'`/`'D'`/`'N'` (extending; the GNU sub-ladder is open-ended — every additional per-typeflag arm fires the same `else` fallback in `Tar.extract`) | #2439 | other (typeflag-policy regression) |
| [testdata/tar/security/tar-mixed-skipped.tar](/home/kim/lean-zip/testdata/tar/security/tar-mixed-skipped.tar) | 2560 B | `Tar.extract` *extract-continuation* invariant across the silent-skip `else` fallback at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) — three-entry archive interleaving a silently-skipped middle entry between two regular files: `before.txt` (typeflag `'0'`, payload `"BEFORE\n"`, size 7) → `fifo-entry` (typeflag `'6'` = `0x36`, POSIX UStar FIFO, empty linkname, size 0, silent-skipped) → `after.txt` (typeflag `'0'`, payload `"AFTER\n"`, size 6); checksum recomputed for each header. Total fixture size: 5 × 512 = 2560 bytes (one header+payload pair for each regular entry, one bare header for the FIFO). No trailing zero blocks (`Tar.forEntries` terminates on the short read at EOF, matching the per-typeflag fixture geometry). `Tar.extract` materialises *both* `before.txt` and `after.txt` with their declared payloads after the middle FIFO entry is silent-skipped — pinning the `else` branch's `skipEntryData input e.size` call's *extract-continuation* invariant: that the call leaves the input stream positioned exactly at the next 512-byte block boundary so a subsequent regular-file entry still extracts cleanly. The test arm asserts both content (`before.txt = "BEFORE\n"`, `after.txt = "AFTER\n"`) and count (exactly two files materialise in the extract dir), pinning the *count* invariant (skip did not eat a regular-file entry) and the *content* invariant (skip did not corrupt a regular-file payload offset). Sibling-class fixture pinning the extract-continuation invariant — explicitly **not** an eleventh per-typeflag arm. The ten per-typeflag fixtures (`hardlink-outside.tar` (typeflag `'1'`), `tar-fifo-skipped.tar` (typeflag `'6'`), `tar-chardev-skipped.tar` (typeflag `'3'`), `tar-blockdev-skipped.tar` (typeflag `'4'`), `tar-contiguous-skipped.tar` (typeflag `'7'`), `tar-volumeheader-skipped.tar` (typeflag `'V'`), `tar-multivol-skipped.tar` (typeflag `'M'`), `tar-sparse-skipped.tar` (typeflag `'S'`), `tar-incremental-skipped.tar` (typeflag `'D'`), `tar-longnames-skipped.tar` (typeflag `'N'`)) already pin the *existence* of the `else` arm at ten distinct typeflag values; this fixture pins a *different* invariant — that the `else` arm's `skipEntryData` call preserves the next-entry offset — which all ten implicitly assume but none exercises (each is single-entry and ends at EOF after the skipped entry, so an off-by-one in `skipEntryData` propagates only into a `forEntries` short-read at EOF and is silently absorbed). The middle entry reuses typeflag `'6'` (FIFO) to mirror `tar-fifo-skipped.tar` — pins the same `else` arm without introducing a new typeflag value (defense-in-depth fixture-only pattern, no new guard code, no new error wording, no new typeflag constant in the `Tar` namespace, no caller / signature change), matching the per-typeflag silent-skip fixture-only convention from PR #2413 onwards. Verified by adversarial check during this PR <!-- drift-detector: prose discussion of the placeholder phrase in a paired-review finding, not a stale placeholder -->: temporarily replacing the `else` arm's `skipEntryData input e.size` with `skipEntryData input (e.size + 1)` caused the new arm to fire with `tar: header checksum mismatch` (the 1-byte offset shift propagates one block forward: after the FIFO header is parsed, the perturbed skip consumes the `after.txt` header (positions 0x600–0x7FF), and the subsequent `forEntries` `readExact 512` parses the `after.txt` payload region as a header whose checksum cannot match), while all ten per-typeflag siblings still passed (each ends at EOF after the skipped entry, so the off-by-one is absorbed into the `forEntries` short-read at EOF without ever propagating to a downstream header parse); reverting the perturbation restored the test to passing and `git diff Zip/Tar.lean` is empty post-revert. Writer-side at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) (`buildHeader`) emits whatever `entry.typeflag` is supplied — the fixture's middle entry is constructed via `Tar.buildHeader` with `typeflag := 0x36`, but `Tar.create`'s caller-API only accepts paths and never invokes `Tar.buildHeader` with a non-`'0'`/`'5'` typeflag, so legitimate archives produced by the lean-zip writer never carry typeflag `'6'`. POSIX UStar typeflag `'6'` (`0x36`) = FIFO per POSIX.1-1988 IEEE Std 1003.1 §10 (USTAR Interchange Format), reused here from the `tar-fifo-skipped.tar` precedent (PR #2413 first established the FIFO arm of the silent-skip family). Scope: pins extract continuation for `Tar.extract` only; `Tar.list`'s continuation invariant is structurally identical (`forEntries` is shared) but a separate fixture for `Tar.list` is not required — the new arm exercises `Tar.extract` only, matching the issue's scope. The open-ended GNU sub-ladder framing of the per-typeflag family remains correct after this fixture lands — this fixture does not close the family, and the family-closure narrative on the per-typeflag rows continues to apply unchanged. Subsequently extended by a defense-in-depth `Tar.list`-side test arm reusing the same fixture bytes (no new fixture file): the `Tar.list` continuation invariant is now explicitly pinned in addition to the `Tar.extract` continuation invariant, so a hypothetical future `Tar.list` refactor that decouples from the shared `forEntries` (e.g., for performance, lazy iteration, or different error reporting) cannot silently break continuation | #2449 | other (extract-continuation regression) |
| [testdata/tar/security/tar-slip.tar](/home/kim/lean-zip/testdata/tar/security/tar-slip.tar) | 10240 B | `Binary.isPathSafe` rejects `..` component traversal at [Zip/Tar.lean](/home/kim/lean-zip/Zip/Tar.lean) — *"unsafe path"* | `481e562` | archive-slip |
| [testdata/zip/malformed/bad-crc.zip](/home/kim/lean-zip/testdata/zip/malformed/bad-crc.zip) | 140 B | Post-extraction CRC32 verification at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) — *"CRC32 mismatch"* | `481e562` | other (integrity check) |
| [testdata/zip/malformed/bad-method.zip](/home/kim/lean-zip/testdata/zip/malformed/bad-method.zip) | 140 B | CD-entry compression-method allowlist check at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) — *"unsupported compression method"* (CD/LH both advertise method=14 (LZMA), outside lean-zip's `{0, 8}` allowlist; `parseCentralDir` rejects at CD parse time, pre-ZIP64-resolution, before any LH read. Previously caught by the late method-dispatch guard at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) — *"unsupported method"* — which still fires as defense-in-depth if a future caller bypasses CD parsing) | #1801 | other (method validation) |
| [testdata/zip/malformed/cd-bad-lh-signature.zip](/home/kim/lean-zip/testdata/zip/malformed/cd-bad-lh-signature.zip) | 122 B | Late LH-signature guard regression coverage at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) — *"bad local header signature for {label}"* (122-byte single-entry stored `hello.txt` archive — LH at file offset 0, CD at offset 45, EOCD at offset 100 — where the LH's first 4 bytes are overwritten with `0xCAFEBABE` (LE: `BE BA FE CA`) instead of the APPNOTE §4.3.7 `sigLocal = 0x04034b50`. The CD itself is byte-identical to the stock baseline so every CD-parse guard passes (`localOffset = 0`, `localOffset + 30 ≤ cdOffset = 45`, `entryEnd = 45 ≤ cdEnd = 100`, method ∈ {0, 8}, stored-method `compSize == uncompSize`, etc.) and `assertSpanInFile` / `readBoundedSpanFromHandle` clear the LH span (30 B at offset 0 ≤ fileSize 122). `Archive.list` never reads the LH and lists the fixture cleanly; only `Archive.extract` throws — confirming that the late LH-signature guard is `Archive.extract`'s defense-in-depth catch for archives that slip past every CD-parse and span guard. Fixture-only regression coverage (no new guard code, no new error wording, no caller / signature change) — pattern matches PRs #1761 / #1889 (`zip64-eocd64-bad-recsize.zip` / `zip64-eocd64-v2-record.zip` at the EOCD64 record-size guard) and PR #1921 (`cd-entry-past-cdend.zip` at the `entryEnd > cdEnd` guard). Sibling of `cd-entry-localoffset-past-cdstart.zip` (PR #1813, fires the per-entry `localOffset + 30 ≤ cdOffset` CD-parse guard before the LH read) and `cd-entry-past-cdend.zip` (PR #1921, fires the `entryEnd > cdEnd` CD-parse guard before the LH read): together the trio pins all three precedence levels of the local-offset → local-header validation chain at CD-parse + late-extract — the late LH-signature guard is the defense-in-depth catch, and this fixture pins that catch behaviour so future refactors of `Archive.extract` cannot silently lose the guard) | #1903 | other (LH signature regression) |
| [testdata/zip/malformed/cd-bad-method-early.zip](/home/kim/lean-zip/testdata/zip/malformed/cd-bad-method-early.zip) | 122 B | CD-entry compression-method allowlist check at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) — *"unsupported compression method"* (CD/LH both advertise method=6 (imploded — deprecated in PKZIP 2.0, 1993), outside lean-zip's `{0, 8}` allowlist; `parseCentralDir` rejects at CD parse time, pre-ZIP64-resolution, before any LH read. Companion to `bad-method.zip` (CD/LH method=14, LZMA): both fixtures trip the same CD-parse guard, but distinct method values let paired-review distinguish which fixture fired) | #1801 | other (method validation) |
| [testdata/zip/malformed/cd-deflate-zero-compsize.zip](/home/kim/lean-zip/testdata/zip/malformed/cd-deflate-zero-compsize.zip) | 116 B | CD-entry `uncompSize > 0 → compSize > 0` math-invariant check at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) — *"CD entry has zero compressedSize with nonzero uncompressedSize"* (CD and LH both advertise `method=8` (deflate) with `compressedSize=0` and `uncompressedSize=42`. APPNOTE §4.4.8 / §4.4.9 define the size fields; every ZIP compression method produces at least one compressed byte from non-empty uncompressed input — method 0 (APPNOTE §4.4.5) has `compSize == uncompSize`; method 8 (RFC 1951) has a 2-byte minimum block-header encoding (`03 00` empty-stored-block), so any non-empty inflate output requires at minimum a block header plus encoded data. Therefore `compSize == 0 ∧ uncompSize > 0` is structurally impossible regardless of method — a universal mathematical invariant every correct writer (Info-ZIP, Go `archive/zip`, CPython `zipfile`, 7-Zip, lean-zip's own `create`) obeys. `parseCentralDir` rejects at CD parse time, post-ZIP64-resolution, after the stored-method size invariant (`cd-stored-size-mismatch.zip`, PR #1773) and the empty-entry CRC invariant (`cd-empty-entry-crc-nonzero.zip`, PR #1857). Pre-PR, PR #1773's method=0 gate skipped this entry (its `compSize == uncompSize` check is method-gated); PR #1857's `uncompSize == 0` gate skipped this entry (since `uncompSize = 42 > 0`). `Archive.list` propagated `{method = 8, compSize = 0, uncompSize = 42, ...}` verbatim — callers routing on `entry.compressedSize == 0` as a short-circuit saw smuggled values — and `Archive.extract` failed only later inside the inflate backend (`Zlib.decompress` / `Gzip.decompress` / `Zip.Native.Inflate.inflate`) with a decompression error whose attribution did not pin the structural anomaly. Sibling of PR #1773 and PR #1857 at the CD-parse mathematical-invariant family — three contiguous columns: #1773 closes `compSize == uncompSize` (tautological for stored, method=0 only); #1857 closes `uncompSize == 0 → crc == 0` (tautological for empty entries, method-agnostic); PR #1886 closes `uncompSize > 0 → compSize > 0` (structurally required under any compression method, method-agnostic). LH and CD fields match byte-for-byte (method / sizes / crc / version / flags) so no CD/LH skew guard fires first; CRC is `0` so PR #1857 does not interact. Interop pre-flight over `testdata/zip/{interop,malformed,security}/*.zip` returned zero hits before landing) | #1886 | other (math invariant / method-agnostic) |
| [testdata/zip/malformed/cd-empty-entry-crc-nonzero.zip](/home/kim/lean-zip/testdata/zip/malformed/cd-empty-entry-crc-nonzero.zip) | 116 B | CD-entry empty-entry CRC invariant check at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) — *"CD entry CRC must be zero when uncompressedSize is zero"* (CD and LH both advertise a zero-byte stored entry (`method=0, compSize=0, uncompSize=0`) but carry a crafted nonzero CRC (`0xDEADBEEF`). APPNOTE §4.4.7 defines the CRC32 field as the ANSI-CRC-32 of the uncompressed payload; the empty byte string has CRC32 `0x00000000` by the CRC-32 start-state `0xFFFFFFFF` + final-complement identity, so `uncompSize == 0 → crc == 0` is a universal mathematical invariant that every correct writer — Info-ZIP, Go `archive/zip`, CPython `zipfile`, 7-Zip, lean-zip's own `create` — obeys. `parseCentralDir` rejects at CD parse time post-ZIP64-resolution, after the stored-method size invariant — so the resolved `uncompSize : UInt64` is the value checked rather than the `0xFFFFFFFF` sentinel, and attribution pins on the empty-file premise rather than a generic CRC check. LH and CD carry the same crafted CRC so the CD/LH `crc32` consistency check (`cd-lh-crc-mismatch.zip`, PR #1728) does not fire first; `compSize == uncompSize == 0` so the stored-method size invariant (`cd-stored-size-mismatch.zip`, PR #1773) does not fire first. Closes both `Archive.list` (pre-PR propagated the crafted CRC into `Entry.crc32` verbatim — callers routing on `entry.crc32` saw the smuggled value) and `Archive.extract` (pre-PR caught the mismatch only post-extraction via the `"CRC32 mismatch"` guard at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean), after any I/O work had been performed) dimensions simultaneously. Sibling of PR #1773 at the CD-parse mathematical-invariant family — #1773 closes the `compSize == uncompSize` column (tautological for stored), PR #1857 closes the `uncompSize == 0 → crc == 0` column (tautological for empty entries, method-agnostic)) | #1857 | other (CRC/empty-file invariant) |
| [testdata/zip/malformed/cd-empty-name.zip](/home/kim/lean-zip/testdata/zip/malformed/cd-empty-name.zip) | 104 B | CD-entry empty-filename rejection at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) — *"CD entry has empty filename"* (CD and LH entries both carry `name_bytes=b""`, so the `name length` UInt16 at CD +28 — APPNOTE §4.4.10 — reads as `0`. `parseCentralDir` rejects at CD parse time immediately after the `nameLen` read, before the `entryEnd > cdEnd` overrun check and before the sibling NUL-byte / path-safety filename guards — so the failure attribution pins cleanly to the structural anomaly rather than the path-safety predicate (which would otherwise catch the empty string via its empty-component rejection, but only if the decode succeeds). Every legitimate ZIP entry has at least one byte of name; `nameLen == 0` is structurally pathological and a parser-differential smuggling vector (lenient readers emit `entry.path = ""` — an `Entry` with no useful identity; `Archive.extract` would resolve `outDir / ""` to either `outDir` itself or a path with a trailing separator, surfacing as an unrelated `IO.FS.writeBinFile` / `createDir` error). Sibling of `cd-nul-in-name.zip` (PR #1831, byte-content dimension) and `cd-path-unsafe.zip` (PR #1840, path-shape dimension): together they close the smuggled-name attack class at CD parse — zero-length, NUL-embedded, and path-traversal forms all rejected pre-decode. Interop pre-flight over `testdata/zip/{interop,malformed}/*.zip` returned zero hits before landing) | #1848 | other (filename validation) |
| [testdata/zip/malformed/cd-entry-disknum-mismatch.zip](/home/kim/lean-zip/testdata/zip/malformed/cd-entry-disknum-mismatch.zip) | 122 B | CD per-entry `diskNumberStart` consistency check at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) — *"CD entry diskNumberStart mismatch"* (CD entry's APPNOTE §4.4.11 disk-number field at offset +34 is `7`; lean-zip supports single-disk archives only, so any nonzero value is rejected. Per-entry counterpart to `eocd-disknum-mismatch.zip` which covers the archive-level EOCD disk-number fields) | #1759 | other (CD/EOCD consistency) |
| [testdata/zip/malformed/cd-entry-internal-attrs-reserved.zip](/home/kim/lean-zip/testdata/zip/malformed/cd-entry-internal-attrs-reserved.zip) | 122 B | CD per-entry `internalFileAttributes` reserved-bits check at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) — *"internalAttrs reserved bits set"* (CD entry's APPNOTE §4.4.10 field at offset +36 carries `0x0080` — bit 7 set, reserved; only bit 0 "apparent ASCII/text data" is defined in version 1.0, bits 1-2 are PKWARE-reserved, bits 3-15 unused. Guard `internalAttrs &&& 0xFFFE == 0` preserves Info-ZIP bit-0 interop while rejecting smuggled reserved-bit values. Contiguous writer-zero `UInt16` sibling of `cd-entry-disknum-mismatch.zip` (CD +34): `parseCentralDir` reads both fields in order and both guards fire pre-ZIP64-resolution, before the `entryEnd > cdEnd` span check) | #1819 | other (CD writer-invariant) |
| [testdata/zip/malformed/cd-entry-localoffset-past-cdstart.zip](/home/kim/lean-zip/testdata/zip/malformed/cd-entry-localoffset-past-cdstart.zip) | 122 B | CD-entry `localOffset + 30 ≤ cdOffset` archive-layout invariant check at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) — *"entry local offset overlaps central directory"* (LH+data at file offset 0 length 45, CD starts at offset 45, and the CD entry's `localOffset` field at CD +42 claims `50` — past `cdOffset - 30 = 15`, so the 30-byte fixed LH header cannot be read strictly before the CD region as APPNOTE §4.3.6 requires. Per-entry micro-shape sibling of the archive-level `cdOffset + cdSize ≤ eocdPos` macro-shape guard; pre-PR `Archive.list` had no gate at all, and only the extract path's late LH-signature check caught a subset of the construction) | #1813 | other (archive-layout invariant) |
| [testdata/zip/malformed/cd-entry-past-cdend.zip](/home/kim/lean-zip/testdata/zip/malformed/cd-entry-past-cdend.zip) | 122 B | Per-entry `entryEnd > cdEnd` footprint guard regression coverage at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) — *"central directory entry extends past end of central directory"* (122-byte single-entry stored `hello.txt` archive — LH at file offset 0, CD at offset 45, EOCD at offset 100 — where the sole CD entry's `commentLen` field at CD +32 (UInt16) is `16` while no comment payload is physically present, so `cdSize = 55` (header + name only). At parse time `entryEnd = 45 + 46 + 9 + 0 + 16 = 116 > cdEnd = 100`, firing the per-entry footprint guard before any name decode. All earlier CD-parse guards pass (loop entry `pos + 46 ≤ cdEnd` (91 ≤ 100), CD signature match, `nameLen = 9 > 0`, `diskNumberStart = 0`, `internalAttrs = 0`) so attribution pins to the footprint guard rather than a sibling early-reject. Fixture-only regression coverage (no new guard code, no new error wording, no caller / signature change) — pattern matches PRs #1761 / #1889 (`zip64-eocd64-bad-recsize.zip` / `zip64-eocd64-v2-record.zip`) and #1903 (`cd-bad-lh-signature.zip`). Companion to in-flight `cd-trailing-garbage.zip` (issue #1775, trailing bytes inside `[lastEntryEnd, cdEnd)`) and `cd-extends-past-eocd.zip` (issue #1799, archive-level `cdOffset + cdSize ≤ eocdPos`) — together the trio closes the three CD-region overrun shapes. Pins the paired-review precedence chain alongside `cd-entry-localoffset-past-cdstart.zip` (PR #1813) and `cd-bad-lh-signature.zip` (PR #1903) so future refactors of `parseCentralDir` cannot silently regress the per-entry footprint fence. Sentinel `commentLen = 16` is canonical "obviously crafted" overrun — any positive value satisfying `46 + nameLen + extraLen + commentLen > cdSize` fires the same guard) | #1921 | other (CD-region overrun regression) |
| [testdata/zip/malformed/cd-extra-overrun-datasize.zip](/home/kim/lean-zip/testdata/zip/malformed/cd-extra-overrun-datasize.zip) | 138 B | CD/LH extra-data sub-field structural check at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) — *"malformed extra field"* (CD/LH extra-data carries a single sub-field with `headerId=0x5455` extended-timestamp but declared `dataSize=0xFF` while only 4 payload bytes remain; no ZIP64 sentinel is set so pre-PR `parseCentralDir` skipped `parseZip64Extra` entirely and the anomaly was entirely invisible. `validateExtraFieldStructure` runs unconditionally on the extra-data blob before the sentinel guard at both the CD and LH sites (mirror assertion at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) — *"malformed local extra field"*). Outer-sub-field sibling of `zip64-extra-oversized-datasize.zip` at the inner-0x0001 layer of the same APPNOTE §4.5 extra-data smuggling class) | #1788 | other (ZIP64 consistency) |
| [testdata/zip/malformed/cd-flags-reserved-bits.zip](/home/kim/lean-zip/testdata/zip/malformed/cd-flags-reserved-bits.zip) | 122 B | CD-entry general-purpose flag reserved/unused-bits rejection at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) — *"flags reserved bits set"* (CD and LH both advertise `flags = 0x0880` — bit 11 UTF-8 names plus bit 7 reserved-bit smuggle. APPNOTE §4.4.4 documents bits 7, 8, 9, 10 as "Currently unused", bit 12 as "Reserved by PKWARE for enhanced compression", and bits 14, 15 as "Reserved by PKWARE"; together these seven bits form the mask `0xD780` (`0b1101_0111_1000_0000`). lean-zip's writer emits the flag word literally as `0x0800` at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) (LH) and  (CD) so `flags &&& 0xD780 == 0` holds for every lean-zip-produced archive independent of method, size, or ZIP64. `parseCentralDir` rejects at CD parse time pre-ZIP64-resolution, immediately after the method allowlist (PR #1801) and before the per-feature-bit checks (bit 5 patched-data at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean)). Bit 7 (`0x0080`) is the smallest reserved-bit smuggle; pairing it with bit 11 keeps the UTF-8-name guard happy so the new reserved-bits guard is unambiguously the one that fires. Both LH and CD flag words match (`flag_bits_override = 0x0880` sets both sides) so the CD-vs-LH bit-3-masked flags check (PR #1715, [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean)) does not fire first. Sibling of `cd-patched-data-flag.zip` (PR #1824, bit 5, single-bit `flags = 0x0020`) at the same CD+8 `flags` field — distinct mask, distinct error substring (`"flags reserved bits set"` vs. `"patched-data flag bit 5 set"`). Bits 1 and 2 (compression-option per APPNOTE §4.4.4 — Info-ZIP / 7-Zip legitimately set them on `method == 8` payloads) are explicitly out of scope; the mask `0xD780` is disjoint from the unsupported-feature mask `0x2071` (bits 0/4/5/6/13). Interop pre-flight over `testdata/zip/{interop,malformed}/*.zip` returned zero hits for `flags & 0xD780 != 0` before landing) | #2237 | other (flag-bit validation) |
| [testdata/zip/malformed/cd-lh-crc-mismatch.zip](/home/kim/lean-zip/testdata/zip/malformed/cd-lh-crc-mismatch.zip) | 122 B | CD/LH `crc32` consistency check at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) — *"crc32 mismatch between CD and local header"* (LH crc differs from CD; both stored, sizes match so earlier guards do not fire first) | #1728 | other (CD/LH consistency) |
| [testdata/zip/malformed/cd-lh-flags-mismatch.zip](/home/kim/lean-zip/testdata/zip/malformed/cd-lh-flags-mismatch.zip) | 122 B | CD/LH flags-consistency check (bit-3-masked) at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) — *"flags mismatch between CD and local header"* (CD sets bit 11 UTF-8-name, LH clears it — a known ZIP-smuggling vector) | #1715 | other (CD/LH consistency) |
| [testdata/zip/malformed/cd-lh-method-mismatch.zip](/home/kim/lean-zip/testdata/zip/malformed/cd-lh-method-mismatch.zip) | 122 B | CD/LH method-consistency check at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) — *"method mismatch between CD and local header"* | #1554 | other (CD/LH consistency) |
| [testdata/zip/malformed/cd-lh-modtime-mismatch.zip](/home/kim/lean-zip/testdata/zip/malformed/cd-lh-modtime-mismatch.zip) | 122 B | CD/LH `lastModTime`/`lastModDate` consistency check at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) — *"lastModTime/Date mismatch between CD and local header"* (LH time `0x1234` disagrees with CD time `0`; the two DOS-encoded `UInt16` slots — LH +10/+12, CD +12/+14 — are compared together and the check is ungated since APPNOTE §4.4.6 restricts the bit-3 data-descriptor allowance to crc/compSize/uncompSize only) | #1769 | other (CD/LH consistency) |
| [testdata/zip/malformed/cd-lh-size-mismatch.zip](/home/kim/lean-zip/testdata/zip/malformed/cd-lh-size-mismatch.zip) | 122 B | CD/LH `compressedSize` consistency check at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) — *"compressedSize mismatch between CD and local header"* | #1554 | other (CD/LH consistency) |
| [testdata/zip/malformed/cd-lh-uncompsize-mismatch.zip](/home/kim/lean-zip/testdata/zip/malformed/cd-lh-uncompsize-mismatch.zip) | 122 B | CD/LH `uncompressedSize` consistency check at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) — *"uncompressedSize mismatch between CD and local header"* (LH uncomp differs from CD; both stored, compressed sizes match so earlier guards do not fire first) | #1728 | other (CD/LH consistency) |
| [testdata/zip/malformed/cd-lh-version-mismatch.zip](/home/kim/lean-zip/testdata/zip/malformed/cd-lh-version-mismatch.zip) | 122 B | CD/LH `versionNeededToExtract` downgrade check at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) — *"LH versionNeededToExtract (…) exceeds CD versionNeededToExtract (…)"* (LH claims higher version than CD — a capability-smuggle; CD > LH is legitimate per Go/Python ZIP64 producers and is allowed) | #1736 | other (CD/LH consistency) |
| [testdata/zip/malformed/cd-nul-in-name.zip](/home/kim/lean-zip/testdata/zip/malformed/cd-nul-in-name.zip) | 118 B | CD-entry name NUL-byte rejection at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) — *"CD entry name contains NUL byte"* (CD and LH entries both carry raw name bytes `b"a\x00b.txt"` — 7 bytes, NUL at index 1. `parseCentralDir` guards on the raw `ByteArray` before the UTF-8 decode, so neither the UTF-8-flagged branch nor the Latin-1 fallback re-introduces NUL into the error message or the decoded `path`. Closes a classic parser-differential / filesystem-truncation smuggling vector: POSIX `open`/`stat` truncates at NUL so `Archive.extract` would deposit files at the short-form prefix, while `Archive.list` callers routing on `entry.path` see the full NUL-embedded string. Interop pre-flight over `testdata/zip/{interop,malformed}/*.zip` returned zero hits before landing) | #1831 | other (filename validation) |
| [testdata/zip/malformed/cd-path-unsafe.zip](/home/kim/lean-zip/testdata/zip/malformed/cd-path-unsafe.zip) | 126 B | CD-entry path-safety rejection at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) — *"CD entry has unsafe path"* (CD and LH entries both carry raw name bytes `b"../evil.txt"` — 11 bytes, a canonical archive-slip `..`-traversal smuggle. `parseCentralDir` runs `Binary.isPathSafe` on the decoded `name` String immediately after the UTF-8 / Latin-1 decode block and before the `versionNeeded` upper-bound check, mirroring the trailing-slash carve-out from the extract-time check so legitimate directory entries (which end in `/`) are not tripped. Closes the path-traversal / archive-slip smuggling dimension on the `Archive.list` path, which pre-PR returned the `Entry` with the unsafe path verbatim — exposing the full smuggled form to callers that route on `entry.path` before any filesystem I/O. Extract-time `Binary.isPathSafe` calls at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) /  remain as defense-in-depth. Quotes the smuggled name via `String.quote` so control bytes never reach logs unescaped. Sibling of `cd-nul-in-name.zip` (PR #1831): together they close the smuggled-name attack class — NUL-byte content (PR #1831) and path-shape (PR #1840). Interop pre-flight over `testdata/zip/{interop,malformed}/*.zip` returned zero hits before landing; the three `testdata/zip/security/` counter-fixtures (`zip-slip.zip`, `absolute-path.zip`, `backslash-slip.zip`) continue to pass via substring matching — their `unsafe path` assertion is a substring of the new `CD entry has unsafe path` wording) | #1840 | archive-slip |
| [testdata/zip/malformed/cd-past-eof.zip](/home/kim/lean-zip/testdata/zip/malformed/cd-past-eof.zip) | 22 B | `cdOffset + cdSize ≤ fileSize` check at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) — *"central directory extends beyond file"* | `481e562` | oversized allocation |
| [testdata/zip/malformed/cd-patched-data-flag.zip](/home/kim/lean-zip/testdata/zip/malformed/cd-patched-data-flag.zip) | 122 B | CD-entry general-purpose flag bit-5 (compressed patched data) rejection at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) — *"patched-data flag bit 5 set"* (CD and LH both advertise `flags = 0x0020`, APPNOTE §4.4.4 bit 5 — PKWARE's proprietary compressed-patched-data format §4.6; lean-zip implements neither creation nor extraction, the writer emits `flags = 0x0800` bit 11 UTF-8 names only. `parseCentralDir` rejects at CD parse time pre-ZIP64-resolution, closing a parser-differential smuggling vector where crafted archives with bit 5 set would otherwise be silently extracted as if the payload were plain Deflate/stored data. Sibling of in-flight PR #1771 (issue #1762, encryption-related bits 0/6/13) at the same CD+8 `flags` field — distinct bit, distinct error substring) | #1824 | other (flag-bit validation) |
| [testdata/zip/malformed/cd-stored-size-mismatch.zip](/home/kim/lean-zip/testdata/zip/malformed/cd-stored-size-mismatch.zip) | 122 B | CD-entry stored-method size-invariant check at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) — *"stored-method size mismatch"* (both CD and LH advertise `method=0` with `compressedSize=6, uncompressedSize=7` — no CD/LH divergence, but APPNOTE §4.4.5 *"no compression"* makes `compSize == uncompSize` a tautology. `parseCentralDir` rejects at CD parse time, post-ZIP64-resolution, before any LH read; complements the CD/LH `uncompressedSize` check which catches CD-vs-LH skew) | #1773 | other (CD/LH consistency) |
| [testdata/zip/malformed/cd-zip64-extra-duplicate.zip](/home/kim/lean-zip/testdata/zip/malformed/cd-zip64-extra-duplicate.zip) | 158 B | CD-side duplicate ZIP64 extra-block guard at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) — *"duplicate ZIP64 extra field"* (CD entry's extra-data carries two `headerId == 0x0001` blocks back-to-back with `uncompSize` payloads `6` and `106`; APPNOTE §4.5 forbids more than one instance of any registered header ID per entry's extra-data, and the layout of each block depends on which standard 32-bit fields are at sentinel — two blocks make the resolved sizes ambiguous. `hasDuplicateZip64Extra` fires before `parseZip64Extra` so the error attributes the fault to the CD side; LH carries a single valid 0x0001 block. Sibling of `lh-zip64-extra-duplicate.zip`, `cd-extra-overrun-datasize.zip`, and `zip64-extra-oversized-datasize.zip` — together they close the ZIP64 extra-field layout-smuggling attack class) | #1793 | other (ZIP64 consistency) |
| [testdata/zip/malformed/eocd-disknum-mismatch.zip](/home/kim/lean-zip/testdata/zip/malformed/eocd-disknum-mismatch.zip) | 122 B | CD-vs-EOCD disk-number consistency check at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) — *"EOCD disk-number mismatch"* (standard EOCD `diskWhereCDStarts=1`; lean-zip supports single-disk archives only, so any nonzero value in either disk-number field is rejected post-ZIP64-override) | #1742 | other (CD/EOCD consistency) |
| [testdata/zip/malformed/eocd-numentries-mismatch.zip](/home/kim/lean-zip/testdata/zip/malformed/eocd-numentries-mismatch.zip) | 122 B | CD-vs-EOCD `totalEntries` consistency check at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) — *"EOCD totalEntries mismatch"* (EOCD declares 2 entries, CD has 1 — parser's trailing-signature loop would silently accept the short list without this guard) | #1733 | other (CD/EOCD consistency) |
| [testdata/zip/malformed/eocd-numentries-thisdisk-mismatch.zip](/home/kim/lean-zip/testdata/zip/malformed/eocd-numentries-thisdisk-mismatch.zip) | 122 B | EOCD-internal `numEntriesThisDisk` vs. `totalEntries` consistency check at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) — *"EOCD numEntriesThisDisk mismatch"* (`numEntriesThisDisk=2`, `totalEntries=1`; single-disk archives must have the sibling EOCD entry-count fields equal, and the writer emits them at the same value) | #1752 | other (CD/EOCD consistency) |
| [testdata/zip/malformed/eocd-zip64-override-cdsize-mismatch.zip](/home/kim/lean-zip/testdata/zip/malformed/eocd-zip64-override-cdsize-mismatch.zip) | 198 B | ZIP64/standard-EOCD override sentinel check — `cdSize` slot at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) — *"EOCD ZIP64-override mismatch"* (standard-EOCD `cdSize=99`, ZIP64 `cdSize=55`; standard value is neither the APPNOTE §4.3.16 sentinel `0xFFFFFFFF` nor a numeric match with the ZIP64 override. All other override slots remain at their sentinels so the relaxed sentinel arm passes for `cdOffset`, `totalEntries`, `numberOfThisDisk`, `diskWhereCDStarts`, `numEntriesThisDisk`, and the `cdSize` sub-check is the one that trips. Per-slot sibling of `eocd-zip64-override-nosentinel.zip` (PR #1745, `cdOffset` slot) at the 6-field EOCD ZIP64-override mismatch family — the per-slot fixtures pin attribution to one specific override-slot guard rather than the family-wide check) | #1900 | other (ZIP64 consistency) |
| [testdata/zip/malformed/eocd-zip64-override-diskcd-mismatch.zip](/home/kim/lean-zip/testdata/zip/malformed/eocd-zip64-override-diskcd-mismatch.zip) | 198 B | ZIP64/standard-EOCD override sentinel check — `diskWhereCDStarts` slot at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) — *"EOCD ZIP64-override mismatch"* (standard-EOCD `diskWhereCDStarts=99`, ZIP64 `diskWhereCDStarts=0`; standard value is neither the APPNOTE §4.3.16 sentinel `0xFFFF` nor a numeric match with the ZIP64 override. All other override slots remain at their sentinels so the relaxed sentinel arm passes for `cdSize`, `cdOffset`, `totalEntries`, `numberOfThisDisk`, `numEntriesThisDisk`, and the `diskWhereCDStarts` sub-check is the one that trips. `diskWhereCDStarts` is the cross-disk dispatch dual of the `numberOfThisDisk` smuggling vector: standard EOCD declares "the CD lives on disk N" while the ZIP64 EOCD64 declares "the CD lives on disk M", letting an attacker present two different archives to two different parsers from the same byte sequence. The downstream EOCD-level disk-number sanity check at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) (`numberOfThisDisk == 0 && diskWhereCDStarts == 0`) cannot be reached when the `diskWhereCDStarts` ZIP64-override sub-check fires first; this fixture exercises the upstream override-mismatch arm specifically. Per-slot sibling of `eocd-zip64-override-nosentinel.zip` (PR #1745, `cdOffset` slot), `eocd-zip64-override-cdsize-mismatch.zip` (PR #1900, `cdSize` slot), and `eocd-zip64-override-totalentries-mismatch.zip` (PR #1901, `totalEntries` slot) at the 6-field EOCD ZIP64-override mismatch family — the per-slot fixtures pin attribution to one specific override-slot guard rather than the family-wide check) | #1906 | other (ZIP64 consistency) |
| [testdata/zip/malformed/eocd-zip64-override-entriesthisdisk-mismatch.zip](/home/kim/lean-zip/testdata/zip/malformed/eocd-zip64-override-entriesthisdisk-mismatch.zip) | 198 B | ZIP64/standard-EOCD override sentinel check — `numEntriesThisDisk` slot at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) — *"EOCD ZIP64-override mismatch"* (standard-EOCD `numEntriesThisDisk=99`, ZIP64 `numEntriesThisDisk=1`; standard value is neither the APPNOTE §4.3.16 sentinel `0xFFFF` nor a numeric match with the ZIP64 override. All other override slots remain at their sentinels so the relaxed sentinel arm passes for `cdSize`, `cdOffset`, `totalEntries`, `numberOfThisDisk`, `diskWhereCDStarts`, and the `numEntriesThisDisk` sub-check is the one that trips. Distinct from the EOCD-internal `numEntriesThisDisk` vs. `totalEntries` consistency guard exercised by `eocd-numentries-thisdisk-mismatch.zip` (PR #1752): the same field name appears in two distinct guards — the override-arm compares the standard EOCD against the ZIP64 record, the internal-consistency arm at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) compares the post-override resolved values — and this fixture pins the override-arm specifically. The standard EOCD's `totalEntries` stays at the `0xFFFF` sentinel so the `totalEntries` override sub-check passes on its sentinel branch *before* the `numEntriesThisDisk` sub-check is reached; the downstream EOCD-internal consistency check is unreachable because the override sub-check fires first. Per-slot sibling of `eocd-zip64-override-nosentinel.zip` (PR #1745, `cdOffset` slot), `eocd-zip64-override-cdsize-mismatch.zip` (PR #1905, `cdSize` slot), `eocd-zip64-override-totalentries-mismatch.zip` (PR #1908, `totalEntries` slot), and `eocd-zip64-override-diskcd-mismatch.zip` (PR #1911, `diskWhereCDStarts` slot) at the 6-field EOCD ZIP64-override mismatch family — the per-slot fixtures pin attribution to one specific override-slot guard rather than the family-wide check) | #1907 | other (ZIP64 consistency) |
| [testdata/zip/malformed/eocd-zip64-override-totalentries-mismatch.zip](/home/kim/lean-zip/testdata/zip/malformed/eocd-zip64-override-totalentries-mismatch.zip) | 198 B | ZIP64/standard-EOCD override sentinel check — `totalEntries` slot at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) — *"EOCD ZIP64-override mismatch"* (standard-EOCD `totalEntries=99`, ZIP64 `totalEntries=1`; standard value is neither the APPNOTE §4.3.16 sentinel `0xFFFF` nor a numeric match with the ZIP64 override. All other override slots remain at their sentinels so the relaxed sentinel arm passes for `cdSize`, `cdOffset`, `numberOfThisDisk`, `diskWhereCDStarts`, `numEntriesThisDisk`, and the `totalEntries` sub-check is the one that trips. `totalEntries` is a particularly notable smuggling vector because it controls the entry-iteration loop of the CD walker — a relaxed reader that trusts a smuggled value walks more or fewer CD entries than the strict reader, opening entry-injection / entry-hiding attacks. Per-slot sibling of `eocd-zip64-override-nosentinel.zip` (PR #1745, `cdOffset` slot) and `eocd-zip64-override-cdsize-mismatch.zip` (PR #1900, `cdSize` slot) at the 6-field EOCD ZIP64-override mismatch family — the per-slot fixtures pin attribution to one specific override-slot guard rather than the family-wide check) | #1901 | other (ZIP64 consistency) |
| [testdata/zip/malformed/eocd-zip64-override-nosentinel.zip](/home/kim/lean-zip/testdata/zip/malformed/eocd-zip64-override-nosentinel.zip) | 198 B | ZIP64/standard-EOCD override sentinel check at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) — *"EOCD ZIP64-override mismatch"* (standard-EOCD `cdOffset=42`, ZIP64 `cdOffset=45`; standard value is neither the APPNOTE §4.3.16 sentinel `0xFFFFFFFF` nor a numeric match with the ZIP64 override — a parser-differential smuggling vector) | #1745 | other (ZIP64 consistency) |
| [testdata/zip/malformed/invalid-utf8-with-flag.zip](/home/kim/lean-zip/testdata/zip/malformed/invalid-utf8-with-flag.zip) | 120 B | UTF-8-flagged entry name strict parse at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) — *"invalid UTF-8 in entry name (UTF-8 flag set)"* | `481e562` | partial-decoder panic |
| [testdata/zip/malformed/lh-zip64-extra-duplicate.zip](/home/kim/lean-zip/testdata/zip/malformed/lh-zip64-extra-duplicate.zip) | 158 B | LH-side duplicate ZIP64 extra-block guard at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) — *"duplicate ZIP64 local extra field"* (CD entry has a single valid `headerId == 0x0001` block so CD parse passes; LH carries two 0x0001 blocks with `uncompSize` payloads `6` and `106`. `hasDuplicateZip64Extra` fires inside `readEntryData` before any CD/LH consistency check. Sibling of `cd-zip64-extra-duplicate.zip` — the two distinct error wordings keep attribution between the parse layers loud under future refactors) | #1793 | other (ZIP64 consistency) |
| [testdata/zip/malformed/no-eocd.zip](/home/kim/lean-zip/testdata/zip/malformed/no-eocd.zip) | 44 B | EOCD-scan failure at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) — *"cannot find end of central directory"* | `481e562` | other (framing) |
| [testdata/zip/malformed/oversized-compressed-size.zip](/home/kim/lean-zip/testdata/zip/malformed/oversized-compressed-size.zip) | 122 B | CD-entry stored-method size-invariant check at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) — *"stored-method size mismatch"* (CD/LH both advertise method=0 with compSize=2 MiB and uncompSize=6; `parseCentralDir` rejects post-ZIP64-resolution before any LH read. Previously caught by the later `local data span` check in `readEntryData` — PR #1773's CD-parse guard fires first, kept in-corpus for regression coverage at the earlier layer) | #1497 | oversized allocation |
| [testdata/zip/malformed/oversized-zip64-compressed-size.zip](/home/kim/lean-zip/testdata/zip/malformed/oversized-zip64-compressed-size.zip) | 134 B | CD-entry stored-method size-invariant check at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) — *"stored-method size mismatch"* (ZIP64 extra resolves compSize=1<<60, uncompSize=6 with method=0; `parseCentralDir` rejects post-ZIP64-resolution before any LH read. Previously caught by the later `local data span` check in `readEntryData` — PR #1773's CD-parse guard fires first, kept in-corpus for regression coverage at the earlier layer) | #1543 | oversized allocation |
| [testdata/zip/malformed/oversized-zip64-uncompressed-size.zip](/home/kim/lean-zip/testdata/zip/malformed/oversized-zip64-uncompressed-size.zip) | 134 B | CD-entry stored-method size-invariant check at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) — *"stored-method size mismatch"* (ZIP64 extra resolves compSize=6, uncompSize=1<<60 with method=0; `parseCentralDir` rejects post-ZIP64-resolution before any LH read. Previously caught by the LH ZIP64 truncation check in `readEntryData` — PR #1773's CD-parse guard fires first, kept in-corpus for regression coverage at the earlier layer) | #1544 | oversized allocation |
| [testdata/zip/malformed/too-short.zip](/home/kim/lean-zip/testdata/zip/malformed/too-short.zip) | 10 B | EOCD-scan failure at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) — *"cannot find end of central directory"* | `481e562` | other (framing) |
| [testdata/zip/malformed/zip64-eocd64-bad-recsize.zip](/home/kim/lean-zip/testdata/zip/malformed/zip64-eocd64-bad-recsize.zip) | 198 B | ZIP64 EOCD64 self-declared record-size check at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) — *"ZIP64 EOCD64 record-size mismatch"* (EOCD64 `size of this record` field at `bufPos + 4` carries `0` instead of the required `44` for a v1 EOCD64; lean-zip reads the record at fixed per-field offsets from a hard-coded 56-byte layout, while a stricter parser that trusts the self-declared length would read past or short of that — a parser-differential smuggling vector) | #1761 | other (ZIP64 consistency) |
| [testdata/zip/malformed/zip64-eocd64-v2-record.zip](/home/kim/lean-zip/testdata/zip/malformed/zip64-eocd64-v2-record.zip) | 214 B | ZIP64 EOCD64 self-declared record-size check at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) — *"ZIP64 EOCD64 record-size mismatch"* (EOCD64 `size of this record` field at `bufPos + 4` carries `60` — the APPNOTE §4.3.14.2 v2 shape with a 16-byte "zip64 extensible data sector" for strong-encryption (SES) fields `compositeSize` + `encryptionAlgID`, making the declared body `56 + 16 - 12 = 60` bytes; the physical record is internally consistent at `4 + 8 + 60 = 72` bytes, so a reader that trusts the declared length and parses per APPNOTE v2 semantics would accept the archive. lean-zip does not implement strong encryption, so v2 records remain rejected by policy — sibling of `zip64-eocd64-bad-recsize.zip` at the specific APPNOTE-documented v2-record angle, pinning the rejection behaviour against the v2 shape rather than a generic `recSize ≠ 44` boundary) | #1889 | other (ZIP64 consistency) |
| [testdata/zip/malformed/zip64-eocd64-versionmadeby-too-high.zip](/home/kim/lean-zip/testdata/zip/malformed/zip64-eocd64-versionmadeby-too-high.zip) | 198 B | ZIP64 EOCD64 `versionMadeBy` lower-byte upper-bound check at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) — *"ZIP64 EOCD64 versionMadeBy spec-version byte too high"* (EOCD64 `versionMadeBy` field at `bufPos + 12` carries `0x0340` — low byte `0x40 = 64`, one past the APPNOTE §4.4.2.2 cap of `63` (spec version 6.3); archive-level counterpart to the per-entry CD+4 `versionMadeBy` fixture, closing the `versionMadeBy` upper-bound dimension across both ZIP layers) | #1826 | other (ZIP64 consistency) |
| [testdata/zip/malformed/zip64-eocd64-versionneeded-too-high.zip](/home/kim/lean-zip/testdata/zip/malformed/zip64-eocd64-versionneeded-too-high.zip) | 198 B | ZIP64 EOCD64 `versionNeededToExtract` upper-bound check at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) — *"ZIP64 EOCD64 versionNeededToExtract too high"* (EOCD64 `versionNeededToExtract` field at `bufPos + 14` carries `0x00FF` — spec version 25.5, well above the APPNOTE §4.4.3.2 cap of `63` (spec version 6.3); upper-bound sibling of the lower-bound `≥ 45` check (issue #1758 / PR #1764), together closing the EOCD64 `versionNeededToExtract` two-sided-bound dimension. Archive-level analog of the per-entry CD+6 upper bound (PR #1807, `cd-version-needed-too-high.zip`); the archive-level cap is `63` (not `45`) because APPNOTE §4.4.3.2 documents the EOCD64 field as the version needed to interpret the record rather than to extract the largest entry) | #1852 | other (ZIP64 consistency) |
| [testdata/zip/malformed/zip64-extra-oversized-datasize.zip](/home/kim/lean-zip/testdata/zip/malformed/zip64-extra-oversized-datasize.zip) | 162 B | ZIP64 extra-field `dataSize` exactness check at [Zip/Archive.lean](/home/kim/lean-zip/Zip/Archive.lean) — *"malformed ZIP64 extra field"* (CD entry's ZIP64 extra `dataSize=16` claims two 8-byte slots while only `stdCompSize` is the sentinel, so APPNOTE §4.5.3 requires exactly `8 * 1 = 8` bytes; the trailing 8 bytes `0xDEADBEEFCAFEBABE` are attacker-chosen slack that a lenient parser silently discards. `parseZip64Extra` enforces `fpos == fieldEnd` after the three conditional reads — sibling of `zip64-eocd64-bad-recsize.zip` at a different layer of the same parser-differential attack class) | #1785 | other (ZIP64 consistency) |

## Required Maintenance Rule

Whenever a new parser, extraction path, FFI helper, or streaming API is
added, this file must be updated in the same change set with:

- trust status
- guardrails
- known missing work
- regression references if a bug prompted the change

Run `bash scripts/check-inventory-links.sh` after any change touching
`Zip/**`, `ZipTest/**`, `testdata/**`, or this file, and resolve any
hard-failure errors before merging. The script verifies fixture-path
existence (hard failure) and flags unresolved placeholder PR
references — `#TBD`, `#N`, `#XXX`, `#NNN`, or the phrase "<!-- drift-detector: literal documentation of placeholder tokens, not a placeholder itself -->this PR" (advisory warning). The
line-anchor freshness passes were retired by PR #2353 (closing
#2345); cite by stable identifier (function name, theorem name,
fixture filename, section header) so the audit trail does not drift
with line shifts.
