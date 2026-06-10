import Zip
/-! # ratio-sweep — block-split knob sweep probe

Sweeps the two `deflateRaw` block-split size knobs — `splitChunkSize`
(self-contained split) and `sharedTokChunk` (cross-block split) — over corpus
files at the max-compression tiers (levels 7–9, the only levels where the
splits activate), printing one CSV row per measurement:

    <file>,<level>,<variant>,<knob>,<size>

with no header (invocations are concatenated by a parallel driver). Variants:

  * `base`   — single-block `deflateRawBase` (the `pickSmaller` floor); empty knob
  * `sc`     — `deflateDynamicBlocksSC` at each chunk-size candidate (each is a
               full fresh-window match pass — chunks must be matched in isolation,
               so the passes cannot be shared across candidates)
  * `shared` — cross-block split at each token-chunk candidate; the whole-file
               `lzMatch` token pass is computed **once** per (file, level) and
               re-partitioned per candidate via `emitSharedBlocks`
  * `zlib`   — FFI zlib raw deflate at the same level (reference); empty knob

Sanity assertions cross-check the reused-token-pass emission against the real
`deflateDynamicBlocksShared`, and `min` over the candidates at the current
defaults against what `deflateRaw` actually emits — so the sweep measures the
deployed candidates, not near-copies. `--fast` skips these (re-running the
default candidates roughly doubles the per-file cost on large inputs).

Usage: lake exe ratio-sweep [--fast] <file> [<file> ...]
-/

open Zip.Native (BitWriter)
open Zip.Native.Deflate

/-- Self-contained split chunk-size candidates (powers of two bracketing the
    current `splitChunkSize = 32768`). -/
def scGrid : List Nat := [8192, 16384, 32768, 65536, 131072]

/-- Cross-block split token-chunk candidates (powers of two bracketing the
    current `sharedTokChunk = 4096`). -/
def sharedGrid : List Nat := [1024, 2048, 4096, 8192, 16384, 32768]

/-- The block-split activation range of `deflateRaw`. -/
def sweepLevels : List UInt8 := [7, 8, 9]

/-- Shared-variant compressed size at `tokChunk`, reusing the precomputed
    whole-file token stream (`deflateDynamicBlocksShared` recomputes it per
    call; the partitioning itself is cheap). Mirrors its empty-input guard. -/
def sharedSizeAt (data : ByteArray) (toks : Array LZ77Token) (level : UInt8)
    (tokChunk : Nat) : Nat :=
  if data.size == 0 then (deflateDynamicBlocksShared data tokChunk level).size
  else ((emitSharedBlocks data toks tokChunk 0 BitWriter.empty).flush).size

def row (file : String) (level : UInt8) (variant knob : String) (size : Nat) :
    String :=
  s!"{file},{level},{variant},{knob},{size}"

/-- Sweep one file at all `sweepLevels`, printing CSV rows to stdout. -/
def runFile (verify : Bool) (path : String) : IO Unit := do
  let data ← IO.FS.readBinFile path
  -- Label rows as "<parent>/<file>" (e.g. "silesia/dickens") when available.
  let p := System.FilePath.mk path
  let label := match p.parent >>= (·.fileName), p.fileName with
    | some d, some f => s!"{d}/{f}"
    | _, some f => f
    | _, _ => path
  for level in sweepLevels do
    IO.println (row label level "base" "" (deflateRawBase data level).size)
    -- One match pass per (file, level), re-partitioned per candidate.
    let toks := lzMatch data level
    let mut sharedDefault := 0
    for t in sharedGrid do
      let sz := sharedSizeAt data toks level t
      if t == sharedTokChunk then sharedDefault := sz
      IO.println (row label level "shared" (toString t) sz)
    let mut scDefault := 0
    for c in scGrid do
      let sz := (deflateDynamicBlocksSC data c level).size
      if c == splitChunkSize then scDefault := sz
      IO.println (row label level "sc" (toString c) sz)
    IO.println (row label level "zlib" "" (← RawDeflate.compress data level).size)
    if verify then
      -- The reused-token-pass emission must equal the deployed shared variant …
      let sharedReal := (deflateDynamicBlocksShared data sharedTokChunk level).size
      unless sharedDefault == sharedReal do
        throw (IO.userError
          s!"{label} L{level}: shared probe {sharedDefault} ≠ deflateDynamicBlocksShared {sharedReal}")
      -- … and the best candidate at the current defaults must be what
      -- `deflateRaw` emits (`pickSmaller` over the same three streams).
      let emitted := (deflateRaw data level).size
      let best := min (deflateRawBase data level).size (min scDefault sharedDefault)
      unless best == emitted do
        throw (IO.userError
          s!"{label} L{level}: min(candidates) {best} ≠ deflateRaw {emitted}")
    IO.eprintln s!"  {label} L{level} done"

def main (args : List String) : IO Unit := do
  let (fast, files) := (args.contains "--fast", args.filter (· ≠ "--fast"))
  if files.isEmpty then
    throw (IO.userError "usage: ratio-sweep [--fast] <file> [<file> ...]")
  files.forM (runFile (verify := !fast))
