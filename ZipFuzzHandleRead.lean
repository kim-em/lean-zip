import ZipTest.FuzzHandleRead

/-! Lake executable driver for the `Handle.read` / `Stream.read`
fuzz harness.

Runs `ZipTest.FuzzHandleRead.runFuzzUntil` for a wall-clock budget
read from the `LEAN_ZIP_FUZZ_HANDLE_READ_SECONDS` environment
variable (default 30 seconds). The PRNG seed is read from
`LEAN_ZIP_FUZZ_HANDLE_READ_SEED` (default `0xc0ffeec0ffeec0ff`).
Exit code 0 on clean completion; any uncaught exception or
sanitizer trap terminates with non-zero status.

Usage:
  scripts/fuzz-handle-read.sh [seconds]
  LEAN_ZIP_FUZZ_HANDLE_READ_SECONDS=60 .lake/build/bin/fuzz_handle_read

See #2380 (the in-repo deterministic regression harness for the
`lean_io_prim_handle_read` class) and `SECURITY_INVENTORY.md`
*Trusted Computing Base → Lean Runtime* *Recent wins*. -/

def getEnvNatOr (name : String) (default : Nat) : IO Nat := do
  match ← IO.getEnv name with
  | none => return default
  | some v =>
    match v.trimAscii.toNat? with
    | some n => return n
    | none => return default

def getEnvUInt64Or (name : String) (default : UInt64) : IO UInt64 := do
  match ← IO.getEnv name with
  | none => return default
  | some v =>
    match v.trimAscii.toNat? with
    | some n => return n.toUInt64
    | none => return default

def main (args : List String) : IO Unit := do
  let cliSeconds : Option Nat := args.head?.bind (·.trimAscii.toNat?)
  let seconds : Nat ← match cliSeconds with
    | some n => pure n
    | none => getEnvNatOr "LEAN_ZIP_FUZZ_HANDLE_READ_SECONDS" 30
  let seed ← getEnvUInt64Or "LEAN_ZIP_FUZZ_HANDLE_READ_SEED" 0xc0ffeec0ffeec0ff
  let startMs ← IO.monoMsNow
  let deadline := startMs + seconds * 1000
  IO.println s!"[fuzz-handle-read] seconds={seconds} seed={seed} \
deadline={deadline}ms"
  let iterations ← ZipTest.FuzzHandleRead.runFuzzUntil seed deadline
  let elapsedMs := (← IO.monoMsNow) - startMs
  IO.println s!"[fuzz-handle-read] iterations={iterations} elapsed={elapsedMs}ms"
