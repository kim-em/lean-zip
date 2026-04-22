import ZipTest.FuzzInflate

/-! Lake executable driver for the inflate fuzz harness.

Runs `ZipTest.FuzzInflate.runFuzzUntil` for a wall-clock budget read
from the `LEAN_ZIP_FUZZ_SECONDS` environment variable (default 30
seconds). The PRNG seed is read from `LEAN_ZIP_FUZZ_SEED` (default
`0xdeadbeefcafef00d`). Exit code 0 on clean completion; any uncaught
exception or sanitizer trap terminates with non-zero status.

Usage:
  scripts/fuzz-inflate.sh [seconds]
  LEAN_ZIP_FUZZ_SECONDS=60 .lake/build/bin/fuzz_inflate

See `plans/track-e-current-audit-checklist.md` Priority 3 item 3 and
`SECURITY_INVENTORY.md` *Fuzz coverage*. -/

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
    | none => getEnvNatOr "LEAN_ZIP_FUZZ_SECONDS" 30
  let seed ← getEnvUInt64Or "LEAN_ZIP_FUZZ_SEED" 0xdeadbeefcafef00d
  let startMs ← IO.monoMsNow
  let deadline := startMs + seconds * 1000
  IO.println s!"[fuzz-inflate] seconds={seconds} seed={seed} \
deadline={deadline}ms"
  let iterations ← ZipTest.FuzzInflate.runFuzzUntil seed deadline
  let elapsedMs := (← IO.monoMsNow) - startMs
  IO.println s!"[fuzz-inflate] iterations={iterations} elapsed={elapsedMs}ms"
