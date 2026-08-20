/-! Shared formatting and timing helpers for benchmark files.

    Consolidates `pad`, `fmtMs`, `fmtMBps`, `fmtRatio`, `forceEval`, and
    `calibrateIters` that were previously duplicated as `private def`s across
    `Benchmark.lean`, `NativeCompressBench.lean`, `ZstdDecompressBench.lean`,
    and `NativeScale.lean`. -/

/-- Right-pad a string to at least `w` characters. -/
def pad (s : String) (w : Nat) : String :=
  s ++ String.ofList (List.replicate (w - min w s.length) ' ')

/-- Format nanoseconds as a human-readable millisecond string (e.g. "1.23"). -/
def fmtMs (ns : Nat) : String :=
  let us := ns / 1000
  let ms := us / 1000
  let frac := us % 1000
  if ms ≥ 10 then s!"{ms}.{frac / 100}"
  else if ms ≥ 1 then
    let d2 := frac / 10
    s!"{ms}.{if d2 < 10 then "0" else ""}{d2}"
  else
    s!"{ms}.{if frac < 100 then "0" else ""}{if frac < 10 then "0" else ""}{frac}"

/-- Format throughput as MB/s with one decimal place, right-aligned to 5 chars. -/
def fmtMBps (dataSize : Nat) (elapsedNs : Nat) : String :=
  if elapsedNs == 0 then "    ∞" else
  let mbps10 := dataSize * 10000000000 / elapsedNs / (1024 * 1024)
  let whole := mbps10 / 10
  let frac := mbps10 % 10
  let s := s!"{whole}.{frac}"
  let padding := if s.length < 5 then String.ofList (List.replicate (5 - s.length) ' ') else ""
  padding ++ s

/-- Format a ratio (num/denom) as a short decimal string. -/
def fmtRatio (num denom : Nat) : String :=
  if denom == 0 then "  N/A" else
  let r := num.toFloat / denom.toFloat
  let s := s!"{r}"
  if s.length > 5 then (s.take 5).toString else s

/-- `@[noinline]` identity for preventing dead-code elimination in benchmarks. -/
@[noinline] def forceEval (b : ByteArray) : IO ByteArray := pure b

/-- Auto-calibrate iteration count based on data size. -/
def calibrateIters (dataSize : Nat) : Nat :=
  if dataSize ≤ 16384 then 100
  else if dataSize ≤ 1048576 then 10
  else 1
