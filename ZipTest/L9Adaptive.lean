import ZipTest.Helpers
import Zip.Native.DeflateDynamic

/-! Focused tests for the adaptive production level-9 route. -/

open Zip.Native.Deflate

namespace ZipTest.L9Adaptive

def assertRoute (name : String) (actual expected : L9AdaptiveRoute) : IO Unit :=
  unless actual == expected do
    throw (IO.userError
      s!"L9 route {name}: expected {repr expected}, got {repr actual}")

def assertProfile (name : String) (actual expected : L7Profile) : IO Unit :=
  unless actual == expected do
    throw (IO.userError
      s!"L9 profile {name}: expected {repr expected}, got {repr actual}")

def allProfiles : List L7Profile := [
  .chain64Probe8, .shallow, .chain64Probe16, .h3Fast, .h3Balanced,
  .chain96Probe16, .chain128Probe16, .chain128Probe32,
  .chain128LongProbe32, .deep
]

def l8Profiles : List L7Profile := [
  .chain64Probe8, .shallow, .chain64Probe16, .chain96Probe16,
  .chain128Probe16, .chain128Probe32
]

def l10Profiles : List L7Profile := [
  .chain128LongProbe32, .h3Fast, .deep
]

/-- Pin each route executor arm to its named source pipeline without requiring
    a multi-megabyte fixture. -/
def checkSelectedPayloadIdentity : IO Unit := do
  let data := ByteArray.mk <| (Array.range 4096).map fun i =>
    ((i * 17 + i / 23) % 251).toUInt8
  for route in [.currentL9, .level8, .level10] do
    let expected :=
      match route with
      | .currentL9 => deflateRawL9P data
      | .level8 => deflateRawL8P data
      | .level10 => deflateRawL10P data
    unless deflateRawL9RouteP data route == expected do
      throw (IO.userError
        s!"L9 selected payload differs from {repr route} source point")

/-- A deterministic 5 MiB input made by repeating one pseudo-random 8 KiB
    block.  Each sampled region contains enough repeated four-grams to reject
    the incompressible prescan, while the cardinality profile selects an L8
    source point. -/
private def adaptiveExerciseData : ByteArray :=
  let seed := mkPrngData 8192 0x9A31F00D
  ByteArray.mk <| Array.ofFn (n := l9AdaptiveMinSize) fun i =>
    seed[i.val % seed.size]!

/-- A run-heavy at-gate fixture whose low four-gram cardinality deterministically
    selects `chain128LongProbe32`, and therefore the public L10 source point. -/
private def adaptiveL10ExerciseData : ByteArray :=
  ByteArray.mk <| Array.replicate l9AdaptiveMinSize (0x41 : UInt8)

/-- Exercise the inclusive production gate in ordinary CI and pin its selected
    payload to the exact named L8 pipeline. -/
def checkAdaptiveProductionArm : IO Unit := do
  let data := adaptiveExerciseData
  unless data.size == l9AdaptiveMinSize do
    throw (IO.userError
      s!"L9 synthetic fixture: expected {l9AdaptiveMinSize} bytes, got {data.size}")
  if incompressiblePrescan data then
    throw (IO.userError "L9 synthetic fixture unexpectedly took the stored prescan route")
  let profile := l7ProfileFor data
  assertProfile "synthetic-at-gate" profile .chain128Probe16
  assertRoute "synthetic-at-gate"
    (l9AdaptiveRouteFor data.size profile) .level8
  let production := deflateRaw data 9
  let selected := deflateRawL8P data
  unless production == selected do
    throw (IO.userError
      "L9 synthetic fixture differs from exact selected L8 payload")
  let decoded ← RawDeflate.decompress production data.size.toUInt64
  unless decoded == data do
    throw (IO.userError "L9 synthetic fixture roundtrip failed")

/-- Exercise a public L10-selected production arm in ordinary CI, including
    byte identity with the public level-10 endpoint and a decoder roundtrip. -/
def checkAdaptiveL10ProductionArm : IO Unit := do
  let data := adaptiveL10ExerciseData
  unless data.size == l9AdaptiveMinSize do
    throw (IO.userError
      s!"L9 synthetic L10 fixture: expected {l9AdaptiveMinSize} bytes, got {data.size}")
  if incompressiblePrescan data then
    throw (IO.userError
      "L9 synthetic L10 fixture unexpectedly took the stored prescan route")
  let profile := l7ProfileFor data
  assertProfile "synthetic-L10-at-gate" profile .chain128LongProbe32
  assertRoute "synthetic-L10-at-gate"
    (l9AdaptiveRouteFor data.size profile) .level10
  let production := deflateRaw data 9
  let publicL10 := deflateRaw data 10
  unless production == publicL10 do
    throw (IO.userError
      "L9 synthetic L10 fixture differs from public level-10 payload")
  let decoded ← RawDeflate.decompress production data.size.toUInt64
  unless decoded == data do
    throw (IO.userError "L9 synthetic L10 fixture roundtrip failed")

def canterburyFiles : List String := [
  "alice29.txt", "asyoulik.txt", "cp.html", "fields.c", "grammar.lsp",
  "kennedy.xls", "lcet10.txt", "plrabn12.txt", "ptt5", "sum", "xargs.1"
]

def silesia :
    List (String × Nat × L7Profile × L9AdaptiveRoute) := [
  ("dickens", 10192446, .chain96Probe16, .level8),
  ("mozilla", 51220480, .h3Balanced, .level8),
  ("mr", 9970564, .chain64Probe8, .level8),
  ("nci", 33553445, .chain128LongProbe32, .level10),
  ("ooffice", 6152192, .h3Balanced, .level10),
  ("osdb", 10085684, .shallow, .level8),
  ("reymont", 6627202, .chain128Probe16, .level8),
  ("samba", 21606400, .chain64Probe16, .level8),
  ("sao", 7251944, .h3Balanced, .level10),
  ("webster", 41458703, .chain128Probe32, .level8),
  ("x-ray", 8474240, .h3Fast, .level10),
  ("xml", 5345280, .deep, .level10)
]

/-- The committed sub-5 MiB corpus must retain the exact former L9 payload. -/
def checkCanterburyBypass : IO Unit := do
  for name in canterburyFiles do
    let path := "bench/corpora/canterbury/" ++ name
    let data ← IO.FS.readBinFile path
    unless data.size < l9AdaptiveMinSize do
      throw (IO.userError s!"L9 bypass fixture unexpectedly above gate: {name}")
    let profile := l7ProfileFor data
    assertRoute name (l9AdaptiveRouteFor data.size profile) .currentL9
    let reference :=
      if incompressiblePrescan data then
        Zip.Spec.DeflateStoredCorrect.deflateStoredPure data
      else
        deflateRawL9P data
    let production := deflateRaw data 9
    unless production == reference do
      throw (IO.userError
        s!"L9 bypass {name}: production bytes differ from pre-adaptive L9")

/-- When the optional Silesia corpus is present, exercise actual signal
    extraction, exact selected-anchor payload identity, roundtrip, and output
    ordering on every file. -/
def checkSilesiaIfPresent : IO Unit := do
  for (name, expectedSize, expectedProfile, expectedRoute) in silesia do
    let path := "bench/corpora/silesia/" ++ name
    if ← System.FilePath.pathExists path then
      let data ← IO.FS.readBinFile path
      unless data.size == expectedSize do
        throw (IO.userError
          s!"Silesia {name}: expected {expectedSize} input bytes, got {data.size}")
      let profile := l7ProfileFor data
      assertProfile name profile expectedProfile
      assertRoute name (l9AdaptiveRouteFor data.size profile) expectedRoute
      let l8 := deflateRaw data 8
      let l10 := deflateRaw data 10
      let production := deflateRaw data 9
      let selected :=
        match expectedRoute with
        | .level8 => l8
        | .level10 => l10
        | .currentL9 => ByteArray.empty
      unless production == selected do
        throw (IO.userError
          s!"Silesia {name}: adaptive L9 differs from exact selected payload")
      unless production.size ≤ l8.size && l10.size ≤ production.size do
        throw (IO.userError
          s!"Silesia {name}: expected L8 >= adaptive L9 >= L10 output ordering")
      let decoded ← RawDeflate.decompress production data.size.toUInt64
      unless decoded == data do
        throw (IO.userError s!"Silesia {name}: adaptive L9 roundtrip failed")

def tests : IO Unit := do
  IO.println "  L9 adaptive-selector tests..."

  -- The bounded gate is inclusive: every profile preserves current L9
  -- immediately outside 5–64 MiB and selects an L8/L10 source point at both
  -- edges.
  for profile in allProfiles do
    assertRoute s!"below-gate/{repr profile}"
      (l9AdaptiveRouteFor (l9AdaptiveMinSize - 1) profile) .currentL9
    assertRoute s!"above-gate/{repr profile}"
      (l9AdaptiveRouteFor (l9AdaptiveMaxSize + 1) profile) .currentL9
  for profile in l8Profiles do
    assertRoute s!"at-gate/L8/{repr profile}"
      (l9AdaptiveRouteFor l9AdaptiveMinSize profile) .level8
    assertRoute s!"at-upper-edge/L8/{repr profile}"
      (l9AdaptiveRouteFor l9AdaptiveMaxSize profile) .level8
  for profile in l10Profiles do
    assertRoute s!"at-gate/L10/{repr profile}"
      (l9AdaptiveRouteFor l9AdaptiveMinSize profile) .level10
    assertRoute s!"at-upper-edge/L10/{repr profile}"
      (l9AdaptiveRouteFor l9AdaptiveMaxSize profile) .level10
  assertRoute "at-upper-edge/balanced"
    (l9AdaptiveRouteFor l9AdaptiveMaxSize .h3Balanced) .level8

  -- Balanced-H3 switches from exact L10 to exact L8 at 20 MiB.
  assertRoute "balanced/at-gate"
    (l9AdaptiveRouteFor l9AdaptiveMinSize .h3Balanced) .level10
  assertRoute "balanced/below-L8-boundary"
    (l9AdaptiveRouteFor
      (l9AdaptiveH3BalancedL10MaxSize - 1) .h3Balanced) .level10
  assertRoute "balanced/at-L8-boundary"
    (l9AdaptiveRouteFor
      l9AdaptiveH3BalancedL10MaxSize .h3Balanced) .level8

  -- Pin all twelve Silesia decisions without requiring the optional payloads.
  for (name, size, profile, route) in silesia do
    assertRoute name (l9AdaptiveRouteFor size profile) route

  checkSelectedPayloadIdentity
  checkAdaptiveProductionArm
  checkAdaptiveL10ProductionArm
  checkCanterburyBypass
  checkSilesiaIfPresent

end ZipTest.L9Adaptive
