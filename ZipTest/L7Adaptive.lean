import ZipTest.Helpers
import Zip.Native.DeflateDynamic

/-! Golden tests for the level-7 content-profile and split-cadence selectors.

The classifier inputs below are deterministic summaries of the eleven
Canterbury and twelve Silesia files used to tune the policy.  Canterbury is
tracked in the repository, so those files also exercise signal extraction.
Silesia extraction is checked when the optional downloaded corpus is present;
the summary goldens still cover all twelve files in ordinary CI.
-/

open Zip.Native.Deflate

namespace ZipTest.L7Adaptive

def assertProfile (name : String) (actual expected : L7Profile) : IO Unit :=
  unless actual == expected do
    throw (IO.userError s!"L7 selector {name}: expected {repr expected}, got {repr actual}")

def assertRoute (name : String) (actual expected : L7OutputRoute) : IO Unit :=
  unless actual == expected do
    throw (IO.userError s!"L7 route {name}: expected {repr expected}, got {repr actual}")

def checkSmall (name : String) (size runs : Nat) (expected : L7Profile) : IO Unit :=
  assertProfile name (l7ClassifySmall size runs) expected

def checkLarge (name : String) (minUnique meanUnique maxUnique : Nat)
    (expected : L7Profile) : IO Unit :=
  assertProfile name (l7ClassifyLarge minUnique meanUnique maxUnique) expected

def checkCadence (name : String) (size : Nat) (profile : L7Profile)
    (expected : Nat) : IO Unit := do
  let actual := l7SplitCheckTokensForSize size profile
  unless actual == expected do
    throw (IO.userError s!"L7 cadence {name}: expected {expected}, got {actual}")

def checkFileIfPresent (path : String) (expectedProfile : L7Profile)
    (expectedCadence : Nat) (expectedRoute : L7OutputRoute)
    (expectedSize : Nat) : IO Unit := do
  if ← System.FilePath.pathExists path then
    let data ← IO.FS.readBinFile path
    let profile := l7ProfileFor data
    assertProfile path profile expectedProfile
    checkCadence path data.size profile expectedCadence
    assertRoute path (l7OutputRouteFor data.size profile) expectedRoute
    let ptokens := l7MatchPFor data profile
    let cuts := chooseSplitsHeuristicPUPacked ptokens data.size
      (l7SplitCheckTokensFor data profile)
    let legacy := deflateRawSplitTierP data ptokens cuts
    let routed := deflateRawL7RouteP data profile ptokens
    unless routed == legacy do
      throw (IO.userError s!"L7 route {path}: bytes differ from size-arbitrated winner")
    unless routed.size == expectedSize do
      throw (IO.userError
        s!"L7 route {path}: expected {expectedSize} bytes, got {routed.size}")

def tests : IO Unit := do
  IO.println "  L7 adaptive-selector tests..."

  -- Canterbury: (size, adjacent equal pairs among the ≤63 probes).
  checkSmall "alice29.txt" 152089 5 .chain64Probe8
  checkSmall "asyoulik.txt" 125179 0 .shallow
  checkSmall "cp.html" 24603 4 .chain64Probe16
  checkSmall "fields.c" 11150 4 .chain64Probe16
  checkSmall "grammar.lsp" 3721 5 .chain64Probe16
  checkSmall "kennedy.xls" 1029744 11 .shallow
  checkSmall "lcet10.txt" 426754 16 .shallow
  checkSmall "plrabn12.txt" 481861 1 .shallow
  checkSmall "ptt5" 513216 63 .chain128Probe16
  checkSmall "sum" 38240 10 .h3Fast
  checkSmall "xargs.1" 4227 1 .chain64Probe16

  -- Canterbury: cadence selected from the profile and exact input size.
  checkCadence "alice29.txt" 152089 .chain64Probe8 512
  checkCadence "asyoulik.txt" 125179 .shallow 512
  checkCadence "cp.html" 24603 .chain64Probe16 512
  checkCadence "fields.c" 11150 .chain64Probe16 512
  checkCadence "grammar.lsp" 3721 .chain64Probe16 512
  checkCadence "kennedy.xls" 1029744 .shallow 512
  checkCadence "lcet10.txt" 426754 .shallow 4096
  checkCadence "plrabn12.txt" 481861 .shallow 1024
  checkCadence "ptt5" 513216 .chain128Probe16 4096
  checkCadence "sum" 38240 .h3Fast 512
  checkCadence "xargs.1" 4227 .chain64Probe16 512

  -- Silesia: four-region HLL-style unique-four-gram fractions, per mille.
  checkLarge "dickens" 503 579 628 .chain96Probe16
  checkLarge "mozilla" 403 414 427 .h3Balanced
  checkLarge "mr" 54 307 614 .chain64Probe8
  checkLarge "nci" 90 102 126 .chain128LongProbe32
  checkLarge "ooffice" 249 545 835 .h3Balanced
  checkLarge "osdb" 462 528 615 .shallow
  checkLarge "reymont" 162 283 343 .chain128Probe16
  checkLarge "samba" 29 325 521 .chain64Probe16
  checkLarge "sao" 629 708 887 .h3Balanced
  checkLarge "webster" 461 511 564 .chain128Probe32
  checkLarge "x-ray" 726 917 1000 .h3Fast
  checkLarge "xml" 99 199 416 .deep

  -- Silesia: cadence selected from the profile and exact input size.
  checkCadence "dickens" 10192446 .chain96Probe16 4096
  checkCadence "mozilla" 51220480 .h3Balanced 512
  checkCadence "mr" 9970564 .chain64Probe8 512
  checkCadence "nci" 33553445 .chain128LongProbe32 4096
  checkCadence "ooffice" 6152192 .h3Balanced 1024
  checkCadence "osdb" 10085684 .shallow 2016
  checkCadence "reymont" 6627202 .chain128Probe16 512
  checkCadence "samba" 21606400 .chain64Probe16 1024
  checkCadence "sao" 7251944 .h3Balanced 512
  checkCadence "webster" 41458703 .chain128Probe32 512
  checkCadence "x-ray" 8474240 .h3Fast 1024
  checkCadence "xml" 5345280 .deep 512

  -- Pin the three held-out-safe small-input exceptions and their boundary.
  assertRoute "small/h3Fast/0" (l7OutputRouteFor 0 .h3Fast) .split
  assertRoute "small/h3Fast/max"
    (l7OutputRouteFor (h3ProbeMinSize - 1) .h3Fast) .split
  for profile in [.chain64Probe8, .shallow] do
    assertRoute s!"small/split/{repr profile}"
      (l7OutputRouteFor (l7SmallDirectSplitMaxSize - 1) profile) .split
    assertRoute s!"small/fallback/{repr profile}"
      (l7OutputRouteFor l7SmallDirectSplitMaxSize profile) .arbitrate

  -- All other small profiles retain exact size arbitration.
  let fallbackProfiles : List L7Profile := [
    .h3Balanced, .chain64Probe16, .chain96Probe16, .chain128Probe16,
    .chain128Probe32, .chain128LongProbe32, .deep
  ]
  for profile in fallbackProfiles do
    assertRoute s!"small/{repr profile}"
      (l7OutputRouteFor (h3ProbeMinSize - 1) profile) .arbitrate

  -- Pin the route independently of signal extraction, then exercise extraction
  -- and exact winner-byte identity on every available file.  Canterbury is
  -- committed; Silesia is an optional download under the ignored directory.
  let files : List (String × Nat × L7Profile × Nat × L7OutputRoute × Nat) := [
    ("canterbury/alice29.txt", 152089, .chain64Probe8, 512, .split, 54155),
    ("canterbury/asyoulik.txt", 125179, .shallow, 512, .split, 48703),
    ("canterbury/cp.html", 24603, .chain64Probe16, 512, .arbitrate, 7914),
    ("canterbury/fields.c", 11150, .chain64Probe16, 512, .arbitrate, 3120),
    ("canterbury/grammar.lsp", 3721, .chain64Probe16, 512, .arbitrate, 1209),
    ("canterbury/kennedy.xls", 1029744, .shallow, 512, .arbitrate, 203000),
    ("canterbury/lcet10.txt", 426754, .shallow, 4096, .arbitrate, 145333),
    ("canterbury/plrabn12.txt", 481861, .shallow, 1024, .arbitrate, 195481),
    ("canterbury/ptt5", 513216, .chain128Probe16, 4096, .arbitrate, 55006),
    ("canterbury/sum", 38240, .h3Fast, 512, .split, 12675),
    ("canterbury/xargs.1", 4227, .chain64Probe16, 512, .arbitrate, 1723),
    ("silesia/dickens", 10192446, .chain96Probe16, 4096, .split, 3841249),
    ("silesia/mozilla", 51220480, .h3Balanced, 512, .split, 18825061),
    ("silesia/mr", 9970564, .chain64Probe8, 512, .split, 3594763),
    ("silesia/nci", 33553445, .chain128LongProbe32, 4096, .split, 3060352),
    ("silesia/ooffice", 6152192, .h3Balanced, 1024, .split, 3082223),
    ("silesia/osdb", 10085684, .shallow, 2016, .base, 3652998),
    ("silesia/reymont", 6627202, .chain128Probe16, 512, .split, 1840013),
    ("silesia/samba", 21606400, .chain64Probe16, 1024, .split, 5408935),
    ("silesia/sao", 7251944, .h3Balanced, 512, .split, 5336619),
    ("silesia/webster", 41458703, .chain128Probe32, 512, .base, 12029742),
    ("silesia/x-ray", 8474240, .h3Fast, 1024, .split, 6033708),
    ("silesia/xml", 5345280, .deep, 512, .split, 660492)
  ]
  for (file, size, profile, cadence, route, expectedSize) in files do
    assertRoute file (l7OutputRouteFor size profile) route
    checkFileIfPresent ("bench/corpora/" ++ file) profile cadence route expectedSize

end ZipTest.L7Adaptive
