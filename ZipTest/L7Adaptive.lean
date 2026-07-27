import ZipTest.Helpers
import Zip.Native.DeflateDynamic

/-! Golden tests for the adaptive level-2–7 content routes.

The classifier inputs below are deterministic summaries of the eleven
Canterbury and twelve Silesia files used to tune the policy.  Canterbury is
tracked in the repository, so those files also exercise signal extraction.
Silesia extraction is checked when the optional downloaded corpus is present;
the summary goldens still cover all twelve files in ordinary CI. A synthetic
input within the adaptive band exercises production L2–L6 in ordinary CI.
-/

open Zip.Native.Deflate

namespace ZipTest.L7Adaptive

def assertProfile (name : String) (actual expected : L7Profile) : IO Unit :=
  unless actual == expected do
    throw (IO.userError s!"L7 selector {name}: expected {repr expected}, got {repr actual}")

def assertRoute (name : String) (actual expected : L7OutputRoute) : IO Unit :=
  unless actual == expected do
    throw (IO.userError s!"L7 route {name}: expected {repr expected}, got {repr actual}")

def assertL2Route (name : String) (actual expected : L2AdaptiveRoute) : IO Unit :=
  unless actual == expected do
    throw (IO.userError s!"L2 route {name}: expected {repr expected}, got {repr actual}")

def assertL3Route (name : String) (actual expected : L3AdaptiveRoute) : IO Unit :=
  unless actual == expected do
    throw (IO.userError s!"L3 route {name}: expected {repr expected}, got {repr actual}")

def assertL4Route (name : String) (actual expected : L4AdaptiveRoute) : IO Unit :=
  unless actual == expected do
    throw (IO.userError s!"L4 route {name}: expected {repr expected}, got {repr actual}")

def assertL5Route (name : String) (actual expected : L5AdaptiveRoute) : IO Unit :=
  unless actual == expected do
    throw (IO.userError s!"L5 route {name}: expected {repr expected}, got {repr actual}")

def assertL6Route (name : String) (actual expected : L6AdaptiveRoute) : IO Unit :=
  unless actual == expected do
    throw (IO.userError s!"L6 route {name}: expected {repr expected}, got {repr actual}")

def assertBytes (name : String) (actual expected : ByteArray) : IO Unit :=
  unless actual == expected do
    throw (IO.userError
      s!"adaptive payload {name}: expected {expected.size} bytes, got {actual.size}")

def assertOutputGolden (name : String) (actual : ByteArray)
    (expectedSize : Nat) (expectedCrc : UInt32) : IO Unit := do
  let actualCrc := Crc32.Native.crc32 0 actual
  unless actual.size == expectedSize && actualCrc == expectedCrc do
    throw (IO.userError s!"adaptive golden {name}: expected size/CRC {expectedSize}/{expectedCrc}, got {actual.size}/{actualCrc}")

def checkAdaptiveRoutes (name : String) (size : Nat) (profile : L7Profile)
    (expected2 : L2AdaptiveRoute) (expected3 : L3AdaptiveRoute)
    (expected4 : L4AdaptiveRoute) (expected5 : L5AdaptiveRoute)
    (expected6 : L6AdaptiveRoute) : IO Unit := do
  assertL2Route name (l2AdaptiveRouteForProfile size profile) expected2
  assertL3Route name (l3AdaptiveRouteForProfile size profile) expected3
  assertL4Route name (l4AdaptiveRouteForProfile size profile) expected4
  assertL5Route name (l5AdaptiveRouteForProfile size profile) expected5
  assertL6Route name (l6AdaptiveRouteForProfile size profile) expected6

/-- Deterministic restricted-alphabet data: compressible enough to bypass the
    stored pre-scan, but with enough distinct four-grams to select h3-balanced. -/
def mkAdaptiveAlphabetData (size : Nat) : ByteArray := Id.run do
  let mut state : UInt32 := 2463534242
  let mut result := ByteArray.empty
  for _ in [:size] do
    state := state ^^^ (state <<< 13)
    state := state ^^^ (state >>> 17)
    state := state ^^^ (state <<< 5)
    result := result.push (state.toNat % 11).toUInt8
  return result

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
    (expectedSize : Nat) : IO (Option (Array Nat)) := do
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
    let production := deflateRaw data 7
    unless production == routed do
      throw (IO.userError s!"L7 production dispatch {path}: bytes differ from selected route")
    unless routed.size == expectedSize do
      throw (IO.userError
        s!"L7 route {path}: expected {expectedSize} bytes, got {routed.size}")
    if useAdaptiveFastTier data.size then
      assertL2Route path (l2AdaptiveRouteFor data)
        (l2AdaptiveRouteForProfile data.size profile)
      assertL3Route path (l3AdaptiveRouteFor data)
        (l3AdaptiveRouteForProfile data.size profile)
      assertL4Route path (l4AdaptiveRouteFor data)
        (l4AdaptiveRouteForProfile data.size profile)
      assertL5Route path (l5AdaptiveRouteFor data)
        (l5AdaptiveRouteForProfile data.size profile)
      assertL6Route path (l6AdaptiveRouteFor data)
        (l6AdaptiveRouteForProfile data.size profile)
      let mut sizes := #[]
      for level in [2, 3, 4, 5, 6] do
        sizes := sizes.push (deflateRaw data level.toUInt8).size
      sizes := sizes.push production.size
      for i in [:sizes.size - 1] do
        unless sizes[i + 1]! ≤ sizes[i]! do
          throw (IO.userError s!"{path} L{i + 2}→L{i + 3} size regressed: {sizes[i]!} → {sizes[i + 1]!}")
      return some sizes
  return none

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

  -- Every profile stays on its exact pre-adaptive pipeline outside the
  -- inclusive 5–64 MiB adaptive band.
  let profiles : List L7Profile := [
    .shallow, .h3Fast, .h3Balanced, .chain64Probe8, .chain64Probe16,
    .chain96Probe16, .chain128Probe16, .chain128Probe32,
    .chain128LongProbe32, .deep
  ]
  for profile in profiles do
    checkAdaptiveRoutes s!"below-gate/{repr profile}" (adaptiveFastTierMinSize - 1)
      profile .current .current .current .current .current
    checkAdaptiveRoutes s!"above-gate/{repr profile}" (adaptiveFastTierMaxSize + 1)
      profile .current .current .current .current .current

  -- Pin every profile's route at the inclusive lower edge.
  let gate := adaptiveFastTierMinSize
  checkAdaptiveRoutes "gate/shallow" gate .shallow
    .level1 .level2 .fast .fast .level7
  checkAdaptiveRoutes "gate/h3Fast" gate .h3Fast
    .level1 .level4 .current .level7 .level7
  checkAdaptiveRoutes "gate/h3Balanced" gate .h3Balanced
    .level1 .fast .fast .fast .level7
  checkAdaptiveRoutes "gate/chain64Probe8" gate .chain64Probe8
    .level1 .fast .fast .fast .fast
  checkAdaptiveRoutes "gate/chain64Probe16" gate .chain64Probe16
    .level1 .fast .level5 .current .level5
  checkAdaptiveRoutes "gate/chain96Probe16" gate .chain96Probe16
    .level1 .fast .fast .fast .fast
  checkAdaptiveRoutes "gate/chain128Probe16" gate .chain128Probe16
    .level1 .level4 .level5 .current .level7
  checkAdaptiveRoutes "gate/chain128Probe32" gate .chain128Probe32
    .current .level4 .level5 .current .level7
  checkAdaptiveRoutes "gate/chain128LongProbe32" gate .chain128LongProbe32
    .level1 .level4 .level5 .level7 .level7
  checkAdaptiveRoutes "gate/deep" gate .deep
    .level1 .level4 .level5 .level7 .level7

  -- The upper edge is inclusive; immediately above it every public adaptive
  -- selector returns its exact pre-adaptive constituent.
  checkAdaptiveRoutes "upper-edge/deep" adaptiveFastTierMaxSize .deep
    .level1 .level4 .level5 .level7 .level7

  -- The L3 7,000,000-byte boundary is deliberately decimal.  The L4–L6
  -- h3-balanced boundary remains binary 20 MiB, and L6's fast band starts at
  -- the former decimal boundary.
  assertL3Route "h3Balanced/6999999"
    (l3AdaptiveRouteForProfile (l3AdaptiveBalancedMaxSize - 1) .h3Balanced) .fast
  assertL3Route "h3Balanced/7000000"
    (l3AdaptiveRouteForProfile l3AdaptiveBalancedMaxSize .h3Balanced) .level2
  assertL4Route "h3Balanced/20MiB-1"
    (l4AdaptiveRouteForProfile (adaptiveBalancedMaxSize - 1) .h3Balanced) .fast
  assertL4Route "h3Balanced/20MiB"
    (l4AdaptiveRouteForProfile adaptiveBalancedMaxSize .h3Balanced) .level5
  assertL5Route "h3Balanced/20MiB-1"
    (l5AdaptiveRouteForProfile (adaptiveBalancedMaxSize - 1) .h3Balanced) .fast
  assertL5Route "h3Balanced/20MiB"
    (l5AdaptiveRouteForProfile adaptiveBalancedMaxSize .h3Balanced) .current
  assertL6Route "h3Balanced/gate"
    (l6AdaptiveRouteForProfile adaptiveFastTierMinSize .h3Balanced) .level7
  assertL6Route "h3Balanced/6999999"
    (l6AdaptiveRouteForProfile (l3AdaptiveBalancedMaxSize - 1) .h3Balanced) .level7
  assertL6Route "h3Balanced/7000000"
    (l6AdaptiveRouteForProfile l3AdaptiveBalancedMaxSize .h3Balanced) .fast
  assertL6Route "h3Balanced/20MiB-1"
    (l6AdaptiveRouteForProfile (adaptiveBalancedMaxSize - 1) .h3Balanced) .fast
  assertL6Route "h3Balanced/20MiB"
    (l6AdaptiveRouteForProfile adaptiveBalancedMaxSize .h3Balanced) .level7

  -- Pin the Silesia profile/size policies even when the optional files are not
  -- downloaded.  These are route goldens, not recomputed sweep choices.
  checkAdaptiveRoutes "silesia/dickens" 10192446 .chain96Probe16
    .level1 .fast .fast .fast .fast
  checkAdaptiveRoutes "silesia/mozilla" 51220480 .h3Balanced
    .level1 .level2 .level5 .current .level7
  checkAdaptiveRoutes "silesia/mr" 9970564 .chain64Probe8
    .level1 .fast .fast .fast .fast
  checkAdaptiveRoutes "silesia/nci" 33553445 .chain128LongProbe32
    .level1 .level4 .level5 .level7 .level7
  checkAdaptiveRoutes "silesia/ooffice" 6152192 .h3Balanced
    .level1 .fast .fast .fast .level7
  checkAdaptiveRoutes "silesia/osdb" 10085684 .shallow
    .level1 .level2 .fast .fast .level7
  checkAdaptiveRoutes "silesia/reymont" 6627202 .chain128Probe16
    .level1 .level4 .level5 .current .level7
  checkAdaptiveRoutes "silesia/samba" 21606400 .chain64Probe16
    .level1 .fast .level5 .current .level5
  checkAdaptiveRoutes "silesia/sao" 7251944 .h3Balanced
    .level1 .level2 .fast .fast .fast
  checkAdaptiveRoutes "silesia/webster" 41458703 .chain128Probe32
    .current .level4 .level5 .current .level7
  checkAdaptiveRoutes "silesia/x-ray" 8474240 .h3Fast
    .level1 .level4 .current .level7 .level7
  checkAdaptiveRoutes "silesia/xml" 5345280 .deep
    .level1 .level4 .level5 .level7 .level7

  -- A below-gate synthetic fixture pins the exact historical output bytes.
  let smallText := mkTextData (64 * 1024)
  unless !incompressiblePrescan smallText do
    throw (IO.userError "small adaptive fixture unexpectedly hit the stored pre-scan")
  assertBytes "small/L2" (deflateRaw smallText 2) (deflateRawBaseF smallText 2)
  assertBytes "small/L3" (deflateRaw smallText 3) (deflateRawBaseF smallText 3)
  assertBytes "small/L4" (deflateRaw smallText 4) (deflateRawBaseF smallText 4)
  assertBytes "small/L5" (deflateRaw smallText 5) (deflateRawSplitLevelP smallText 5)
  assertBytes "small/L6" (deflateRaw smallText 6) (deflateRawSplitLevelP smallText 6)

  -- Literal historical-byte goldens within the bypass band.  Four MiB reaches
  -- L5's chain-22/2016-token policy and L6's ≥1 MiB matcher/split policy while
  -- remaining below the adaptive classifier gate.
  let historicalText := mkTextData (4 * 1024 * 1024)
  unless !incompressiblePrescan historicalText do
    throw (IO.userError "historical adaptive fixture unexpectedly hit the stored pre-scan")
  assertOutputGolden "historical/L5" (deflateRaw historicalText 5) 20496 1741195073
  assertOutputGolden "historical/L6" (deflateRaw historicalText 6) 20496 1741195073

  -- This normal-CI control sits above the gate and is independent of Silesia.
  -- Its low-cardinality text profile traverses representative L1, L4, split-L5,
  -- and retained-profile-L7 constituents through public L2–L6 dispatch.
  let adaptiveText := mkTextData (adaptiveFastTierMinSize + 64 * 1024)
  unless !incompressiblePrescan adaptiveText do
    throw (IO.userError "large adaptive fixture unexpectedly hit the stored pre-scan")
  let adaptiveProfile := l7ProfileFor adaptiveText
  assertProfile "large synthetic text" adaptiveProfile .chain128LongProbe32
  checkAdaptiveRoutes "large synthetic text" adaptiveText.size adaptiveProfile
    .level1 .level4 .level5 .level7 .level7
  assertL2Route "large synthetic text/production" (l2AdaptiveRouteFor adaptiveText) .level1
  assertL3Route "large synthetic text/production" (l3AdaptiveRouteFor adaptiveText) .level4
  assertL4Route "large synthetic text/production" (l4AdaptiveRouteFor adaptiveText) .level5
  assertL5Route "large synthetic text/production" (l5AdaptiveRouteFor adaptiveText) .level7
  assertL6Route "large synthetic text/production" (l6AdaptiveRouteFor adaptiveText) .level7
  let expectedL1 := deflateRawBaseF adaptiveText 1
  let expectedL4 := deflateRawBaseF adaptiveText 4
  let expectedL5 := deflateRawSplitLevelP adaptiveText 5
  let expectedL7 := deflateRawL7P adaptiveText adaptiveProfile
  assertBytes "large/L2" (deflateRaw adaptiveText 2) expectedL1
  assertBytes "large/L3" (deflateRaw adaptiveText 3) expectedL4
  assertBytes "large/L4" (deflateRaw adaptiveText 4) expectedL5
  assertBytes "large/L5" (deflateRaw adaptiveText 5) expectedL7
  assertBytes "large/L6" (deflateRaw adaptiveText 6) expectedL7

  -- A second normal-CI profile pins the shared c8/i12 payload itself and its
  -- selection through three public adaptive levels.
  let fastText := mkAdaptiveAlphabetData (adaptiveFastTierMinSize + 64 * 1024)
  unless !incompressiblePrescan fastText do
    throw (IO.userError "large fast fixture unexpectedly hit the stored pre-scan")
  let fastProfile := l7ProfileFor fastText
  assertProfile "large restricted-alphabet data" fastProfile .h3Balanced
  checkAdaptiveRoutes "large restricted-alphabet data" fastText.size fastProfile
    .level1 .fast .fast .fast .level7
  assertL3Route "large fast/production" (l3AdaptiveRouteFor fastText) .fast
  assertL4Route "large fast/production" (l4AdaptiveRouteFor fastText) .fast
  assertL5Route "large fast/production" (l5AdaptiveRouteFor fastText) .fast
  let expectedFast := deflateRawBaseFNU64 fastText 8 12 258
  assertBytes "large-fast/L3" (deflateRaw fastText 3) expectedFast
  assertBytes "large-fast/L4" (deflateRaw fastText 4) expectedFast
  assertBytes "large-fast/L5" (deflateRaw fastText 5) expectedFast

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
  -- and exact winner-byte identity on every available file. Canterbury is
  -- committed; Silesia is an optional download under the ignored directory.
  -- The aggregate L7 speed/ratio point intentionally does not promise per-file
  -- monotonicity: the selected fast profile makes kennedy and lcet10 0.28% and
  -- 0.32% larger than L6 (203000 vs 202429; 145333 vs 144871).
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
  let mut adaptiveTotals : Array Nat := #[0, 0, 0, 0, 0, 0]
  let mut adaptiveFileCount := 0
  for (file, size, profile, cadence, route, expectedSize) in files do
    assertRoute file (l7OutputRouteFor size profile) route
    if let some sizes ←
        checkFileIfPresent ("bench/corpora/" ++ file) profile cadence route expectedSize then
      adaptiveFileCount := adaptiveFileCount + 1
      for i in [:adaptiveTotals.size] do
        adaptiveTotals := adaptiveTotals.set! i (adaptiveTotals[i]! + sizes[i]!)

  -- With the complete optional corpus present, the aggregate production sizes
  -- must remain monotone across L2–L7.  Partial downloads still exercise every
  -- available file's classifier and selected public dispatch above.
  if adaptiveFileCount == 12 then
    for i in [:adaptiveTotals.size - 1] do
      unless adaptiveTotals[i + 1]! ≤ adaptiveTotals[i]! do
        throw (IO.userError s!"Silesia aggregate L{i + 2}→L{i + 3} regressed: {adaptiveTotals[i]!} → {adaptiveTotals[i + 1]!}")

end ZipTest.L7Adaptive
