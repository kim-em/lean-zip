import ZipTest.Helpers
import Zip.Native.DeflateDynamic

/-! Golden tests for the level-7 content-profile selector.

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

def checkSmall (name : String) (size runs : Nat) (expected : L7Profile) : IO Unit :=
  assertProfile name (l7ClassifySmall size runs) expected

def checkLarge (name : String) (minUnique meanUnique maxUnique : Nat)
    (expected : L7Profile) : IO Unit :=
  assertProfile name (l7ClassifyLarge minUnique meanUnique maxUnique) expected

def checkFileIfPresent (path : String) (expected : L7Profile) : IO Unit := do
  if ← System.FilePath.pathExists path then
    let data ← IO.FS.readBinFile path
    assertProfile path (l7ProfileFor data) expected

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

  -- Exercise extraction on every available corpus file.  Canterbury is
  -- committed; Silesia is an optional download under the ignored directory.
  let files : List (String × L7Profile) := [
    ("canterbury/alice29.txt", .chain64Probe8),
    ("canterbury/asyoulik.txt", .shallow),
    ("canterbury/cp.html", .chain64Probe16),
    ("canterbury/fields.c", .chain64Probe16),
    ("canterbury/grammar.lsp", .chain64Probe16),
    ("canterbury/kennedy.xls", .shallow),
    ("canterbury/lcet10.txt", .shallow),
    ("canterbury/plrabn12.txt", .shallow),
    ("canterbury/ptt5", .chain128Probe16),
    ("canterbury/sum", .h3Fast),
    ("canterbury/xargs.1", .chain64Probe16),
    ("silesia/dickens", .chain96Probe16),
    ("silesia/mozilla", .h3Balanced),
    ("silesia/mr", .chain64Probe8),
    ("silesia/nci", .chain128LongProbe32),
    ("silesia/ooffice", .h3Balanced),
    ("silesia/osdb", .shallow),
    ("silesia/reymont", .chain128Probe16),
    ("silesia/samba", .chain64Probe16),
    ("silesia/sao", .h3Balanced),
    ("silesia/webster", .chain128Probe32),
    ("silesia/x-ray", .h3Fast),
    ("silesia/xml", .deep)
  ]
  for (file, expected) in files do
    checkFileIfPresent ("bench/corpora/" ++ file) expected

end ZipTest.L7Adaptive
