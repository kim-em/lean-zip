import ZipTest.Helpers

/-! Regression tests for codepoint-boundary truncation of UTF-8 paths in
    the tar writer (`Tar.truncateUTF8`) and for the end-to-end writer/
    reader round-trip when a path's 80th or 100th byte lands inside a
    multibyte sequence (Track E Priority 1, item 1). -/

namespace ZipTest.TarPathTruncation

private def assertEq (label : String) (expected actual : String) : IO Unit := do
  unless expected == actual do
    throw (IO.userError s!"{label}: expected {repr expected}, got {repr actual}")

def tests : IO Unit := do
  -- Unit checks: truncateUTF8 respects codepoint boundaries.
  assertEq "truncateUTF8 ASCII short"  "hello"  (Tar.truncateUTF8 "hello" 10)
  assertEq "truncateUTF8 ASCII exact"  "abc"    (Tar.truncateUTF8 "abc" 3)
  assertEq "truncateUTF8 ASCII cut"    "ab"     (Tar.truncateUTF8 "abc" 2)
  assertEq "truncateUTF8 zero"         ""       (Tar.truncateUTF8 "café" 0)
  -- "café" is 5 UTF-8 bytes: c(1) a(1) f(1) é(2). A raw byte cut at 4
  -- would split 'é'; truncateUTF8 must stop before it.
  assertEq "truncateUTF8 café/4" "caf"  (Tar.truncateUTF8 "café" 4)
  assertEq "truncateUTF8 café/3" "caf"  (Tar.truncateUTF8 "café" 3)
  assertEq "truncateUTF8 café/5" "café" (Tar.truncateUTF8 "café" 5)

  -- Boundary-straddle: place 'é' so its first byte sits at position 79,
  -- i.e. cutting at 80 bytes would split the sequence.
  let head79 := String.ofList (List.replicate 79 'a')
  let straddle80 := head79 ++ "é" ++ String.ofList (List.replicate 40 'b')
  unless straddle80.utf8ByteSize > 80 do
    throw (IO.userError "straddle80: unexpected byte size")
  let t80 := Tar.truncateUTF8 straddle80 80
  assertEq "truncateUTF8 80-byte straddle" head79 t80
  unless t80.utf8ByteSize ≤ 80 do
    throw (IO.userError s!"truncateUTF8: produced {t80.utf8ByteSize} bytes (> 80)")
  unless (String.fromUTF8? t80.toUTF8).isSome do
    throw (IO.userError "truncateUTF8: result is not valid UTF-8")

  -- Same straddle at the 100-byte boundary used by the PAX placeholder.
  let head99 := String.ofList (List.replicate 99 'a')
  let straddle100 := head99 ++ "é" ++ String.ofList (List.replicate 40 'b')
  let t100 := Tar.truncateUTF8 straddle100 100
  assertEq "truncateUTF8 100-byte straddle" head99 t100
  unless t100.utf8ByteSize ≤ 100 do
    throw (IO.userError "truncateUTF8: 100-byte straddle exceeded max")

  -- buildPaxEntry: a path whose 80th byte lands inside a multibyte
  -- sequence. Previously this panicked through `String.fromUTF8!` on
  -- `paxName`'s UStar placeholder. The header must now emerge intact
  -- and the UStar name field must parse as valid UTF-8.
  let longPath := head79 ++ "é" ++ String.ofList (List.replicate 20 'c') ++ ".txt"
  let block ← Tar.buildPaxEntry ByteArray.empty longPath
  unless block.size == 512 do
    throw (IO.userError s!"buildPaxEntry: expected 512-byte block, got {block.size}")
  let placeholderName := Binary.readString block 0 100
  unless placeholderName.startsWith "PaxHeader/" do
    throw (IO.userError s!"buildPaxEntry: UStar name missing PaxHeader/ prefix: {placeholderName}")
  unless (String.fromUTF8? placeholderName.toUTF8).isSome do
    throw (IO.userError "buildPaxEntry: placeholder is not valid UTF-8")

  -- End-to-end round-trip via createFromDir + list. Build a file whose
  -- relative path's 100th byte falls inside a multibyte sequence and
  -- verify the decoder recovers the exact original path through the
  -- PAX extended header.
  let tmpDir : System.FilePath := "/tmp/lean-zip-tar-utf8-truncate"
  if ← tmpDir.pathExists then
    let _ ← IO.Process.run { cmd := "rm", args := #["-rf", tmpDir.toString] }
  IO.FS.createDirAll tmpDir
  let relName := head99 ++ "é" ++ String.ofList (List.replicate 20 'w') ++ ".txt"
  IO.FS.writeFile (tmpDir / relName) "content"
  let tarPath : System.FilePath := "/tmp/lean-zip-tar-utf8-truncate.tar"
  IO.FS.withFile tarPath .write fun outH =>
    Tar.createFromDir (IO.FS.Stream.ofHandle outH) tmpDir
  let entries ← IO.FS.withFile tarPath .read fun h =>
    Tar.list (IO.FS.Stream.ofHandle h)
  unless entries.any (·.path == relName) do
    let paths := entries.map (·.path)
    throw (IO.userError s!"round-trip: expected path preserved, got {paths}")
  let _ ← IO.Process.run { cmd := "rm", args := #["-rf", tmpDir.toString] }
  let _ ← IO.Process.run { cmd := "rm", args := #["-f", tarPath.toString] }

  IO.println "Tar path truncation tests: OK"

end ZipTest.TarPathTruncation
