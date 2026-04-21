import ZipTest.Helpers

/-! Tests for ZIP archive creation, listing, and extraction with compression method selection. -/

def ZipTest.Archive.tests : IO Unit := do
  -- Create test files
  let zipTestDir : System.FilePath := "/tmp/lean-zlib-zip-test"
  if ← zipTestDir.pathExists then
    let _ ← IO.Process.run { cmd := "rm", args := #["-rf", zipTestDir.toString] }
  IO.FS.createDirAll (zipTestDir / "sub")
  IO.FS.writeFile (zipTestDir / "hello.txt") "Hello from ZIP!"
  IO.FS.writeFile (zipTestDir / "sub" / "data.txt") "Some nested data for compression testing."
  -- Compressible data (should use deflate method 8)
  let mut compressible := ByteArray.empty
  for _ in [:100] do
    compressible := compressible ++ "Repeated text for compression. ".toUTF8
  IO.FS.writeBinFile (zipTestDir / "big.bin") compressible
  IO.FS.writeFile (zipTestDir / "empty.txt") ""

  -- Create ZIP from explicit file list
  let zipPath : System.FilePath := "/tmp/lean-zlib-test.zip"
  Archive.create zipPath #[
    ("hello.txt", zipTestDir / "hello.txt"),
    ("sub/data.txt", zipTestDir / "sub" / "data.txt"),
    ("big.bin", zipTestDir / "big.bin"),
    ("empty.txt", zipTestDir / "empty.txt")
  ]

  -- List entries
  let zipEntries ← Archive.list zipPath
  unless zipEntries.size == 4 do throw (IO.userError s!"zip list: expected 4, got {zipEntries.size}")
  -- Check method selection: big.bin should be deflated (method 8)
  let bigEntry := zipEntries.find? (·.path == "big.bin")
  match bigEntry with
  | some e =>
    unless e.method == 8 do throw (IO.userError s!"zip: big.bin should be deflated, got method {e.method}")
    unless e.compressedSize < e.uncompressedSize do
      throw (IO.userError "zip: big.bin compressed should be smaller")
  | none => throw (IO.userError "zip: big.bin not found in listing")

  -- Extract and verify roundtrip
  let zipExtractDir : System.FilePath := "/tmp/lean-zlib-zip-extract"
  if ← zipExtractDir.pathExists then
    let _ ← IO.Process.run { cmd := "rm", args := #["-rf", zipExtractDir.toString] }
  IO.FS.createDirAll zipExtractDir
  Archive.extract zipPath zipExtractDir
  let zHello ← IO.FS.readFile (zipExtractDir / "hello.txt")
  unless zHello == "Hello from ZIP!" do throw (IO.userError s!"zip extract hello: {zHello}")
  let zData ← IO.FS.readFile (zipExtractDir / "sub" / "data.txt")
  unless zData == "Some nested data for compression testing." do
    throw (IO.userError s!"zip extract data: {zData}")
  let zBig ← IO.FS.readBinFile (zipExtractDir / "big.bin")
  unless zBig.beq compressible do
    throw (IO.userError s!"zip extract big: content mismatch (sizes: {zBig.size} vs {compressible.size})")
  let zEmpty ← IO.FS.readFile (zipExtractDir / "empty.txt")
  unless zEmpty == "" do throw (IO.userError "zip extract empty")

  -- extractFile by name
  let singleFile ← Archive.extractFile zipPath "hello.txt"
  unless String.fromUTF8! singleFile == "Hello from ZIP!" do
    throw (IO.userError "zip extractFile")

  -- createFromDir roundtrip
  let zipFromDirPath : System.FilePath := "/tmp/lean-zlib-test-fromdir.zip"
  Archive.createFromDir zipFromDirPath zipTestDir
  let dirEntries ← Archive.list zipFromDirPath
  unless dirEntries.size == 4 do
    throw (IO.userError s!"zip createFromDir: expected 4, got {dirEntries.size}")
  let zipFromDirExtract : System.FilePath := "/tmp/lean-zlib-zip-fromdir-extract"
  if ← zipFromDirExtract.pathExists then
    let _ ← IO.Process.run { cmd := "rm", args := #["-rf", zipFromDirExtract.toString] }
  IO.FS.createDirAll zipFromDirExtract
  Archive.extract zipFromDirPath zipFromDirExtract
  let zHello2 ← IO.FS.readFile (zipFromDirExtract / "hello.txt")
  unless zHello2 == "Hello from ZIP!" do throw (IO.userError "zip fromDir hello")

  -- Central directory size limit
  let cdLimitResult ← (Archive.list zipPath (maxCentralDirSize := 10)).toBaseIO
  match cdLimitResult with
  | .ok _ => throw (IO.userError "zip: CD size limit should have been rejected")
  | .error e =>
    unless (toString e).contains "central directory too large" do
      throw (IO.userError s!"zip: CD size limit wrong error: {e}")

  -- maxEntrySize bomb regression: an uncompressedSize larger than the limit
  -- must be rejected before any decompression happens (Zip/Archive.lean:408-410).
  let bombSrcDir : System.FilePath := "/tmp/lean-zlib-zip-bomb-src"
  let bombZipPath : System.FilePath := "/tmp/lean-zlib-zip-bomb.zip"
  let bombExtractDir : System.FilePath := "/tmp/lean-zlib-zip-bomb-extract"
  if ← bombSrcDir.pathExists then
    let _ ← IO.Process.run { cmd := "rm", args := #["-rf", bombSrcDir.toString] }
  IO.FS.createDirAll bombSrcDir
  let bombPayload ← mkTestData  -- 6200 bytes, well above the 100-byte threshold
  IO.FS.writeBinFile (bombSrcDir / "bomb.txt") bombPayload
  Archive.create bombZipPath #[("bomb.txt", bombSrcDir / "bomb.txt")]
  if ← bombExtractDir.pathExists then
    let _ ← IO.Process.run { cmd := "rm", args := #["-rf", bombExtractDir.toString] }
  IO.FS.createDirAll bombExtractDir
  let extractBombResult ←
    (Archive.extract bombZipPath bombExtractDir (maxEntrySize := 10)).toBaseIO
  match extractBombResult with
  | .ok _ => throw (IO.userError "zip: maxEntrySize bomb should have been rejected by extract")
  | .error e =>
    unless (toString e).contains "exceeds limit" do
      throw (IO.userError s!"zip: maxEntrySize bomb wrong error from extract: {e}")
  let extractFileBombResult ←
    (Archive.extractFile bombZipPath "bomb.txt" (maxEntrySize := 10)).toBaseIO
  match extractFileBombResult with
  | .ok _ => throw (IO.userError "zip: maxEntrySize bomb should have been rejected by extractFile")
  | .error e =>
    unless (toString e).contains "exceeds limit" do
      throw (IO.userError s!"zip: maxEntrySize bomb wrong error from extractFile: {e}")
  let _ ← IO.Process.run { cmd := "rm", args := #["-rf", bombSrcDir.toString] }
  let _ ← IO.Process.run { cmd := "rm", args := #["-rf", bombExtractDir.toString] }
  let _ ← IO.Process.run { cmd := "rm", args := #["-f", bombZipPath.toString] }

  -- readExactStream with fragmenting stream (Bug #1: short read robustness)
  let testPayload := "Hello, World! This is test data for readExactStream.".toUTF8
  let fragStream := fragmentingStream (← byteArrayReadStream testPayload) 3
  let result ← Archive.readExactStream fragStream testPayload.size "fragmenting test"
  unless result.beq testPayload do
    throw (IO.userError "readExactStream: content mismatch with fragmenting stream (3-byte chunks)")
  -- Also test with 1-byte fragments
  let fragStream1 := fragmentingStream (← byteArrayReadStream testPayload) 1
  let result1 ← Archive.readExactStream fragStream1 testPayload.size "fragmenting test (1-byte)"
  unless result1.beq testPayload do
    throw (IO.userError "readExactStream: content mismatch with fragmenting stream (1-byte chunks)")

  -- Clean up zip temps
  let _ ← IO.Process.run { cmd := "rm", args := #["-rf", zipTestDir.toString] }
  let _ ← IO.Process.run { cmd := "rm", args := #["-rf", zipExtractDir.toString] }
  let _ ← IO.Process.run { cmd := "rm", args := #["-rf", zipFromDirExtract.toString] }
  let _ ← IO.Process.run { cmd := "rm", args := #["-f", zipPath.toString] }
  let _ ← IO.Process.run { cmd := "rm", args := #["-f", zipFromDirPath.toString] }
  IO.println "Archive tests: OK"
