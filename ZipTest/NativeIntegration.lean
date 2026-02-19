import ZipTest.Helpers

def ZipTest.NativeIntegration.tests : IO Unit := do
  IO.println "  NativeIntegration tests..."
  -- === ZIP native extraction ===

  -- Create test files with FFI compression
  let zipTestDir : System.FilePath := "/tmp/lean-zip-native-int-test"
  if ← zipTestDir.pathExists then
    let _ ← IO.Process.run { cmd := "rm", args := #["-rf", zipTestDir.toString] }
  IO.FS.createDirAll (zipTestDir / "sub")
  IO.FS.writeFile (zipTestDir / "hello.txt") "Hello from native integration!"
  IO.FS.writeFile (zipTestDir / "sub" / "nested.txt") "Nested file for native decompression."

  -- Compressible data (will use deflate method 8)
  let mut compressible := ByteArray.empty
  for _ in [:200] do
    compressible := compressible ++ "Repeated content for native integration test. ".toUTF8
  IO.FS.writeBinFile (zipTestDir / "big.bin") compressible
  IO.FS.writeFile (zipTestDir / "empty.txt") ""

  -- Create ZIP archive using FFI
  let zipPath : System.FilePath := "/tmp/lean-zip-native-int.zip"
  Archive.create zipPath #[
    ("hello.txt", zipTestDir / "hello.txt"),
    ("sub/nested.txt", zipTestDir / "sub" / "nested.txt"),
    ("big.bin", zipTestDir / "big.bin"),
    ("empty.txt", zipTestDir / "empty.txt")
  ]

  -- Extract with native backend
  let nativeExtDir : System.FilePath := "/tmp/lean-zip-native-int-extract"
  if ← nativeExtDir.pathExists then
    let _ ← IO.Process.run { cmd := "rm", args := #["-rf", nativeExtDir.toString] }
  IO.FS.createDirAll nativeExtDir
  Archive.extract zipPath nativeExtDir (useNative := true)

  -- Verify extracted files match originals
  let nHello ← IO.FS.readFile (nativeExtDir / "hello.txt")
  unless nHello == "Hello from native integration!" do
    throw (IO.userError s!"native zip extract hello: got '{nHello}'")
  let nNested ← IO.FS.readFile (nativeExtDir / "sub" / "nested.txt")
  unless nNested == "Nested file for native decompression." do
    throw (IO.userError s!"native zip extract nested: got '{nNested}'")
  let nBig ← IO.FS.readBinFile (nativeExtDir / "big.bin")
  unless nBig.beq compressible do
    throw (IO.userError s!"native zip extract big: size mismatch ({nBig.size} vs {compressible.size})")
  let nEmpty ← IO.FS.readFile (nativeExtDir / "empty.txt")
  unless nEmpty == "" do throw (IO.userError "native zip extract empty")

  -- extractFile with native backend
  let singleNative ← Archive.extractFile zipPath "big.bin" (useNative := true)
  unless singleNative.beq compressible do
    throw (IO.userError "native zip extractFile big.bin mismatch")
  let singleHello ← Archive.extractFile zipPath "hello.txt" (useNative := true)
  unless String.fromUTF8! singleHello == "Hello from native integration!" do
    throw (IO.userError "native zip extractFile hello.txt mismatch")

  -- === tar.gz native extraction ===

  -- Create a tar.gz using FFI
  let tarGzPath : System.FilePath := "/tmp/lean-zip-native-int.tar.gz"
  Tar.createTarGz tarGzPath zipTestDir

  -- Extract with native backend
  let tarNativeDir : System.FilePath := "/tmp/lean-zip-native-int-tar-extract"
  if ← tarNativeDir.pathExists then
    let _ ← IO.Process.run { cmd := "rm", args := #["-rf", tarNativeDir.toString] }
  IO.FS.createDirAll tarNativeDir
  Tar.extractTarGzNative tarGzPath tarNativeDir

  -- Verify extracted files
  let tHello ← IO.FS.readFile (tarNativeDir / "hello.txt")
  unless tHello == "Hello from native integration!" do
    throw (IO.userError s!"native tar.gz extract hello: got '{tHello}'")
  let tNested ← IO.FS.readFile (tarNativeDir / "sub" / "nested.txt")
  unless tNested == "Nested file for native decompression." do
    throw (IO.userError s!"native tar.gz extract nested: got '{tNested}'")
  let tBig ← IO.FS.readBinFile (tarNativeDir / "big.bin")
  unless tBig.beq compressible do
    throw (IO.userError s!"native tar.gz extract big: size mismatch ({tBig.size} vs {compressible.size})")
  let tEmpty ← IO.FS.readFile (tarNativeDir / "empty.txt")
  unless tEmpty == "" do throw (IO.userError "native tar.gz extract empty")

  -- Clean up
  let _ ← IO.Process.run { cmd := "rm", args := #["-rf", zipTestDir.toString] }
  let _ ← IO.Process.run { cmd := "rm", args := #["-rf", nativeExtDir.toString] }
  let _ ← IO.Process.run { cmd := "rm", args := #["-rf", tarNativeDir.toString] }
  let _ ← IO.Process.run { cmd := "rm", args := #["-f", zipPath.toString] }
  let _ ← IO.Process.run { cmd := "rm", args := #["-f", tarGzPath.toString] }
  IO.println "  NativeIntegration tests passed."
