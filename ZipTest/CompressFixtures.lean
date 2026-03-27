import ZipTest.Helpers

/-! Tests for gzip decompression with real-world interop fixtures and malformed data. -/

def ZipTest.CompressFixtures.tests : IO Unit := do
  -- system-hello.gz: decompress gzip from system gzip tool
  let sysGzData ← readFixture "gzip/interop/system-hello.gz"
  let sysGzDecomp ← Gzip.decompress sysGzData
  unless String.fromUTF8! sysGzDecomp == "Hello from system gzip\n" do
    throw (IO.userError s!"system-hello.gz: content mismatch: {repr (String.fromUTF8! sysGzDecomp)}")

  -- two-members.gz: concatenated gzip from Haskell zlib
  let twoMembersData ← readFixture "gzip/interop/two-members.gz"
  let twoMembersDecomp ← Gzip.decompress twoMembersData
  unless String.fromUTF8! twoMembersDecomp == "Test 1Test 2" do
    throw (IO.userError s!"two-members.gz: content mismatch: {repr (String.fromUTF8! twoMembersDecomp)}")

  -- bad-crc.gz: gzip with wrong CRC
  let badCrcGzData ← readFixture "gzip/malformed/bad-crc.gz"
  assertThrows "Gzip malformed (bad-crc.gz)"
    (do let _ ← Gzip.decompress badCrcGzData; pure ())
    "incorrect data check"

  -- truncated.gz: truncated deflate stream
  let truncGzData ← readFixture "gzip/malformed/truncated.gz"
  assertThrows "Gzip malformed (truncated.gz)"
    (do let _ ← Gzip.decompress truncGzData; pure ())
    "buffer error"

  IO.println "Gzip fixture tests: OK"
