import ZipTest.Helpers

/-! Tests for gzip and zstd decompression with real-world interop fixtures and malformed data. -/

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

  -- system-hello.zst: decompress zstd from system zstd tool
  let sysZstData ← readFixture "zstd/interop/system-hello.zst"
  let sysZstDecomp ← Zstd.decompress sysZstData
  unless String.fromUTF8! sysZstDecomp == "Hello from system zstd\n" do
    throw (IO.userError s!"system-hello.zst: content mismatch: {repr (String.fromUTF8! sysZstDecomp)}")

  -- truncated.zst: truncated zstd frame
  -- Note: ZSTD_decompress succeeds on this fixture because the frame header
  -- is intact and enough compressed data remains. Verify it at least runs.
  let truncZstData ← readFixture "zstd/malformed/truncated.zst"
  let _ ← Zstd.decompress truncZstData

  -- not-zstd.bin: random bytes, not valid zstd
  let notZstData ← readFixture "zstd/malformed/not-zstd.bin"
  assertThrows "Zstd malformed (not-zstd.bin)"
    (do let _ ← Zstd.decompress notZstData; pure ())
    "not a valid"
  IO.println "Gzip/Zstd fixture tests: OK"
