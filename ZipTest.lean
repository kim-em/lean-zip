import ZipTest.BenchHelpers
import ZipTest.Zlib
import ZipTest.Gzip
import ZipTest.RawDeflate
import ZipTest.Libdeflate
import ZipTest.Checksum
import ZipTest.Binary
import ZipTest.Tar
import ZipTest.Archive
import ZipTest.ZipFixtures
import ZipTest.TarFixtures
import ZipTest.TarPathTruncation
import ZipTest.CompressFixtures
import ZipTest.Utf8Fixtures
import ZipTest.NativeChecksum
import ZipTest.NativeInflate
import ZipTest.NativeGzip
import ZipTest.NativeIntegration
import ZipTest.NativeScale
import ZipTest.NativeDeflate
import ZipTest.NativeCompressBench
import ZipTest.Benchmark
import ZipTest.FuzzInflate
import ZipTest.BoundedReadTest

def main : IO Unit := do
  unless ← System.FilePath.pathExists "testdata" do
    throw (IO.userError "testdata/ not found — run tests via 'lake test' from the project root")
  ZipTest.Zlib.tests
  ZipTest.Gzip.tests
  ZipTest.RawDeflate.tests
  ZipTest.Libdeflate.tests
  ZipTest.Checksum.tests
  ZipTest.Binary.tests
  ZipTest.Tar.tests
  ZipTest.Archive.tests
  ZipTest.ZipFixtures.tests
  ZipTest.TarFixtures.tests
  ZipTest.TarPathTruncation.tests
  ZipTest.CompressFixtures.tests
  ZipTest.Utf8Fixtures.tests
  ZipTest.NativeChecksum.tests
  ZipTest.NativeInflate.tests
  ZipTest.NativeGzip.tests
  ZipTest.NativeIntegration.tests
  ZipTest.NativeScale.tests
  ZipTest.NativeDeflate.tests
  ZipTest.NativeCompressBench.tests
  ZipTest.Benchmark.tests
  ZipTest.FuzzInflate.tests
  ZipTest.BoundedRead.tests
  IO.println "\nAll tests passed!"
