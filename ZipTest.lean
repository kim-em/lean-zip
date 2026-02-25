import ZipTest.Zlib
import ZipTest.Gzip
import ZipTest.RawDeflate
import ZipTest.Checksum
import ZipTest.Binary
import ZipTest.Tar
import ZipTest.Archive
import ZipTest.Zstd
import ZipTest.ZipFixtures
import ZipTest.TarFixtures
import ZipTest.CompressFixtures
import ZipTest.Utf8Fixtures
import ZipTest.NativeChecksum
import ZipTest.NativeInflate
import ZipTest.NativeGzip
import ZipTest.NativeIntegration
import ZipTest.NativeScale
import ZipTest.NativeDeflate
import ZipTest.NativeCompressBench

def main : IO Unit := do
  unless ← System.FilePath.pathExists "testdata" do
    throw (IO.userError "testdata/ not found — run tests via 'lake test' from the project root")
  ZipTest.Zlib.tests
  ZipTest.Gzip.tests
  ZipTest.RawDeflate.tests
  ZipTest.Checksum.tests
  ZipTest.Binary.tests
  ZipTest.Tar.tests
  ZipTest.Archive.tests
  ZipTest.Zstd.tests
  ZipTest.ZipFixtures.tests
  ZipTest.TarFixtures.tests
  ZipTest.CompressFixtures.tests
  ZipTest.Utf8Fixtures.tests
  ZipTest.NativeChecksum.tests
  ZipTest.NativeInflate.tests
  ZipTest.NativeGzip.tests
  ZipTest.NativeIntegration.tests
  ZipTest.NativeScale.tests
  ZipTest.NativeDeflate.tests
  ZipTest.NativeCompressBench.tests
  IO.println "\nAll tests passed!"
