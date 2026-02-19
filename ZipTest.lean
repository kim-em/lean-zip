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
  IO.println "\nAll tests passed!"
