import ZipTest.Binary
import ZipTest.Wide
import ZipTest.ExtendWithin
import ZipTest.InflateTable
import ZipTest.PackedTokens
import ZipTest.PackedHeads
import ZipTest.SizeHelpers
import ZipTest.L7Adaptive
import ZipTest.Parallel

def main : IO Unit := do
  ZipTest.Binary.tests
  ZipTest.Wide.tests
  ZipTest.ExtendWithin.tests
  ZipTest.InflateTable.tests
  ZipTest.InflateTable.canonicalTests
  ZipTest.InflateTable.subtableTests
  ZipTest.PackedTokens.tests
  ZipTest.PackedHeads.tests
  ZipTest.SizeHelpers.tests
  ZipTest.L7Adaptive.tests
  ZipTest.Parallel.tests
  IO.println "\nAll tests passed!"
