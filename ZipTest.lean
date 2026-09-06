module

public import ZipTest.Binary
public import ZipTest.Wide
public import ZipTest.ExtendWithin
public import ZipTest.InflateTable
public import ZipTest.PackedTokens
public import ZipTest.PackedHeads
public import ZipTest.SizeHelpers
public import ZipTest.L7Adaptive

public section

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
  IO.println "\nAll tests passed!"
