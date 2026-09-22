import Conformance.NativeChecksum
import Conformance.NativeInflate
import Conformance.InflateFast
import Conformance.NativeGzip
import Conformance.NativeScale
import Conformance.NativeDeflate
import Conformance.OptimalParse
import Conformance.NativeCompressBench
import Conformance.ParallelBench
import Conformance.Benchmark
import Conformance.FuzzInflate

def main : IO Unit := do
  Conformance.NativeChecksum.tests
  Conformance.NativeInflate.tests
  Conformance.InflateFast.tests
  Conformance.NativeGzip.tests
  Conformance.NativeScale.tests
  Conformance.NativeDeflate.tests
  Conformance.OptimalParse.tests
  Conformance.NativeCompressBench.tests
  Conformance.ParallelBench.tests
  Conformance.Benchmark.tests
  Conformance.FuzzInflate.tests
  IO.println "\nAll conformance tests passed!"
