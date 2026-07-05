import BenchTests.MinizOxide
import BenchTests.Libdeflate
import BenchTests.Zopfli
import BenchTests.FuzzInflate
import BenchTests.FuzzCompress
import BenchTests.FuzzHandleRead

/-! Dev-only conformance + fuzz test driver for the Track D comparators.

These modules moved out of the root `test` driver together with the
comparator `extern_lib`s they need. Each comparator test self-skips (via
its `"<name>: not built with"` marker) when the comparator toolchain is
absent, so this driver stays green on minimal toolchains; with cargo /
libdeflate / zopfli present it exercises the real comparators. The three
fuzz modules run their default (short) budgets — the dedicated
`fuzz_inflate` / `fuzz_handle_read` executables run the longer budgeted
sweeps. -/

def main : IO Unit := do
  ZipTest.MinizOxide.tests
  ZipTest.Libdeflate.tests
  ZipTest.Zopfli.tests
  ZipTest.FuzzInflate.tests
  ZipTest.FuzzCompress.tests
  ZipTest.FuzzHandleRead.tests
  IO.println "\nAll bench tests passed!"
