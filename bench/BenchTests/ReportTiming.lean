import Bench.ReportTiming

/-! Sentinel tests for the Track D dashboard timing contract. -/

namespace ZipTest.ReportTiming

def tests : IO Unit := do
  assert! Bench.dashboardTiming.aggregation == "median"
  assert! Bench.dashboardTiming.repetitions == 5
  assert! Bench.singleRepArtifactTiming.aggregation == "single"
  assert! Bench.singleRepArtifactTiming.repetitions == 1
  IO.println "Report timing policy tests: OK"

end ZipTest.ReportTiming
