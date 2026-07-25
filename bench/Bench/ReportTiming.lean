/-! Shared timing policies for the Track D benchmark reports.

Routine dashboard data has one protocol: median-of-5. Keep the repetition
count here so the measurement loop, JSON provenance, and tests cannot drift
independently. The frozen zopfli ceiling is the sole one-repetition exception;
its speed is explicitly an artifact rather than benchmark evidence. -/

namespace Bench

structure TimingPolicy where
  aggregation : String
  repetitions : Nat

/-- Timing policy for every routine dashboard measurement. -/
def dashboardTiming : TimingPolicy :=
  { aggregation := "median", repetitions := 5 }

/-- Timing policy for the frozen, ratio-only zopfli artifact. -/
def singleRepArtifactTiming : TimingPolicy :=
  { aggregation := "single", repetitions := 1 }

end Bench
