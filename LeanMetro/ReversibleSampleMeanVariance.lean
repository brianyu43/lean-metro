import LeanMetro.SampleMeanVariance
import LeanMetro.ReversibleVarianceLimit

namespace LeanMetro

open Filter ProbabilityTheory
open scoped Topology

/-- Actual stationary sample-mean variances inherit the decay-free reversible
limit from the exact finite-path variance identity. -/
theorem chainSampleMean_scaledVariance_tendsto_of_reversible
    {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (P : FiniteKernel ι)
    (hπ_nonneg : ∀ x, 0 ≤ π x)
    (hπ_sum : ∑ x, π x = 1)
    (hrev : P.ReversibleFor π)
    (hinv : MeanZeroPoissonInvertible π P)
    (f : ι → ℝ) (hf : MeanZero π f) :
    Tendsto
      (fun n => ((n + 1 : ℕ) : ℝ) *
        variance (chainSampleMean f n)
          (stationaryPathMeasure π P hπ_nonneg hπ_sum n))
      atTop (𝓝 (algebraicAsymptoticVariance π P hinv f hf)) := by
  have heq :
      (fun n => ((n + 1 : ℕ) : ℝ) *
        variance (chainSampleMean f n)
          (stationaryPathMeasure π P hπ_nonneg hπ_sum n)) =
        stationaryScaledVariance π P f := by
    funext n
    exact chainSampleMean_scaledVariance_eq
      π P hπ_nonneg hπ_sum hrev.stationary f hf n
  rw [heq]
  exact stationaryScaledVariance_tendsto_algebraicAsymptoticVariance_of_reversible
    π P hrev hinv f hf

end LeanMetro
