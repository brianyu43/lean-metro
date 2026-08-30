import LeanMetro.SampleMeanVariance

namespace LeanMetro

open Filter ProbabilityTheory
open scoped Topology

/-- A kernel has sample-mean asymptotic variance `σ` for `f` when the actual
finite-path variances, multiplied by their sample sizes, converge to `σ`. -/
def HasSampleMeanAsymptoticVariance
    {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (P : FiniteKernel ι)
    (hπ_nonneg : ∀ x, 0 ≤ π x)
    (hπ_sum : ∑ x, π x = 1)
    (f : ι → ℝ) (σ : ℝ) : Prop :=
  Tendsto
    (fun n => ((n + 1 : ℕ) : ℝ) *
      variance (chainSampleMean f n)
        (stationaryPathMeasure π P hπ_nonneg hπ_sum n))
    atTop (𝓝 σ)

theorem hasSampleMeanAsymptoticVariance_of_poissonCovariance_tendsto
    {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (P : FiniteKernel ι)
    (hπ_nonneg : ∀ x, 0 ≤ π x)
    (hπ_sum : ∑ x, π x = 1)
    (hstat : P.StationaryFor π)
    (hinv : MeanZeroPoissonInvertible π P)
    (f : ι → ℝ) (hf : MeanZero π f)
    (hdecay : Tendsto
      (fun n => weightedInner π f
        (markovIterate P n (poissonSolution π P hinv f hf)))
      atTop (𝓝 0)) :
    HasSampleMeanAsymptoticVariance
      π P hπ_nonneg hπ_sum f
      (algebraicAsymptoticVariance π P hinv f hf) := by
  exact chainSampleMean_scaledVariance_tendsto
    π P hπ_nonneg hπ_sum hstat hinv f hf hdecay

/-- Final probabilistic Peskun theorem. Both kernels have actual sample-mean
variance limits on their finite path probability spaces, and the MH limit is no
larger than the limit for any admissible accept/reject competitor. -/
theorem metropolisHastings_minimizes_sampleMeanAsymptoticVariance
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (w : ι → ℝ) (q a : ι → ι → ℝ)
    (hw : ∀ x, 0 < w x)
    (hq_nonneg : ∀ x y, 0 ≤ q x y)
    (hq_row_sum : ∀ x, ∑ y, q x y = 1)
    (ha : AdmissibleAcceptance w q a)
    (hinvMH : MeanZeroPoissonInvertible
      (normalizedWeight w)
      (metropolisHastingsKernel w q hw hq_nonneg hq_row_sum))
    (hinvA : MeanZeroPoissonInvertible
      (normalizedWeight w)
      (acceptRejectKernel
        q a hq_nonneg hq_row_sum ha.nonneg ha.le_one))
    (f : ι → ℝ) (hf : MeanZero (normalizedWeight w) f)
    (hdecayMH : Tendsto
      (fun n => weightedInner (normalizedWeight w) f
        (markovIterate
          (metropolisHastingsKernel w q hw hq_nonneg hq_row_sum) n
          (poissonSolution
            (normalizedWeight w)
            (metropolisHastingsKernel w q hw hq_nonneg hq_row_sum)
            hinvMH f hf)))
      atTop (𝓝 0))
    (hdecayA : Tendsto
      (fun n => weightedInner (normalizedWeight w) f
        (markovIterate
          (acceptRejectKernel
            q a hq_nonneg hq_row_sum ha.nonneg ha.le_one) n
          (poissonSolution
            (normalizedWeight w)
            (acceptRejectKernel
              q a hq_nonneg hq_row_sum ha.nonneg ha.le_one)
            hinvA f hf)))
      atTop (𝓝 0)) :
    HasSampleMeanAsymptoticVariance
        (normalizedWeight w)
        (metropolisHastingsKernel w q hw hq_nonneg hq_row_sum)
        (normalizedWeight_nonneg w hw)
        (normalizedWeight_sum w hw)
        f
        (algebraicAsymptoticVariance
          (normalizedWeight w)
          (metropolisHastingsKernel w q hw hq_nonneg hq_row_sum)
          hinvMH f hf) ∧
      HasSampleMeanAsymptoticVariance
        (normalizedWeight w)
        (acceptRejectKernel
          q a hq_nonneg hq_row_sum ha.nonneg ha.le_one)
        (normalizedWeight_nonneg w hw)
        (normalizedWeight_sum w hw)
        f
        (algebraicAsymptoticVariance
          (normalizedWeight w)
          (acceptRejectKernel
            q a hq_nonneg hq_row_sum ha.nonneg ha.le_one)
          hinvA f hf) ∧
      algebraicAsymptoticVariance
          (normalizedWeight w)
          (metropolisHastingsKernel w q hw hq_nonneg hq_row_sum)
          hinvMH f hf ≤
        algebraicAsymptoticVariance
          (normalizedWeight w)
          (acceptRejectKernel
            q a hq_nonneg hq_row_sum ha.nonneg ha.le_one)
          hinvA f hf := by
  constructor
  · exact hasSampleMeanAsymptoticVariance_of_poissonCovariance_tendsto
      (normalizedWeight w)
      (metropolisHastingsKernel w q hw hq_nonneg hq_row_sum)
      (normalizedWeight_nonneg w hw)
      (normalizedWeight_sum w hw)
      (metropolisHastingsKernel_stationary
        w q hw hq_nonneg hq_row_sum)
      hinvMH f hf hdecayMH
  constructor
  · exact hasSampleMeanAsymptoticVariance_of_poissonCovariance_tendsto
      (normalizedWeight w)
      (acceptRejectKernel
        q a hq_nonneg hq_row_sum ha.nonneg ha.le_one)
      (normalizedWeight_nonneg w hw)
      (normalizedWeight_sum w hw)
      (admissibleAcceptRejectReversibleKernel
        w q a hq_nonneg hq_row_sum ha).stationary
      hinvA f hf hdecayA
  · exact metropolisHastings_minimizes_algebraicAsymptoticVariance
      w q a hw hq_nonneg hq_row_sum ha hinvMH hinvA f hf

end LeanMetro
