import LeanMetro.StationaryMoments
import Mathlib.Probability.Moments.Variance

namespace LeanMetro

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

/-- The empirical mean of an observable along a path of `n + 1` states. -/
noncomputable def chainSampleMean
    {ι : Type*} (f : ι → ℝ) (n : ℕ) (p : ChainPath ι n) : ℝ :=
  (((n + 1 : ℕ) : ℝ)⁻¹) * chainPathSum f p

theorem chainPathSum_aemeasurable
    {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (P : FiniteKernel ι)
    (hπ_nonneg : ∀ x, 0 ≤ π x)
    (hπ_sum : ∑ x, π x = 1)
    (f : ι → ℝ) (n : ℕ) :
    AEMeasurable (chainPathSum f : ChainPath ι n → ℝ)
      (stationaryPathMeasure π P hπ_nonneg hπ_sum n) := by
  exact Measurable.of_discrete.aemeasurable

theorem chainSampleMean_aemeasurable
    {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (P : FiniteKernel ι)
    (hπ_nonneg : ∀ x, 0 ≤ π x)
    (hπ_sum : ∑ x, π x = 1)
    (f : ι → ℝ) (n : ℕ) :
    AEMeasurable (chainSampleMean f n)
      (stationaryPathMeasure π P hπ_nonneg hπ_sum n) := by
  exact Measurable.of_discrete.aemeasurable

theorem chainPathSum_integral_eq_zero
    {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (P : FiniteKernel ι)
    (hπ_nonneg : ∀ x, 0 ≤ π x)
    (hπ_sum : ∑ x, π x = 1)
    (hstat : P.StationaryFor π)
    (f : ι → ℝ) (hf : MeanZero π f) (n : ℕ) :
    ∫ p, chainPathSum f p
        ∂(stationaryPathMeasure π P hπ_nonneg hπ_sum n) = 0 := by
  change stationaryPathExpectation π P hπ_nonneg hπ_sum n
      (chainPathSum f) = 0
  rw [stationaryPath_sum_expectation π P hπ_nonneg hπ_sum hstat f n]
  rw [hf, mul_zero]

theorem chainSampleMean_integral_eq_zero
    {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (P : FiniteKernel ι)
    (hπ_nonneg : ∀ x, 0 ≤ π x)
    (hπ_sum : ∑ x, π x = 1)
    (hstat : P.StationaryFor π)
    (f : ι → ℝ) (hf : MeanZero π f) (n : ℕ) :
    ∫ p, chainSampleMean f n p
        ∂(stationaryPathMeasure π P hπ_nonneg hπ_sum n) = 0 := by
  unfold chainSampleMean
  rw [integral_const_mul]
  rw [chainPathSum_integral_eq_zero
    π P hπ_nonneg hπ_sum hstat f hf n, mul_zero]

/-- For a centered observable, the variance of the path sum is its second
moment, and hence has the exact stationary covariance expansion. -/
theorem chainPathSum_variance_eq
    {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (P : FiniteKernel ι)
    (hπ_nonneg : ∀ x, 0 ≤ π x)
    (hπ_sum : ∑ x, π x = 1)
    (hstat : P.StationaryFor π)
    (f : ι → ℝ) (hf : MeanZero π f) (n : ℕ) :
    variance (chainPathSum f : ChainPath ι n → ℝ)
        (stationaryPathMeasure π P hπ_nonneg hπ_sum n) =
      ((n + 1 : ℕ) : ℝ) * weightedInner π f f +
        2 * ∑ k ∈ Finset.range n,
          ((n : ℝ) - (k : ℝ)) * lagCovariance π P f (k + 1) := by
  rw [variance_of_integral_eq_zero
    (chainPathSum_aemeasurable π P hπ_nonneg hπ_sum f n)
    (chainPathSum_integral_eq_zero
      π P hπ_nonneg hπ_sum hstat f hf n)]
  change stationaryPathExpectation π P hπ_nonneg hπ_sum n
      (fun p => (chainPathSum f p) ^ 2) = _
  exact stationaryPath_sum_secondMoment
    π P hπ_nonneg hπ_sum hstat f n

/-- Exact finite-time bridge: the scaled variance of the actual empirical mean
on the path probability space is the covariance expression from Phase 6a. -/
theorem chainSampleMean_scaledVariance_eq
    {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (P : FiniteKernel ι)
    (hπ_nonneg : ∀ x, 0 ≤ π x)
    (hπ_sum : ∑ x, π x = 1)
    (hstat : P.StationaryFor π)
    (f : ι → ℝ) (hf : MeanZero π f) (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) *
        variance (chainSampleMean f n)
          (stationaryPathMeasure π P hπ_nonneg hπ_sum n) =
      stationaryScaledVariance π P f n := by
  unfold chainSampleMean
  rw [variance_const_mul]
  rw [chainPathSum_variance_eq
    π P hπ_nonneg hπ_sum hstat f hf n]
  unfold stationaryScaledVariance
  have hsample : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp

/-- The actual scaled sample-mean variance converges to the algebraic
asymptotic variance under the explicit Poisson-covariance decay assumption. -/
theorem chainSampleMean_scaledVariance_tendsto
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
      π P hπ_nonneg hπ_sum hstat f hf n
  rw [heq]
  exact stationaryScaledVariance_tendsto_algebraicAsymptoticVariance
    π P hinv f hf hdecay

end LeanMetro
