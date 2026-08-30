import LeanMetro.ProbabilisticPeskun
import LeanMetro.VarianceLimitExample

namespace LeanMetro

open Filter
open scoped Topology

theorem three_state_stationary_nonneg :
    ∀ x, 0 ≤ threeStateStationary x := by
  intro x
  fin_cases x <;> norm_num [threeStateStationary]

theorem three_state_stationary_sum :
    ∑ x, threeStateStationary x = 1 := by
  norm_num [threeStateStationary, Fin.sum_univ_succ]

/-- On centered functions, every step of the lazy kernel multiplies the
explicit Poisson solution by `1/2`. -/
theorem three_state_lazy_iterate_solution (n : ℕ) :
    markovIterate threeStateLazyKernel n threeStateLazyPoissonSolution =
      fun x => ((1 / 2 : ℝ) ^ n) * threeStateLazyPoissonSolution x := by
  induction n with
  | zero =>
      funext x
      simp [markovIterate]
  | succ n ih =>
      rw [markovIterate_succ, ih]
      funext x
      fin_cases x <;>
        norm_num [markovOperator, threeStateLazyKernel,
          threeStateLazyPoissonSolution, Fin.sum_univ_succ,
          pow_succ] <;> ring

theorem three_state_lazy_poisson_covariance_formula (n : ℕ) :
    weightedInner threeStateStationary threeStateCenteredObservable
        (markovIterate threeStateLazyKernel n
          threeStateLazyPoissonSolution) =
      (4 / 3 : ℝ) * (1 / 2 : ℝ) ^ n := by
  rw [three_state_lazy_iterate_solution]
  norm_num [weightedInner, threeStateStationary,
    threeStateCenteredObservable, threeStateLazyPoissonSolution,
    Fin.sum_univ_succ]
  ring

theorem three_state_lazy_poisson_covariance_tendsto_zero :
    Tendsto
      (fun n => weightedInner threeStateStationary
        threeStateCenteredObservable
        (markovIterate threeStateLazyKernel n
          (poissonSolution threeStateStationary threeStateLazyKernel
            three_state_lazy_meanZeroPoissonInvertible
            threeStateCenteredObservable three_state_observable_meanZero)))
      atTop (𝓝 0) := by
  rw [three_state_lazy_selectedSolution_eq]
  have hpow : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n)
      atTop (𝓝 0) := by
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hscaled : Tendsto
      (fun n : ℕ => (4 / 3 : ℝ) * (1 / 2 : ℝ) ^ n)
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hpow : Tendsto
      (fun n : ℕ => (4 / 3 : ℝ) * (1 / 2 : ℝ) ^ n)
      atTop (𝓝 ((4 / 3 : ℝ) * 0)))
  simpa only [three_state_lazy_poisson_covariance_formula] using hscaled

/-- Regression example for the actual finite-path sample mean: the fast chain
has asymptotic variance `2/3`. -/
theorem three_state_fast_sampleMean_variance_limit :
    HasSampleMeanAsymptoticVariance
      threeStateStationary threeStateFastKernel
      three_state_stationary_nonneg three_state_stationary_sum
      threeStateCenteredObservable (2 / 3 : ℝ) := by
  rw [← three_state_fast_algebraicAsymptoticVariance]
  exact hasSampleMeanAsymptoticVariance_of_poissonCovariance_tendsto
    threeStateStationary threeStateFastKernel
    three_state_stationary_nonneg three_state_stationary_sum
    three_state_fast_reversible.stationary
    three_state_fast_meanZeroPoissonInvertible
    threeStateCenteredObservable three_state_observable_meanZero
    three_state_fast_poisson_covariance_tendsto_zero

/-- Regression example for a nontrivial geometric decay: the lazy chain has
actual sample-mean asymptotic variance `2`. -/
theorem three_state_lazy_sampleMean_variance_limit :
    HasSampleMeanAsymptoticVariance
      threeStateStationary threeStateLazyKernel
      three_state_stationary_nonneg three_state_stationary_sum
      threeStateCenteredObservable 2 := by
  rw [← three_state_lazy_algebraicAsymptoticVariance]
  exact hasSampleMeanAsymptoticVariance_of_poissonCovariance_tendsto
    threeStateStationary threeStateLazyKernel
    three_state_stationary_nonneg three_state_stationary_sum
    three_state_lazy_reversible.stationary
    three_state_lazy_meanZeroPoissonInvertible
    threeStateCenteredObservable three_state_observable_meanZero
    three_state_lazy_poisson_covariance_tendsto_zero

theorem three_state_actual_sampleMean_limits_and_order :
    HasSampleMeanAsymptoticVariance
        threeStateStationary threeStateFastKernel
        three_state_stationary_nonneg three_state_stationary_sum
        threeStateCenteredObservable (2 / 3 : ℝ) ∧
      HasSampleMeanAsymptoticVariance
        threeStateStationary threeStateLazyKernel
        three_state_stationary_nonneg three_state_stationary_sum
        threeStateCenteredObservable 2 ∧
      (2 / 3 : ℝ) < 2 := by
  exact ⟨three_state_fast_sampleMean_variance_limit,
    three_state_lazy_sampleMean_variance_limit, by norm_num⟩

end LeanMetro
