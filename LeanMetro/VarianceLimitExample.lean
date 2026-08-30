import LeanMetro.VarianceLimit
import LeanMetro.ThreeStateExample

namespace LeanMetro

open Filter
open scoped Topology

theorem three_state_fast_iterate_solution_succ (n : ℕ) :
    markovIterate threeStateFastKernel (n + 1)
        threeStateFastPoissonSolution = fun _ => 0 := by
  induction n with
  | zero =>
      funext x
      fin_cases x <;>
        norm_num [markovIterate, markovOperator, threeStateFastKernel,
          threeStateFastPoissonSolution, Fin.sum_univ_succ]
  | succ n ih =>
      rw [markovIterate_succ, ih]
      funext x
      simp [markovOperator]

theorem three_state_fast_poisson_covariance_tendsto_zero :
    Tendsto
      (fun n => weightedInner threeStateStationary
        threeStateCenteredObservable
        (markovIterate threeStateFastKernel n
          (poissonSolution threeStateStationary threeStateFastKernel
            three_state_fast_meanZeroPoissonInvertible
            threeStateCenteredObservable three_state_observable_meanZero)))
      atTop (𝓝 0) := by
  rw [three_state_fast_selectedSolution_eq]
  have hevent : ∀ᶠ n : ℕ in atTop,
      weightedInner threeStateStationary threeStateCenteredObservable
        (markovIterate threeStateFastKernel n
          threeStateFastPoissonSolution) = 0 := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    rw [three_state_fast_iterate_solution_succ]
    simp [weightedInner]
  exact (tendsto_congr' hevent).2 tendsto_const_nhds

theorem three_state_fast_scaledVariance_limit :
    Tendsto
      (stationaryScaledVariance threeStateStationary
        threeStateFastKernel threeStateCenteredObservable)
      atTop (𝓝 (2 / 3 : ℝ)) := by
  rw [← three_state_fast_algebraicAsymptoticVariance]
  exact stationaryScaledVariance_tendsto_algebraicAsymptoticVariance
    threeStateStationary threeStateFastKernel
    three_state_fast_meanZeroPoissonInvertible
    threeStateCenteredObservable three_state_observable_meanZero
    three_state_fast_poisson_covariance_tendsto_zero

end LeanMetro
