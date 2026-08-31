import LeanMetro.IrreduciblePeskun

namespace LeanMetro

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

/-! ## A periodic chain whose covariance does not decay pointwise

The deterministic two-state swap is irreducible and reversible, but has
period two.  Its Poisson covariance alternates between `1 / 2` and `-1 / 2`,
so the old pointwise-decay hypothesis fails.  Nevertheless the exact
telescoping remainder proves that the actual scaled sample-mean variance
converges to zero.
-/

noncomputable def periodicStationary : Fin 2 → ℝ := ![1 / 2, 1 / 2]

noncomputable def periodicSwapKernel : FiniteKernel (Fin 2) where
  prob := ![![0, 1], ![1, 0]]
  nonneg := by
    intro x y
    fin_cases x <;> fin_cases y <;> norm_num
  row_sum := by
    intro x
    fin_cases x <;> norm_num [Fin.sum_univ_two]

def periodicObservable : Fin 2 → ℝ := ![1, -1]

noncomputable def periodicPoissonSolution : Fin 2 → ℝ := ![1 / 2, -1 / 2]

theorem periodic_stationary_nonneg (x : Fin 2) :
    0 ≤ periodicStationary x := by
  fin_cases x <;> norm_num [periodicStationary]

theorem periodic_stationary_sum :
    ∑ x, periodicStationary x = 1 := by
  norm_num [periodicStationary, Fin.sum_univ_two]

theorem periodic_swap_nonneg (x y : Fin 2) :
    0 ≤ periodicSwapKernel.prob x y :=
  periodicSwapKernel.nonneg x y

theorem periodic_swap_row_sum (x : Fin 2) :
    ∑ y, periodicSwapKernel.prob x y = 1 :=
  periodicSwapKernel.row_sum x

theorem periodic_swap_reversible :
    periodicSwapKernel.ReversibleFor periodicStationary := by
  intro x y
  fin_cases x <;> fin_cases y <;>
    norm_num [periodicSwapKernel, periodicStationary]

theorem periodic_swap_irreducible :
    periodicSwapKernel.Irreducible := by
  constructor
  · exact periodicSwapKernel.nonneg
  intro x y
  let : Quiver (Fin 2) := Matrix.toQuiver periodicSwapKernel.prob
  have h01 : (0 : Fin 2) ⟶ (1 : Fin 2) :=
    PLift.up (by norm_num [periodicSwapKernel])
  have h10 : (1 : Fin 2) ⟶ (0 : Fin 2) :=
    PLift.up (by norm_num [periodicSwapKernel])
  fin_cases x <;> fin_cases y
  · exact ⟨(Quiver.Path.nil.cons h01).cons h10, by simp⟩
  · exact ⟨Quiver.Path.nil.cons h01, by simp⟩
  · exact ⟨Quiver.Path.nil.cons h10, by simp⟩
  · exact ⟨(Quiver.Path.nil.cons h10).cons h01, by simp⟩

theorem periodic_observable_meanZero :
    MeanZero periodicStationary periodicObservable := by
  norm_num [MeanZero, weightedMean, periodicStationary,
    periodicObservable, Fin.sum_univ_two]

theorem periodic_meanZeroPoissonInvertible :
    MeanZeroPoissonInvertible periodicStationary periodicSwapKernel := by
  exact meanZeroPoissonInvertible_of_irreducible
    periodicStationary periodicSwapKernel periodic_stationary_sum
    periodic_swap_reversible.stationary periodic_swap_irreducible

theorem periodic_explicitSolution_meanZero :
    MeanZero periodicStationary periodicPoissonSolution := by
  norm_num [MeanZero, weightedMean, periodicStationary,
    periodicPoissonSolution, Fin.sum_univ_two]

theorem periodic_explicitSolution_equation :
    PoissonEquation periodicSwapKernel
      periodicObservable periodicPoissonSolution := by
  unfold PoissonEquation
  funext x
  fin_cases x <;>
    norm_num [laplacianOperator, markovOperator, periodicSwapKernel,
      periodicObservable, periodicPoissonSolution, Fin.sum_univ_two]

theorem periodic_selectedSolution_eq :
    poissonSolution periodicStationary periodicSwapKernel
        periodic_meanZeroPoissonInvertible
        periodicObservable periodic_observable_meanZero =
      periodicPoissonSolution := by
  exact poissonSolution_eq_of_meanZero_solution
    periodicStationary periodicSwapKernel
    periodic_meanZeroPoissonInvertible
    periodicObservable periodic_observable_meanZero
    periodicPoissonSolution periodic_explicitSolution_meanZero
    periodic_explicitSolution_equation

theorem periodic_algebraicAsymptoticVariance :
    algebraicAsymptoticVariance
        periodicStationary periodicSwapKernel
        periodic_meanZeroPoissonInvertible
        periodicObservable periodic_observable_meanZero = 0 := by
  unfold algebraicAsymptoticVariance inverseQuadraticForm
  rw [periodic_selectedSolution_eq]
  norm_num [weightedInner, periodicStationary, periodicObservable,
    periodicPoissonSolution, Fin.sum_univ_two]

theorem periodic_iterate_solution (n : ℕ) :
    markovIterate periodicSwapKernel n periodicPoissonSolution =
      fun x ↦ ((-1 : ℝ) ^ n) * periodicPoissonSolution x := by
  induction n with
  | zero =>
      funext x
      simp
  | succ n ih =>
      rw [markovIterate_succ, ih]
      funext x
      fin_cases x <;>
        norm_num [markovOperator, periodicSwapKernel,
          periodicPoissonSolution, Fin.sum_univ_two, pow_succ]

theorem periodic_poisson_covariance_formula (n : ℕ) :
    weightedInner periodicStationary periodicObservable
        (markovIterate periodicSwapKernel n
          (poissonSolution periodicStationary periodicSwapKernel
            periodic_meanZeroPoissonInvertible
            periodicObservable periodic_observable_meanZero)) =
      ((-1 : ℝ) ^ n) / 2 := by
  rw [periodic_selectedSolution_eq, periodic_iterate_solution]
  norm_num [weightedInner, periodicStationary, periodicObservable,
    periodicPoissonSolution, Fin.sum_univ_two]
  ring

/-- The old pointwise covariance-decay premise is false for this period-two
chain: the covariance equals `1 / 2` at every even time. -/
theorem periodic_poisson_covariance_not_tendsto_zero :
    ¬ Tendsto
      (fun n ↦ weightedInner periodicStationary periodicObservable
        (markovIterate periodicSwapKernel n
          (poissonSolution periodicStationary periodicSwapKernel
            periodic_meanZeroPoissonInvertible
            periodicObservable periodic_observable_meanZero)))
      atTop (nhds 0) := by
  intro hdecay
  rw [Metric.tendsto_atTop] at hdecay
  obtain ⟨N, hN⟩ := hdecay (1 / 4) (by norm_num)
  have hlarge := hN (2 * N) (by omega)
  rw [periodic_poisson_covariance_formula] at hlarge
  have heven : ((-1 : ℝ) ^ (2 * N)) = 1 := by
    rw [pow_mul]
    norm_num
  rw [heven] at hlarge
  norm_num [Real.dist_eq] at hlarge

/-- The new telescoping theorem proves the variance limit without pointwise
covariance decay (and hence without aperiodicity). -/
theorem periodic_stationaryScaledVariance_tendsto_zero :
    Tendsto
      (stationaryScaledVariance
        periodicStationary periodicSwapKernel periodicObservable)
      atTop (nhds 0) := by
  have hlimit :=
    stationaryScaledVariance_tendsto_algebraicAsymptoticVariance_of_reversible
      periodicStationary periodicSwapKernel periodic_swap_reversible
      periodic_meanZeroPoissonInvertible
      periodicObservable periodic_observable_meanZero
  rw [periodic_algebraicAsymptoticVariance] at hlimit
  exact hlimit

/-- On the actual finite-path probability spaces, the scaled variance of the
sample mean converges to zero although the Poisson covariance oscillates. -/
theorem periodic_hasSampleMeanAsymptoticVariance_zero :
    HasSampleMeanAsymptoticVariance
      periodicStationary periodicSwapKernel
      periodic_stationary_nonneg periodic_stationary_sum
      periodicObservable 0 := by
  have hlimit := hasSampleMeanAsymptoticVariance_of_irreducible
    periodicStationary periodicSwapKernel
    periodic_stationary_nonneg periodic_stationary_sum
    periodic_swap_reversible periodic_swap_irreducible
    periodicObservable periodic_observable_meanZero
  dsimp only at hlimit
  rw [periodic_algebraicAsymptoticVariance] at hlimit
  exact hlimit

/-- The same periodic result, expanded to its literal `Tendsto` statement. -/
theorem periodic_sampleMean_scaledVariance_tendsto_zero :
    Tendsto
      (fun n ↦ ((n + 1 : ℕ) : ℝ) *
        variance (chainSampleMean periodicObservable n)
          (stationaryPathMeasure
            periodicStationary periodicSwapKernel
            periodic_stationary_nonneg periodic_stationary_sum n))
      atTop (nhds 0) := by
  exact periodic_hasSampleMeanAsymptoticVariance_zero

end LeanMetro
