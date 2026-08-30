import LeanMetro.Peskun

namespace LeanMetro

/-! A three-state numerical regression example. The fast kernel draws a fresh
uniform state; the lazy kernel stays put with probability `1/2` and otherwise
uses the fast kernel. -/

noncomputable def threeStateStationary : Fin 3 → ℝ :=
  ![1 / 3, 1 / 3, 1 / 3]

noncomputable def threeStateFastKernel : FiniteKernel (Fin 3) where
  prob := ![
    ![1 / 3, 1 / 3, 1 / 3],
    ![1 / 3, 1 / 3, 1 / 3],
    ![1 / 3, 1 / 3, 1 / 3]]
  nonneg := by
    intro x y
    fin_cases x <;> fin_cases y <;> norm_num
  row_sum := by
    intro x
    fin_cases x <;> norm_num [Fin.sum_univ_succ]

noncomputable def threeStateLazyKernel : FiniteKernel (Fin 3) where
  prob := ![
    ![2 / 3, 1 / 6, 1 / 6],
    ![1 / 6, 2 / 3, 1 / 6],
    ![1 / 6, 1 / 6, 2 / 3]]
  nonneg := by
    intro x y
    fin_cases x <;> fin_cases y <;> norm_num
  row_sum := by
    intro x
    fin_cases x <;> norm_num [Fin.sum_univ_succ]

theorem three_state_fast_reversible :
    threeStateFastKernel.ReversibleFor threeStateStationary := by
  intro x y
  fin_cases x <;> fin_cases y <;>
    norm_num [threeStateFastKernel, threeStateStationary]

theorem three_state_lazy_reversible :
    threeStateLazyKernel.ReversibleFor threeStateStationary := by
  intro x y
  fin_cases x <;> fin_cases y <;>
    norm_num [threeStateLazyKernel, threeStateStationary]

theorem three_state_fast_dominates_lazy :
    PeskunDominates threeStateFastKernel threeStateLazyKernel := by
  intro x y hxy
  fin_cases x <;> fin_cases y
  all_goals norm_num [threeStateFastKernel, threeStateLazyKernel] at *

theorem three_state_meanZero_sum
    {f : Fin 3 → ℝ} (hf : MeanZero threeStateStationary f) :
    f 0 + f 1 + f 2 = 0 := by
  unfold MeanZero weightedMean at hf
  norm_num [threeStateStationary, Fin.sum_univ_succ] at hf ⊢
  linarith

theorem three_state_fast_fixedPointsAreConstants :
    FixedPointsAreConstants threeStateFastKernel := by
  intro f hfixed
  have hzero := hfixed 0
  have hone := hfixed 1
  have htwo := hfixed 2
  norm_num [markovOperator, threeStateFastKernel, Fin.sum_univ_succ]
    at hzero hone htwo
  have hone_eq : f 1 = f 0 := by linarith
  have htwo_eq : f 2 = f 0 := by linarith
  refine ⟨f 0, ?_⟩
  intro x
  fin_cases x
  · rfl
  · simpa using hone_eq
  · simpa using htwo_eq

theorem three_state_lazy_fixedPointsAreConstants :
    FixedPointsAreConstants threeStateLazyKernel := by
  intro f hfixed
  have hzero := hfixed 0
  have hone := hfixed 1
  have htwo := hfixed 2
  norm_num [markovOperator, threeStateLazyKernel, Fin.sum_univ_succ]
    at hzero hone htwo
  have hone_eq : f 1 = f 0 := by linarith
  have htwo_eq : f 2 = f 0 := by linarith
  refine ⟨f 0, ?_⟩
  intro x
  fin_cases x
  · rfl
  · simpa using hone_eq
  · simpa using htwo_eq

theorem three_state_fast_meanZeroPoissonSolvable :
    MeanZeroPoissonSolvable threeStateStationary threeStateFastKernel := by
  intro f hf
  have hsum := three_state_meanZero_sum hf
  refine ⟨f, hf, ?_⟩
  unfold PoissonEquation
  funext x
  fin_cases x
  · norm_num [laplacianOperator, markovOperator, threeStateFastKernel,
      Fin.sum_univ_succ]
    linarith
  · norm_num [laplacianOperator, markovOperator, threeStateFastKernel,
      Fin.sum_univ_succ]
    linarith
  · have hsum' : f 0 + f 1 + f (⟨2, by omega⟩ : Fin 3) = 0 := by
      simpa using hsum
    norm_num [laplacianOperator, markovOperator, threeStateFastKernel,
      Fin.sum_univ_succ]
    linarith

theorem three_state_lazy_meanZeroPoissonSolvable :
    MeanZeroPoissonSolvable threeStateStationary threeStateLazyKernel := by
  intro f hf
  have hsum := three_state_meanZero_sum hf
  let g : Fin 3 → ℝ := fun x => 2 * f x
  refine ⟨g, hf.smul 2, ?_⟩
  unfold PoissonEquation
  funext x
  fin_cases x
  · norm_num [laplacianOperator, markovOperator, threeStateLazyKernel,
      Fin.sum_univ_succ, g]
    linarith
  · norm_num [laplacianOperator, markovOperator, threeStateLazyKernel,
      Fin.sum_univ_succ, g]
    linarith
  · have hsum' : f 0 + f 1 + f (⟨2, by omega⟩ : Fin 3) = 0 := by
      simpa using hsum
    norm_num [laplacianOperator, markovOperator, threeStateLazyKernel,
      Fin.sum_univ_succ, g]
    linarith

theorem three_state_fast_meanZeroPoissonInvertible :
    MeanZeroPoissonInvertible threeStateStationary threeStateFastKernel := by
  apply meanZeroPoissonInvertible_of_solvable_of_fixedPoints
  · norm_num [threeStateStationary, Fin.sum_univ_succ]
  · exact three_state_fast_fixedPointsAreConstants
  · exact three_state_fast_meanZeroPoissonSolvable

theorem three_state_lazy_meanZeroPoissonInvertible :
    MeanZeroPoissonInvertible threeStateStationary threeStateLazyKernel := by
  apply meanZeroPoissonInvertible_of_solvable_of_fixedPoints
  · norm_num [threeStateStationary, Fin.sum_univ_succ]
  · exact three_state_lazy_fixedPointsAreConstants
  · exact three_state_lazy_meanZeroPoissonSolvable

def threeStateCenteredObservable : Fin 3 → ℝ := ![-1, 0, 1]

def threeStateFastPoissonSolution : Fin 3 → ℝ := ![-1, 0, 1]

def threeStateLazyPoissonSolution : Fin 3 → ℝ := ![-2, 0, 2]

theorem three_state_observable_meanZero :
    MeanZero threeStateStationary threeStateCenteredObservable := by
  norm_num [MeanZero, weightedMean, threeStateStationary,
    threeStateCenteredObservable, Fin.sum_univ_succ]

theorem three_state_fast_explicitSolution_meanZero :
    MeanZero threeStateStationary threeStateFastPoissonSolution := by
  norm_num [MeanZero, weightedMean, threeStateStationary,
    threeStateFastPoissonSolution, Fin.sum_univ_succ]

theorem three_state_lazy_explicitSolution_meanZero :
    MeanZero threeStateStationary threeStateLazyPoissonSolution := by
  norm_num [MeanZero, weightedMean, threeStateStationary,
    threeStateLazyPoissonSolution, Fin.sum_univ_succ]

theorem three_state_fast_explicitSolution_equation :
    PoissonEquation threeStateFastKernel
      threeStateCenteredObservable threeStateFastPoissonSolution := by
  unfold PoissonEquation
  funext x
  fin_cases x <;>
    norm_num [laplacianOperator, markovOperator, threeStateFastKernel,
      threeStateCenteredObservable, threeStateFastPoissonSolution,
      Fin.sum_univ_succ]

theorem three_state_lazy_explicitSolution_equation :
    PoissonEquation threeStateLazyKernel
      threeStateCenteredObservable threeStateLazyPoissonSolution := by
  unfold PoissonEquation
  funext x
  fin_cases x <;>
    norm_num [laplacianOperator, markovOperator, threeStateLazyKernel,
      threeStateCenteredObservable, threeStateLazyPoissonSolution,
      Fin.sum_univ_succ]

theorem three_state_fast_selectedSolution_eq :
    poissonSolution threeStateStationary threeStateFastKernel
        three_state_fast_meanZeroPoissonInvertible
        threeStateCenteredObservable three_state_observable_meanZero =
      threeStateFastPoissonSolution := by
  exact poissonSolution_eq_of_meanZero_solution
    threeStateStationary threeStateFastKernel
    three_state_fast_meanZeroPoissonInvertible
    threeStateCenteredObservable three_state_observable_meanZero
    threeStateFastPoissonSolution
    three_state_fast_explicitSolution_meanZero
    three_state_fast_explicitSolution_equation

theorem three_state_lazy_selectedSolution_eq :
    poissonSolution threeStateStationary threeStateLazyKernel
        three_state_lazy_meanZeroPoissonInvertible
        threeStateCenteredObservable three_state_observable_meanZero =
      threeStateLazyPoissonSolution := by
  exact poissonSolution_eq_of_meanZero_solution
    threeStateStationary threeStateLazyKernel
    three_state_lazy_meanZeroPoissonInvertible
    threeStateCenteredObservable three_state_observable_meanZero
    threeStateLazyPoissonSolution
    three_state_lazy_explicitSolution_meanZero
    three_state_lazy_explicitSolution_equation

theorem three_state_fast_algebraicAsymptoticVariance :
    algebraicAsymptoticVariance
        threeStateStationary threeStateFastKernel
        three_state_fast_meanZeroPoissonInvertible
        threeStateCenteredObservable three_state_observable_meanZero = 2 / 3 := by
  unfold algebraicAsymptoticVariance inverseQuadraticForm
  rw [three_state_fast_selectedSolution_eq]
  norm_num [weightedInner, threeStateStationary, threeStateCenteredObservable,
    threeStateFastPoissonSolution, Fin.sum_univ_succ]

theorem three_state_lazy_algebraicAsymptoticVariance :
    algebraicAsymptoticVariance
        threeStateStationary threeStateLazyKernel
        three_state_lazy_meanZeroPoissonInvertible
        threeStateCenteredObservable three_state_observable_meanZero = 2 := by
  unfold algebraicAsymptoticVariance inverseQuadraticForm
  rw [three_state_lazy_selectedSolution_eq]
  norm_num [weightedInner, threeStateStationary, threeStateCenteredObservable,
    threeStateLazyPoissonSolution, Fin.sum_univ_succ]

theorem three_state_fast_variance_strictly_less_than_lazy :
    algebraicAsymptoticVariance
        threeStateStationary threeStateFastKernel
        three_state_fast_meanZeroPoissonInvertible
        threeStateCenteredObservable three_state_observable_meanZero <
      algebraicAsymptoticVariance
        threeStateStationary threeStateLazyKernel
        three_state_lazy_meanZeroPoissonInvertible
        threeStateCenteredObservable three_state_observable_meanZero := by
  rw [three_state_fast_algebraicAsymptoticVariance]
  rw [three_state_lazy_algebraicAsymptoticVariance]
  norm_num

theorem three_state_variance_order_from_peskun :
    algebraicAsymptoticVariance
        threeStateStationary threeStateFastKernel
        three_state_fast_meanZeroPoissonInvertible
        threeStateCenteredObservable three_state_observable_meanZero ≤
      algebraicAsymptoticVariance
        threeStateStationary threeStateLazyKernel
        three_state_lazy_meanZeroPoissonInvertible
        threeStateCenteredObservable three_state_observable_meanZero := by
  exact algebraicAsymptoticVariance_mono_of_peskunDominates
    threeStateStationary threeStateFastKernel threeStateLazyKernel
    (by
      intro x
      fin_cases x <;> norm_num [threeStateStationary])
    three_state_fast_reversible three_state_lazy_reversible
    three_state_fast_dominates_lazy
    three_state_fast_meanZeroPoissonInvertible
    three_state_lazy_meanZeroPoissonInvertible
    threeStateCenteredObservable three_state_observable_meanZero

end LeanMetro
