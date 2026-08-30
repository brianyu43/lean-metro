import LeanMetro.Peskun
import LeanMetro.PoissonExample

namespace LeanMetro

/-! ## Two-state numerical variance comparison -/

noncomputable def twoStateLazyKernel : FiniteKernel (Fin 2) where
  prob := ![![1 / 2, 1 / 2], ![1 / 6, 5 / 6]]
  nonneg := by
    intro x y
    fin_cases x <;> fin_cases y <;> norm_num
  row_sum := by
    intro x
    fin_cases x <;> norm_num [Fin.sum_univ_two]

theorem two_state_mh_reversible :
    twoStateFiniteKernel.ReversibleFor twoStateStationary := by
  intro x y
  fin_cases x <;> fin_cases y <;>
    norm_num [twoStateFiniteKernel, twoStateTransition, twoStateStationary]

theorem two_state_lazy_reversible :
    twoStateLazyKernel.ReversibleFor twoStateStationary := by
  intro x y
  fin_cases x <;> fin_cases y <;>
    norm_num [twoStateLazyKernel, twoStateStationary]

theorem two_state_mh_dominates_lazy :
    PeskunDominates twoStateFiniteKernel twoStateLazyKernel := by
  intro x y hxy
  fin_cases x <;> fin_cases y
  · exact (hxy rfl).elim
  · norm_num [twoStateFiniteKernel, twoStateLazyKernel, twoStateTransition]
  · norm_num [twoStateFiniteKernel, twoStateLazyKernel, twoStateTransition]
  · exact (hxy rfl).elim

theorem two_state_lazy_fixedPointsAreConstants :
    FixedPointsAreConstants twoStateLazyKernel := by
  intro f hfixed
  refine ⟨f 0, ?_⟩
  intro x
  fin_cases x
  · rfl
  · have hzero := hfixed 0
    norm_num [markovOperator, twoStateLazyKernel, Fin.sum_univ_two] at hzero
    have heq : f 1 = f 0 := by linarith
    simpa using heq

theorem two_state_lazy_meanZeroPoissonSolvable :
    MeanZeroPoissonSolvable twoStateStationary twoStateLazyKernel := by
  intro f hf
  let g : Fin 2 → ℝ := ![(3 / 2 : ℝ) * f 0, -(1 / 2 : ℝ) * f 0]
  have hcenter : f 0 + 3 * f 1 = 0 := by
    unfold MeanZero weightedMean at hf
    norm_num [twoStateStationary, Fin.sum_univ_two] at hf ⊢
    linarith
  refine ⟨g, ?_, ?_⟩
  · unfold MeanZero weightedMean
    norm_num [g, twoStateStationary, Fin.sum_univ_two]
    ring
  · unfold PoissonEquation
    funext x
    fin_cases x
    · norm_num [laplacianOperator, markovOperator, twoStateLazyKernel,
        g, Fin.sum_univ_two]
      ring
    · norm_num [laplacianOperator, markovOperator, twoStateLazyKernel,
        g, Fin.sum_univ_two]
      linarith

theorem two_state_lazy_meanZeroPoissonInvertible :
    MeanZeroPoissonInvertible twoStateStationary twoStateLazyKernel := by
  apply meanZeroPoissonInvertible_of_solvable_of_fixedPoints
  · norm_num [twoStateStationary, Fin.sum_univ_two]
  · exact two_state_lazy_fixedPointsAreConstants
  · exact two_state_lazy_meanZeroPoissonSolvable

def twoStateCenteredObservable : Fin 2 → ℝ := ![-3, 1]

noncomputable def twoStateMHPoissonSolution : Fin 2 → ℝ := ![-9 / 4, 3 / 4]

noncomputable def twoStateLazyPoissonSolution : Fin 2 → ℝ := ![-9 / 2, 3 / 2]

theorem two_state_observable_meanZero :
    MeanZero twoStateStationary twoStateCenteredObservable := by
  norm_num [MeanZero, weightedMean, twoStateStationary,
    twoStateCenteredObservable, Fin.sum_univ_two]

theorem two_state_mh_explicitSolution_meanZero :
    MeanZero twoStateStationary twoStateMHPoissonSolution := by
  norm_num [MeanZero, weightedMean, twoStateStationary,
    twoStateMHPoissonSolution, Fin.sum_univ_two]

theorem two_state_lazy_explicitSolution_meanZero :
    MeanZero twoStateStationary twoStateLazyPoissonSolution := by
  norm_num [MeanZero, weightedMean, twoStateStationary,
    twoStateLazyPoissonSolution, Fin.sum_univ_two]

theorem two_state_mh_explicitSolution_equation :
    PoissonEquation twoStateFiniteKernel
      twoStateCenteredObservable twoStateMHPoissonSolution := by
  unfold PoissonEquation
  funext x
  fin_cases x <;>
    norm_num [laplacianOperator, markovOperator, twoStateFiniteKernel,
      twoStateTransition, twoStateCenteredObservable,
      twoStateMHPoissonSolution, Fin.sum_univ_two]

theorem two_state_lazy_explicitSolution_equation :
    PoissonEquation twoStateLazyKernel
      twoStateCenteredObservable twoStateLazyPoissonSolution := by
  unfold PoissonEquation
  funext x
  fin_cases x <;>
    norm_num [laplacianOperator, markovOperator, twoStateLazyKernel,
      twoStateCenteredObservable, twoStateLazyPoissonSolution,
      Fin.sum_univ_two]

theorem two_state_mh_selectedSolution_eq :
    poissonSolution twoStateStationary twoStateFiniteKernel
        two_state_meanZeroPoissonInvertible
        twoStateCenteredObservable two_state_observable_meanZero =
      twoStateMHPoissonSolution := by
  exact poissonSolution_eq_of_meanZero_solution
    twoStateStationary twoStateFiniteKernel
    two_state_meanZeroPoissonInvertible
    twoStateCenteredObservable two_state_observable_meanZero
    twoStateMHPoissonSolution
    two_state_mh_explicitSolution_meanZero
    two_state_mh_explicitSolution_equation

theorem two_state_lazy_selectedSolution_eq :
    poissonSolution twoStateStationary twoStateLazyKernel
        two_state_lazy_meanZeroPoissonInvertible
        twoStateCenteredObservable two_state_observable_meanZero =
      twoStateLazyPoissonSolution := by
  exact poissonSolution_eq_of_meanZero_solution
    twoStateStationary twoStateLazyKernel
    two_state_lazy_meanZeroPoissonInvertible
    twoStateCenteredObservable two_state_observable_meanZero
    twoStateLazyPoissonSolution
    two_state_lazy_explicitSolution_meanZero
    two_state_lazy_explicitSolution_equation

theorem two_state_mh_algebraicAsymptoticVariance :
    algebraicAsymptoticVariance
        twoStateStationary twoStateFiniteKernel
        two_state_meanZeroPoissonInvertible
        twoStateCenteredObservable two_state_observable_meanZero = 3 / 2 := by
  unfold algebraicAsymptoticVariance inverseQuadraticForm
  rw [two_state_mh_selectedSolution_eq]
  norm_num [weightedInner, twoStateStationary, twoStateCenteredObservable,
    twoStateMHPoissonSolution, Fin.sum_univ_two]

theorem two_state_lazy_algebraicAsymptoticVariance :
    algebraicAsymptoticVariance
        twoStateStationary twoStateLazyKernel
        two_state_lazy_meanZeroPoissonInvertible
        twoStateCenteredObservable two_state_observable_meanZero = 6 := by
  unfold algebraicAsymptoticVariance inverseQuadraticForm
  rw [two_state_lazy_selectedSolution_eq]
  norm_num [weightedInner, twoStateStationary, twoStateCenteredObservable,
    twoStateLazyPoissonSolution, Fin.sum_univ_two]

theorem two_state_mh_variance_strictly_less_than_lazy :
    algebraicAsymptoticVariance
        twoStateStationary twoStateFiniteKernel
        two_state_meanZeroPoissonInvertible
        twoStateCenteredObservable two_state_observable_meanZero <
      algebraicAsymptoticVariance
        twoStateStationary twoStateLazyKernel
        two_state_lazy_meanZeroPoissonInvertible
        twoStateCenteredObservable two_state_observable_meanZero := by
  rw [two_state_mh_algebraicAsymptoticVariance]
  rw [two_state_lazy_algebraicAsymptoticVariance]
  norm_num

theorem two_state_variance_order_from_peskun :
    algebraicAsymptoticVariance
        twoStateStationary twoStateFiniteKernel
        two_state_meanZeroPoissonInvertible
        twoStateCenteredObservable two_state_observable_meanZero ≤
      algebraicAsymptoticVariance
        twoStateStationary twoStateLazyKernel
        two_state_lazy_meanZeroPoissonInvertible
        twoStateCenteredObservable two_state_observable_meanZero := by
  exact algebraicAsymptoticVariance_mono_of_peskunDominates
    twoStateStationary twoStateFiniteKernel twoStateLazyKernel
    (by
      intro x
      fin_cases x <;> norm_num [twoStateStationary])
    two_state_mh_reversible two_state_lazy_reversible
    two_state_mh_dominates_lazy
    two_state_meanZeroPoissonInvertible
    two_state_lazy_meanZeroPoissonInvertible
    twoStateCenteredObservable two_state_observable_meanZero

end LeanMetro
