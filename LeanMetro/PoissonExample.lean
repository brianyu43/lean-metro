import LeanMetro.Poisson
import LeanMetro.TwoState

namespace LeanMetro

/-- The original two-state MH transition bundled as a finite kernel. -/
noncomputable def twoStateFiniteKernel : FiniteKernel (Fin 2) where
  prob := twoStateTransition
  nonneg := two_state_transition_nonneg_from_general
  row_sum := two_state_row_sum

theorem two_state_fixedPointsAreConstants :
    FixedPointsAreConstants twoStateFiniteKernel := by
  intro f hfixed
  refine ⟨f 0, ?_⟩
  intro x
  fin_cases x
  · rfl
  · have hzero := hfixed 0
    norm_num [markovOperator, twoStateFiniteKernel, twoStateTransition,
      Fin.sum_univ_two] at hzero
    simpa using hzero

theorem two_state_meanZeroPoissonSolvable :
    MeanZeroPoissonSolvable twoStateStationary twoStateFiniteKernel := by
  intro f hf
  let g : Fin 2 → ℝ := ![(3 / 4 : ℝ) * f 0, -(1 / 4 : ℝ) * f 0]
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
    · norm_num [laplacianOperator, markovOperator, twoStateFiniteKernel,
        twoStateTransition, g, Fin.sum_univ_two]
      ring
    · norm_num [laplacianOperator, markovOperator, twoStateFiniteKernel,
        twoStateTransition, g, Fin.sum_univ_two]
      linarith

theorem two_state_meanZeroPoissonInvertible :
    MeanZeroPoissonInvertible twoStateStationary twoStateFiniteKernel := by
  apply meanZeroPoissonInvertible_of_solvable_of_fixedPoints
  · norm_num [twoStateStationary, Fin.sum_univ_two]
  · exact two_state_fixedPointsAreConstants
  · exact two_state_meanZeroPoissonSolvable

/-- The identity chain is a deliberately singular regression example. -/
noncomputable def twoStateIdentityKernel : FiniteKernel (Fin 2) where
  prob := ![![1, 0], ![0, 1]]
  nonneg := by
    intro x y
    fin_cases x <;> fin_cases y <;> norm_num
  row_sum := by
    intro x
    fin_cases x <;> norm_num [Fin.sum_univ_two]

theorem two_state_identity_markovOperator
    (f : Fin 2 → ℝ) (x : Fin 2) :
    markovOperator twoStateIdentityKernel f x = f x := by
  fin_cases x <;>
    norm_num [markovOperator, twoStateIdentityKernel, Fin.sum_univ_two]

theorem two_state_identity_not_fixedPointsAreConstants :
    ¬ FixedPointsAreConstants twoStateIdentityKernel := by
  intro hfixed
  let f : Fin 2 → ℝ := ![0, 1]
  obtain ⟨c, hc⟩ := hfixed f (two_state_identity_markovOperator f)
  have hzero := hc 0
  have hone := hc 1
  norm_num [f] at hzero hone
  linarith

end LeanMetro
