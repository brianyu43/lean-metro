import LeanMetro.Asymmetric
import LeanMetro.TwoState

namespace LeanMetro

/-- A genuinely asymmetric two-state proposal. -/
noncomputable def asymmetricTwoStateProposal : Fin 2 → Fin 2 → ℝ :=
  ![![1 / 2, 1 / 2], ![1 / 4, 3 / 4]]

/-- The asymmetric MH transition generated from target weights `(1, 3)`. -/
noncomputable def asymmetricTwoStateTransition : Fin 2 → Fin 2 → ℝ :=
  ![![1 / 2, 1 / 2], ![1 / 6, 5 / 6]]

theorem asymmetric_two_state_proposal_nonneg (i j : Fin 2) :
    0 ≤ asymmetricTwoStateProposal i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [asymmetricTwoStateProposal]

theorem asymmetric_two_state_proposal_row_sum (i : Fin 2) :
    ∑ j : Fin 2, asymmetricTwoStateProposal i j = 1 := by
  fin_cases i <;>
    norm_num [asymmetricTwoStateProposal, Fin.sum_univ_two]

theorem asymmetric_two_state_proposal_not_symmetric :
    asymmetricTwoStateProposal 0 1 ≠ asymmetricTwoStateProposal 1 0 := by
  norm_num [asymmetricTwoStateProposal]

theorem asymmetric_two_state_transition_eq_general (i j : Fin 2) :
    mhAsymmetricTransition twoStateWeight asymmetricTwoStateProposal i j =
      asymmetricTwoStateTransition i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [mhAsymmetricTransition, mhAsymmetricLeavingMass,
      mhAsymmetricAcceptedMove, mhAsymmetricAcceptance,
      twoStateWeight, asymmetricTwoStateProposal,
      asymmetricTwoStateTransition]

theorem asymmetric_two_state_transition_is_stochastic :
    (∀ i j, 0 ≤ asymmetricTwoStateTransition i j) ∧
      ∀ i, ∑ j, asymmetricTwoStateTransition i j = 1 := by
  constructor
  · intro i j
    rw [← asymmetric_two_state_transition_eq_general]
    exact mhAsymmetricTransition_nonneg
      twoStateWeight asymmetricTwoStateProposal
      two_state_weight_pos asymmetric_two_state_proposal_nonneg
      asymmetric_two_state_proposal_row_sum i j
  · intro i
    simp_rw [← asymmetric_two_state_transition_eq_general]
    exact mhAsymmetricTransition_row_sum
      twoStateWeight asymmetricTwoStateProposal i

theorem asymmetric_two_state_detailed_balance_from_general (i j : Fin 2) :
    twoStateWeight i * asymmetricTwoStateTransition i j =
      twoStateWeight j * asymmetricTwoStateTransition j i := by
  rw [← asymmetric_two_state_transition_eq_general i j]
  rw [← asymmetric_two_state_transition_eq_general j i]
  exact mhAsymmetricTransition_detailed_balance
    twoStateWeight asymmetricTwoStateProposal
    two_state_weight_pos asymmetric_two_state_proposal_nonneg i j

theorem asymmetric_two_state_stationary_from_general (j : Fin 2) :
    ∑ i : Fin 2, twoStateStationary i * asymmetricTwoStateTransition i j =
      twoStateStationary j := by
  simp_rw [← two_state_stationary_eq_normalized]
  simp_rw [← asymmetric_two_state_transition_eq_general]
  exact mhAsymmetricTransition_stationary
    twoStateWeight asymmetricTwoStateProposal
    two_state_weight_pos asymmetric_two_state_proposal_nonneg j

end LeanMetro
