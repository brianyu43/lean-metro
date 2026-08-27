import LeanMetro.Stationary

namespace LeanMetro

def twoStateWeight : Fin 2 → ℝ :=
  ![1, 3]

def twoStateProposal : Fin 2 → Fin 2 → ℝ :=
  ![![0, 1], ![1, 0]]

noncomputable def twoStateTransition : Fin 2 → Fin 2 → ℝ :=
  ![![0, 1], ![1 / 3, 2 / 3]]

noncomputable def twoStateStationary : Fin 2 → ℝ :=
  ![1 / 4, 3 / 4]

theorem two_state_row_sum (i : Fin 2) :
    ∑ j : Fin 2, twoStateTransition i j = 1 := by
  fin_cases i <;> norm_num [twoStateTransition, Fin.sum_univ_two]

theorem two_state_proposal_symmetric (i j : Fin 2) :
    twoStateProposal i j = twoStateProposal j i := by
  fin_cases i <;> fin_cases j <;> norm_num [twoStateProposal]

theorem two_state_weight_pos (i : Fin 2) :
    0 < twoStateWeight i := by
  fin_cases i <;> norm_num [twoStateWeight]

theorem two_state_proposal_nonneg (i j : Fin 2) :
    0 ≤ twoStateProposal i j := by
  fin_cases i <;> fin_cases j <;> norm_num [twoStateProposal]

theorem two_state_proposal_row_sum (i : Fin 2) :
    ∑ j : Fin 2, twoStateProposal i j = 1 := by
  fin_cases i <;> norm_num [twoStateProposal, Fin.sum_univ_two]

theorem two_state_transition_eq_general (i j : Fin 2) :
    mhTransition twoStateWeight twoStateProposal i j =
      twoStateTransition i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [mhTransition, mhLeavingMass, mhAcceptedMove, mhAcceptance,
      twoStateWeight, twoStateProposal, twoStateTransition]

theorem two_state_transition_nonneg_from_general (i j : Fin 2) :
    0 ≤ twoStateTransition i j := by
  rw [← two_state_transition_eq_general]
  exact mhTransition_nonneg
    twoStateWeight twoStateProposal
    two_state_weight_pos two_state_proposal_nonneg two_state_proposal_row_sum i j

theorem two_state_row_sum_from_general (i : Fin 2) :
    ∑ j : Fin 2, twoStateTransition i j = 1 := by
  simp_rw [← two_state_transition_eq_general]
  exact mhTransition_row_sum twoStateWeight twoStateProposal i

theorem two_state_stationary_eq_normalized (i : Fin 2) :
    normalizedWeight twoStateWeight i = twoStateStationary i := by
  fin_cases i <;>
    norm_num [normalizedWeight, totalWeight, twoStateWeight,
      twoStateStationary, Fin.sum_univ_two]

theorem two_state_transition_off_diagonal
    {i j : Fin 2} (hij : i ≠ j) :
    twoStateTransition i j =
      twoStateProposal i j * mhAcceptance twoStateWeight i j := by
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · norm_num [twoStateTransition, twoStateProposal, mhAcceptance, twoStateWeight]
  · norm_num [twoStateTransition, twoStateProposal, mhAcceptance, twoStateWeight]
  · exact (hij rfl).elim

theorem two_state_detailed_balance (i j : Fin 2) :
    twoStateWeight i * twoStateTransition i j =
      twoStateWeight j * twoStateTransition j i := by
  fin_cases i <;> fin_cases j <;>
    norm_num [twoStateWeight, twoStateTransition]

theorem two_state_detailed_balance_from_general (i j : Fin 2) :
    twoStateWeight i * twoStateTransition i j =
      twoStateWeight j * twoStateTransition j i := by
  rw [← two_state_transition_eq_general i j]
  rw [← two_state_transition_eq_general j i]
  exact mhTransition_detailed_balance
    twoStateWeight twoStateProposal
    two_state_weight_pos two_state_proposal_symmetric i j

theorem two_state_stationary (j : Fin 2) :
    ∑ i : Fin 2, twoStateStationary i * twoStateTransition i j =
      twoStateStationary j := by
  fin_cases j <;>
    norm_num [twoStateStationary, twoStateTransition, Fin.sum_univ_two]

theorem two_state_stationary_from_general (j : Fin 2) :
    ∑ i : Fin 2, twoStateStationary i * twoStateTransition i j =
      twoStateStationary j := by
  simp_rw [← two_state_stationary_eq_normalized]
  simp_rw [← two_state_transition_eq_general]
  exact mhTransition_stationary
    twoStateWeight twoStateProposal
    two_state_weight_pos two_state_proposal_symmetric j

theorem two_state_off_diagonal_balance_from_general :
    twoStateWeight 0 * twoStateTransition 0 1 =
      twoStateWeight 1 * twoStateTransition 1 0 := by
  rw [two_state_transition_off_diagonal (i := 0) (j := 1) (by decide)]
  rw [two_state_transition_off_diagonal (i := 1) (j := 0) (by decide)]
  exact mh_balance_symmetric_proposal
    twoStateWeight twoStateProposal
    (by norm_num [twoStateWeight])
    (by norm_num [twoStateWeight])
    (two_state_proposal_symmetric 0 1)

end LeanMetro
