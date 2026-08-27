import LeanMetro.OffDiagonal

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

theorem two_state_stationary (j : Fin 2) :
    ∑ i : Fin 2, twoStateStationary i * twoStateTransition i j =
      twoStateStationary j := by
  fin_cases j <;>
    norm_num [twoStateStationary, twoStateTransition, Fin.sum_univ_two]

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
