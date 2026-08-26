import Mathlib

namespace LeanMetro

def twoStateWeight : Fin 2 → ℝ :=
  ![1, 3]

noncomputable def twoStateTransition : Fin 2 → Fin 2 → ℝ :=
  ![![0, 1], ![1 / 3, 2 / 3]]

noncomputable def twoStateStationary : Fin 2 → ℝ :=
  ![1 / 4, 3 / 4]

theorem two_state_row_sum (i : Fin 2) :
    ∑ j : Fin 2, twoStateTransition i j = 1 := by
  fin_cases i <;> norm_num [twoStateTransition, Fin.sum_univ_two]

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

end LeanMetro
