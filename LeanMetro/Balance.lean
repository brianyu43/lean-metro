import Mathlib

theorem mh_balance_scalar {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    a * min 1 (b / a) = b * min 1 (a / b) := by
  rcases le_total a b with hab | hba
  · have h_one_le : 1 ≤ b / a := by
      apply (le_div_iff₀ ha).2
      simpa using hab
    have h_div_le : a / b ≤ 1 := by
      apply (div_le_iff₀ hb).2
      simpa using hab
    rw [min_eq_left h_one_le, min_eq_right h_div_le]
    field_simp [ne_of_gt hb]
  · have h_div_le : b / a ≤ 1 := by
      apply (div_le_iff₀ ha).2
      simpa using hba
    have h_one_le : 1 ≤ a / b := by
      apply (le_div_iff₀ hb).2
      simpa using hba
    rw [min_eq_right h_div_le, min_eq_left h_one_le]
    field_simp [ne_of_gt ha]
