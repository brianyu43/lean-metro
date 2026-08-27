import Mathlib

/-- The accepted mass from weight `a` toward weight `b` is `min a b`. -/
theorem weight_mul_acceptance_eq_min {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    a * min 1 (b / a) = min a b := by
  rcases le_total a b with hab | hba
  · have h_one_le : 1 ≤ b / a := by
      apply (le_div_iff₀ ha).2
      simpa using hab
    simp [min_eq_left h_one_le, min_eq_left hab]
  · have h_div_le : b / a ≤ 1 := by
      apply (div_le_iff₀ ha).2
      simpa using hba
    rw [min_eq_right h_div_le, min_eq_right hba]
    field_simp [ne_of_gt ha]

/-- The scalar detailed-balance identity for the Metropolis acceptance rule. -/
theorem mh_balance_scalar {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    a * min 1 (b / a) = b * min 1 (a / b) := by
  calc
    a * min 1 (b / a) = min a b := weight_mul_acceptance_eq_min ha hb
    _ = min b a := min_comm a b
    _ = b * min 1 (a / b) := (weight_mul_acceptance_eq_min hb ha).symm
