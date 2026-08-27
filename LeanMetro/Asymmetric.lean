import LeanMetro.Stationary

namespace LeanMetro

/-- The accepted flow identity with nonnegative, rather than strictly positive,
inputs.  This is the zero-safe scalar core needed for asymmetric proposals. -/
theorem nonneg_mul_acceptance_eq_min {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * min 1 (b / a) = min a b := by
  by_cases ha0 : a = 0
  · subst a
    simp [hb]
  · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    by_cases hba : b ≤ a
    · have hratio : b / a ≤ 1 := by
        apply (div_le_iff₀ ha_pos).2
        simpa using hba
      rw [min_eq_right hratio, min_eq_right hba]
      field_simp
    · have hab : a ≤ b := le_of_not_ge hba
      have hratio : 1 ≤ b / a := by
        apply (le_div_iff₀ ha_pos).2
        simpa using hab
      rw [min_eq_left hratio, min_eq_left hab, mul_one]

/-- Metropolis--Hastings acceptance probability for a possibly asymmetric
proposal.  The reverse proposal probability appears in the numerator. -/
noncomputable def mhAsymmetricAcceptance
    {ι : Type*} (w : ι → ℝ) (q : ι → ι → ℝ) (x y : ι) : ℝ :=
  min 1 ((w y * q y x) / (w x * q x y))

theorem mhAsymmetricAcceptance_nonneg
    {ι : Type*} (w : ι → ℝ) (q : ι → ι → ℝ)
    (hw : ∀ z, 0 < w z) (hq_nonneg : ∀ i j, 0 ≤ q i j)
    (x y : ι) :
    0 ≤ mhAsymmetricAcceptance w q x y := by
  unfold mhAsymmetricAcceptance
  apply le_min zero_le_one
  exact div_nonneg
    (mul_nonneg (hw y).le (hq_nonneg y x))
    (mul_nonneg (hw x).le (hq_nonneg x y))

theorem mhAsymmetricAcceptance_le_one
    {ι : Type*} (w : ι → ℝ) (q : ι → ι → ℝ) (x y : ι) :
    mhAsymmetricAcceptance w q x y ≤ 1 := by
  exact min_le_left _ _

/-- Accepted off-diagonal move probability for asymmetric MH. -/
noncomputable def mhAsymmetricAcceptedMove
    {ι : Type*} (w : ι → ℝ) (q : ι → ι → ℝ) (x y : ι) : ℝ :=
  q x y * mhAsymmetricAcceptance w q x y

theorem mhAsymmetricAcceptedMove_nonneg
    {ι : Type*} (w : ι → ℝ) (q : ι → ι → ℝ)
    (hw : ∀ z, 0 < w z) (hq_nonneg : ∀ i j, 0 ≤ q i j)
    (x y : ι) :
    0 ≤ mhAsymmetricAcceptedMove w q x y := by
  exact mul_nonneg (hq_nonneg x y)
    (mhAsymmetricAcceptance_nonneg w q hw hq_nonneg x y)

theorem mhAsymmetricAcceptedMove_le_proposal
    {ι : Type*} (w : ι → ℝ) (q : ι → ι → ℝ)
    (hq_nonneg : ∀ i j, 0 ≤ q i j)
    (x y : ι) :
    mhAsymmetricAcceptedMove w q x y ≤ q x y := by
  exact mul_le_of_le_one_right (hq_nonneg x y)
    (mhAsymmetricAcceptance_le_one w q x y)

/-- The asymmetric MH acceptance rule makes the accepted probability flow
symmetric even when the proposal itself is not symmetric. -/
theorem mhAsymmetricAcceptedMove_balance
    {ι : Type*} (w : ι → ℝ) (q : ι → ι → ℝ)
    (hw : ∀ z, 0 < w z) (hq_nonneg : ∀ i j, 0 ≤ q i j)
    (x y : ι) :
    w x * mhAsymmetricAcceptedMove w q x y =
      w y * mhAsymmetricAcceptedMove w q y x := by
  unfold mhAsymmetricAcceptedMove mhAsymmetricAcceptance
  calc
    w x * (q x y * min 1 ((w y * q y x) / (w x * q x y))) =
        (w x * q x y) * min 1 ((w y * q y x) / (w x * q x y)) := by
      ring
    _ = min (w x * q x y) (w y * q y x) := by
      exact nonneg_mul_acceptance_eq_min
        (mul_nonneg (hw x).le (hq_nonneg x y))
        (mul_nonneg (hw y).le (hq_nonneg y x))
    _ = min (w y * q y x) (w x * q x y) := min_comm _ _
    _ = (w y * q y x) * min 1 ((w x * q x y) / (w y * q y x)) := by
      exact (nonneg_mul_acceptance_eq_min
        (mul_nonneg (hw y).le (hq_nonneg y x))
        (mul_nonneg (hw x).le (hq_nonneg x y))).symm
    _ = w y * (q y x * min 1 ((w x * q x y) / (w y * q y x))) := by
      ring

/-- Total accepted asymmetric-MH probability mass that leaves `x`. -/
noncomputable def mhAsymmetricLeavingMass
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (q : ι → ι → ℝ) (x : ι) : ℝ :=
  ∑ y ∈ Finset.univ.erase x, mhAsymmetricAcceptedMove w q x y

theorem mhAsymmetricLeavingMass_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (q : ι → ι → ℝ)
    (hw : ∀ z, 0 < w z) (hq_nonneg : ∀ i j, 0 ≤ q i j)
    (x : ι) :
    0 ≤ mhAsymmetricLeavingMass w q x := by
  apply Finset.sum_nonneg
  intro y _
  exact mhAsymmetricAcceptedMove_nonneg w q hw hq_nonneg x y

theorem mhAsymmetricLeavingMass_le_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (q : ι → ι → ℝ)
    (hq_nonneg : ∀ i j, 0 ≤ q i j)
    (hq_row_sum : ∀ i, ∑ j, q i j = 1)
    (x : ι) :
    mhAsymmetricLeavingMass w q x ≤ 1 := by
  have haccepted_le :
      (∑ y ∈ Finset.univ.erase x, mhAsymmetricAcceptedMove w q x y) ≤
        ∑ y ∈ Finset.univ.erase x, q x y := by
    apply Finset.sum_le_sum
    intro y _
    exact mhAsymmetricAcceptedMove_le_proposal w q hq_nonneg x y
  have hsplit :
      (∑ y ∈ Finset.univ.erase x, q x y) + q x x = 1 := by
    calc
      (∑ y ∈ Finset.univ.erase x, q x y) + q x x =
          ∑ y ∈ Finset.univ, q x y :=
        Finset.sum_erase_add Finset.univ (fun y => q x y) (Finset.mem_univ x)
      _ = 1 := hq_row_sum x
  unfold mhAsymmetricLeavingMass
  linarith [hq_nonneg x x]

/-- Complete finite-state MH transition for a possibly asymmetric proposal. -/
noncomputable def mhAsymmetricTransition
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (q : ι → ι → ℝ) (x y : ι) : ℝ :=
  if x = y then
    1 - mhAsymmetricLeavingMass w q x
  else
    mhAsymmetricAcceptedMove w q x y

@[simp]
theorem mhAsymmetricTransition_self
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (q : ι → ι → ℝ) (x : ι) :
    mhAsymmetricTransition w q x x =
      1 - mhAsymmetricLeavingMass w q x := by
  simp [mhAsymmetricTransition]

theorem mhAsymmetricTransition_of_ne
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (q : ι → ι → ℝ) {x y : ι} (hxy : x ≠ y) :
    mhAsymmetricTransition w q x y =
      mhAsymmetricAcceptedMove w q x y := by
  simp [mhAsymmetricTransition, hxy]

theorem mhAsymmetricTransition_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (q : ι → ι → ℝ)
    (hw : ∀ z, 0 < w z)
    (hq_nonneg : ∀ i j, 0 ≤ q i j)
    (hq_row_sum : ∀ i, ∑ j, q i j = 1)
    (x y : ι) :
    0 ≤ mhAsymmetricTransition w q x y := by
  by_cases hxy : x = y
  · subst y
    rw [mhAsymmetricTransition_self]
    exact sub_nonneg.mpr
      (mhAsymmetricLeavingMass_le_one w q hq_nonneg hq_row_sum x)
  · rw [mhAsymmetricTransition_of_ne w q hxy]
    exact mhAsymmetricAcceptedMove_nonneg w q hw hq_nonneg x y

theorem mhAsymmetricTransition_row_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (q : ι → ι → ℝ) (x : ι) :
    ∑ y, mhAsymmetricTransition w q x y = 1 := by
  have hoffDiagonal :
      (∑ y ∈ Finset.univ.erase x, mhAsymmetricTransition w q x y) =
        mhAsymmetricLeavingMass w q x := by
    apply Finset.sum_congr rfl
    intro y hy
    rw [mhAsymmetricTransition_of_ne w q]
    exact (Finset.mem_erase.mp hy).1.symm
  calc
    ∑ y, mhAsymmetricTransition w q x y =
        (∑ y ∈ Finset.univ.erase x, mhAsymmetricTransition w q x y) +
          mhAsymmetricTransition w q x x :=
      (Finset.sum_erase_add Finset.univ
        (fun y => mhAsymmetricTransition w q x y)
        (Finset.mem_univ x)).symm
    _ = mhAsymmetricLeavingMass w q x +
          (1 - mhAsymmetricLeavingMass w q x) := by
      rw [hoffDiagonal, mhAsymmetricTransition_self]
    _ = 1 := by ring

theorem mhAsymmetricTransition_detailed_balance
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (q : ι → ι → ℝ)
    (hw : ∀ z, 0 < w z) (hq_nonneg : ∀ i j, 0 ≤ q i j)
    (x y : ι) :
    w x * mhAsymmetricTransition w q x y =
      w y * mhAsymmetricTransition w q y x := by
  by_cases hxy : x = y
  · subst y
    rfl
  · rw [mhAsymmetricTransition_of_ne w q hxy]
    rw [mhAsymmetricTransition_of_ne w q (Ne.symm hxy)]
    exact mhAsymmetricAcceptedMove_balance w q hw hq_nonneg x y

theorem normalizedWeight_mhAsymmetricTransition_detailed_balance
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (q : ι → ι → ℝ)
    (hw : ∀ z, 0 < w z) (hq_nonneg : ∀ i j, 0 ≤ q i j)
    (x y : ι) :
    normalizedWeight w x * mhAsymmetricTransition w q x y =
      normalizedWeight w y * mhAsymmetricTransition w q y x := by
  calc
    normalizedWeight w x * mhAsymmetricTransition w q x y =
        (w x * mhAsymmetricTransition w q x y) / totalWeight w := by
      simp [normalizedWeight]
      ring
    _ = (w y * mhAsymmetricTransition w q y x) / totalWeight w := by
      rw [mhAsymmetricTransition_detailed_balance w q hw hq_nonneg x y]
    _ = normalizedWeight w y * mhAsymmetricTransition w q y x := by
      simp [normalizedWeight]
      ring

/-- The normalized target weights are stationary for asymmetric finite-state
Metropolis--Hastings. -/
theorem mhAsymmetricTransition_stationary
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (q : ι → ι → ℝ)
    (hw : ∀ z, 0 < w z) (hq_nonneg : ∀ i j, 0 ≤ q i j)
    (y : ι) :
    ∑ x, normalizedWeight w x * mhAsymmetricTransition w q x y =
      normalizedWeight w y := by
  exact stationary_of_detailed_balance
    (normalizedWeight w) (mhAsymmetricTransition w q)
    (mhAsymmetricTransition_row_sum w q)
    (normalizedWeight_mhAsymmetricTransition_detailed_balance
      w q hw hq_nonneg)
    y

theorem mhAsymmetricTransition_is_stochastic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (q : ι → ι → ℝ)
    (hw : ∀ z, 0 < w z)
    (hq_nonneg : ∀ i j, 0 ≤ q i j)
    (hq_row_sum : ∀ i, ∑ j, q i j = 1) :
    (∀ x y, 0 ≤ mhAsymmetricTransition w q x y) ∧
      ∀ x, ∑ y, mhAsymmetricTransition w q x y = 1 := by
  constructor
  · exact mhAsymmetricTransition_nonneg w q hw hq_nonneg hq_row_sum
  · exact mhAsymmetricTransition_row_sum w q

/-- End-to-end correctness certificate for finite asymmetric-proposal MH. -/
theorem mhAsymmetricTransition_correct
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (w : ι → ℝ) (q : ι → ι → ℝ)
    (hw : ∀ z, 0 < w z)
    (hq_nonneg : ∀ i j, 0 ≤ q i j)
    (hq_row_sum : ∀ i, ∑ j, q i j = 1) :
    (∀ x, 0 ≤ normalizedWeight w x) ∧
    (∑ x, normalizedWeight w x = 1) ∧
    (∀ x y, 0 ≤ mhAsymmetricTransition w q x y) ∧
    (∀ x, ∑ y, mhAsymmetricTransition w q x y = 1) ∧
    (∀ x y,
      normalizedWeight w x * mhAsymmetricTransition w q x y =
        normalizedWeight w y * mhAsymmetricTransition w q y x) ∧
    (∀ y, ∑ x, normalizedWeight w x * mhAsymmetricTransition w q x y =
      normalizedWeight w y) := by
  constructor
  · exact normalizedWeight_nonneg w hw
  constructor
  · exact normalizedWeight_sum w hw
  constructor
  · exact mhAsymmetricTransition_nonneg w q hw hq_nonneg hq_row_sum
  constructor
  · exact mhAsymmetricTransition_row_sum w q
  constructor
  · exact normalizedWeight_mhAsymmetricTransition_detailed_balance
      w q hw hq_nonneg
  · exact mhAsymmetricTransition_stationary w q hw hq_nonneg

end LeanMetro
