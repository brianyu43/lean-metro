import LeanMetro.Asymmetric

namespace LeanMetro

/-- An acceptance rule is admissible for target weights `w` and proposal `q`
when it takes values in `[0,1]` and its accepted probability flow is balanced
in both directions. -/
structure AdmissibleAcceptance
    {ι : Type*} (w : ι → ℝ) (q a : ι → ι → ℝ) : Prop where
  nonneg : ∀ x y, 0 ≤ a x y
  le_one : ∀ x y, a x y ≤ 1
  balance : ∀ x y,
    (w x * q x y) * a x y = (w y * q y x) * a y x

/-- Probability mass that proposes and accepts a generic move. -/
noncomputable def acceptRejectAcceptedMove
    {ι : Type*} (q a : ι → ι → ℝ) (x y : ι) : ℝ :=
  q x y * a x y

theorem acceptRejectAcceptedMove_nonneg
    {ι : Type*} (q a : ι → ι → ℝ)
    (hq_nonneg : ∀ x y, 0 ≤ q x y)
    (ha_nonneg : ∀ x y, 0 ≤ a x y)
    (x y : ι) :
    0 ≤ acceptRejectAcceptedMove q a x y := by
  exact mul_nonneg (hq_nonneg x y) (ha_nonneg x y)

theorem acceptRejectAcceptedMove_le_proposal
    {ι : Type*} (q a : ι → ι → ℝ)
    (hq_nonneg : ∀ x y, 0 ≤ q x y)
    (ha_le_one : ∀ x y, a x y ≤ 1)
    (x y : ι) :
    acceptRejectAcceptedMove q a x y ≤ q x y := by
  exact mul_le_of_le_one_right (hq_nonneg x y) (ha_le_one x y)

theorem acceptRejectAcceptedMove_balance
    {ι : Type*} (w : ι → ℝ) (q a : ι → ι → ℝ)
    (ha : AdmissibleAcceptance w q a) (x y : ι) :
    w x * acceptRejectAcceptedMove q a x y =
      w y * acceptRejectAcceptedMove q a y x := by
  unfold acceptRejectAcceptedMove
  simpa [mul_assoc] using ha.balance x y

/-- Total accepted mass that leaves state `x` under a generic acceptance rule. -/
noncomputable def acceptRejectLeavingMass
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q a : ι → ι → ℝ) (x : ι) : ℝ :=
  ∑ y ∈ Finset.univ.erase x, acceptRejectAcceptedMove q a x y

theorem acceptRejectLeavingMass_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q a : ι → ι → ℝ)
    (hq_nonneg : ∀ x y, 0 ≤ q x y)
    (ha_nonneg : ∀ x y, 0 ≤ a x y)
    (x : ι) :
    0 ≤ acceptRejectLeavingMass q a x := by
  apply Finset.sum_nonneg
  intro y _
  exact acceptRejectAcceptedMove_nonneg q a hq_nonneg ha_nonneg x y

theorem acceptRejectLeavingMass_le_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q a : ι → ι → ℝ)
    (hq_nonneg : ∀ x y, 0 ≤ q x y)
    (hq_row_sum : ∀ x, ∑ y, q x y = 1)
    (ha_le_one : ∀ x y, a x y ≤ 1)
    (x : ι) :
    acceptRejectLeavingMass q a x ≤ 1 := by
  have haccepted_le :
      (∑ y ∈ Finset.univ.erase x, acceptRejectAcceptedMove q a x y) ≤
        ∑ y ∈ Finset.univ.erase x, q x y := by
    apply Finset.sum_le_sum
    intro y _
    exact acceptRejectAcceptedMove_le_proposal q a hq_nonneg ha_le_one x y
  have hsplit :
      (∑ y ∈ Finset.univ.erase x, q x y) + q x x = 1 := by
    calc
      (∑ y ∈ Finset.univ.erase x, q x y) + q x x =
          ∑ y ∈ Finset.univ, q x y :=
        Finset.sum_erase_add Finset.univ (fun y => q x y) (Finset.mem_univ x)
      _ = 1 := hq_row_sum x
  unfold acceptRejectLeavingMass
  linarith [hq_nonneg x x]

/-- Complete accept/reject transition: accepted mass off the diagonal and all
remaining probability mass on the diagonal. -/
noncomputable def acceptRejectTransition
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q a : ι → ι → ℝ) (x y : ι) : ℝ :=
  if x = y then
    1 - acceptRejectLeavingMass q a x
  else
    acceptRejectAcceptedMove q a x y

@[simp]
theorem acceptRejectTransition_self
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q a : ι → ι → ℝ) (x : ι) :
    acceptRejectTransition q a x x =
      1 - acceptRejectLeavingMass q a x := by
  simp [acceptRejectTransition]

theorem acceptRejectTransition_of_ne
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q a : ι → ι → ℝ) {x y : ι} (hxy : x ≠ y) :
    acceptRejectTransition q a x y =
      acceptRejectAcceptedMove q a x y := by
  simp [acceptRejectTransition, hxy]

theorem acceptRejectTransition_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q a : ι → ι → ℝ)
    (hq_nonneg : ∀ x y, 0 ≤ q x y)
    (hq_row_sum : ∀ x, ∑ y, q x y = 1)
    (ha_nonneg : ∀ x y, 0 ≤ a x y)
    (ha_le_one : ∀ x y, a x y ≤ 1)
    (x y : ι) :
    0 ≤ acceptRejectTransition q a x y := by
  by_cases hxy : x = y
  · subst y
    rw [acceptRejectTransition_self]
    exact sub_nonneg.mpr
      (acceptRejectLeavingMass_le_one q a hq_nonneg hq_row_sum ha_le_one x)
  · rw [acceptRejectTransition_of_ne q a hxy]
    exact acceptRejectAcceptedMove_nonneg q a hq_nonneg ha_nonneg x y

theorem acceptRejectTransition_row_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q a : ι → ι → ℝ) (x : ι) :
    ∑ y, acceptRejectTransition q a x y = 1 := by
  have hoffDiagonal :
      (∑ y ∈ Finset.univ.erase x, acceptRejectTransition q a x y) =
        acceptRejectLeavingMass q a x := by
    apply Finset.sum_congr rfl
    intro y hy
    rw [acceptRejectTransition_of_ne q a]
    exact (Finset.mem_erase.mp hy).1.symm
  calc
    ∑ y, acceptRejectTransition q a x y =
        (∑ y ∈ Finset.univ.erase x, acceptRejectTransition q a x y) +
          acceptRejectTransition q a x x :=
      (Finset.sum_erase_add Finset.univ
        (fun y => acceptRejectTransition q a x y)
        (Finset.mem_univ x)).symm
    _ = acceptRejectLeavingMass q a x +
          (1 - acceptRejectLeavingMass q a x) := by
      rw [hoffDiagonal, acceptRejectTransition_self]
    _ = 1 := by ring

theorem acceptRejectTransition_detailed_balance
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (q a : ι → ι → ℝ)
    (ha : AdmissibleAcceptance w q a) (x y : ι) :
    w x * acceptRejectTransition q a x y =
      w y * acceptRejectTransition q a y x := by
  by_cases hxy : x = y
  · subst y
    rfl
  · rw [acceptRejectTransition_of_ne q a hxy]
    rw [acceptRejectTransition_of_ne q a (Ne.symm hxy)]
    exact acceptRejectAcceptedMove_balance w q a ha x y

theorem normalizedWeight_acceptRejectTransition_detailed_balance
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (q a : ι → ι → ℝ)
    (ha : AdmissibleAcceptance w q a) (x y : ι) :
    normalizedWeight w x * acceptRejectTransition q a x y =
      normalizedWeight w y * acceptRejectTransition q a y x := by
  calc
    normalizedWeight w x * acceptRejectTransition q a x y =
        (w x * acceptRejectTransition q a x y) / totalWeight w := by
      simp [normalizedWeight]
      ring
    _ = (w y * acceptRejectTransition q a y x) / totalWeight w := by
      rw [acceptRejectTransition_detailed_balance w q a ha x y]
    _ = normalizedWeight w y * acceptRejectTransition q a y x := by
      simp [normalizedWeight]
      ring

theorem acceptRejectTransition_stationary
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (q a : ι → ι → ℝ)
    (ha : AdmissibleAcceptance w q a) (y : ι) :
    ∑ x, normalizedWeight w x * acceptRejectTransition q a x y =
      normalizedWeight w y := by
  exact stationary_of_detailed_balance
    (normalizedWeight w) (acceptRejectTransition q a)
    (acceptRejectTransition_row_sum q a)
    (normalizedWeight_acceptRejectTransition_detailed_balance w q a ha)
    y

theorem acceptRejectTransition_correct
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (w : ι → ℝ) (q a : ι → ι → ℝ)
    (hw : ∀ x, 0 < w x)
    (hq_nonneg : ∀ x y, 0 ≤ q x y)
    (hq_row_sum : ∀ x, ∑ y, q x y = 1)
    (ha : AdmissibleAcceptance w q a) :
    (∀ x, 0 ≤ normalizedWeight w x) ∧
    (∑ x, normalizedWeight w x = 1) ∧
    (∀ x y, 0 ≤ acceptRejectTransition q a x y) ∧
    (∀ x, ∑ y, acceptRejectTransition q a x y = 1) ∧
    (∀ x y,
      normalizedWeight w x * acceptRejectTransition q a x y =
        normalizedWeight w y * acceptRejectTransition q a y x) ∧
    (∀ y, ∑ x, normalizedWeight w x * acceptRejectTransition q a x y =
      normalizedWeight w y) := by
  constructor
  · exact normalizedWeight_nonneg w hw
  constructor
  · exact normalizedWeight_sum w hw
  constructor
  · exact acceptRejectTransition_nonneg
      q a hq_nonneg hq_row_sum ha.nonneg ha.le_one
  constructor
  · exact acceptRejectTransition_row_sum q a
  constructor
  · exact normalizedWeight_acceptRejectTransition_detailed_balance w q a ha
  · exact acceptRejectTransition_stationary w q a ha

/-- The asymmetric MH acceptance rule is admissible. -/
theorem mhAsymmetricAcceptance_admissible
    {ι : Type*} (w : ι → ℝ) (q : ι → ι → ℝ)
    (hw : ∀ x, 0 < w x)
    (hq_nonneg : ∀ x y, 0 ≤ q x y) :
    AdmissibleAcceptance w q (mhAsymmetricAcceptance w q) := by
  constructor
  · exact mhAsymmetricAcceptance_nonneg w q hw hq_nonneg
  · exact mhAsymmetricAcceptance_le_one w q
  · intro x y
    simpa [mhAsymmetricAcceptedMove, mul_assoc] using
      mhAsymmetricAcceptedMove_balance w q hw hq_nonneg x y

/-- The generic completion instantiated with MH acceptance is definitionally
the previously verified asymmetric MH transition. -/
theorem acceptRejectTransition_mhAsymmetricAcceptance_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (q : ι → ι → ℝ) (x y : ι) :
    acceptRejectTransition q (mhAsymmetricAcceptance w q) x y =
      mhAsymmetricTransition w q x y := by
  rfl

/-- MH maximizes accepted move probability among every admissible acceptance
rule with the same target and proposal. -/
theorem mhAcceptedMove_maximal
    {ι : Type*} (w : ι → ℝ) (q a : ι → ι → ℝ)
    (hw : ∀ x, 0 < w x)
    (hq_nonneg : ∀ x y, 0 ≤ q x y)
    (ha : AdmissibleAcceptance w q a)
    (x y : ι) :
    acceptRejectAcceptedMove q a x y ≤
      mhAsymmetricAcceptedMove w q x y := by
  let A := w x * q x y
  let B := w y * q y x
  have hA : 0 ≤ A := mul_nonneg (hw x).le (hq_nonneg x y)
  have hB : 0 ≤ B := mul_nonneg (hw y).le (hq_nonneg y x)
  have hflow_le_A : A * a x y ≤ A :=
    mul_le_of_le_one_right hA (ha.le_one x y)
  have hflow_le_B : A * a x y ≤ B := by
    calc
      A * a x y = B * a y x := ha.balance x y
      _ ≤ B := mul_le_of_le_one_right hB (ha.le_one y x)
  have hflow_le_min : A * a x y ≤ min A B :=
    le_min hflow_le_A hflow_le_B
  have hweighted :
      w x * acceptRejectAcceptedMove q a x y ≤
        w x * mhAsymmetricAcceptedMove w q x y := by
    calc
      w x * acceptRejectAcceptedMove q a x y = A * a x y := by
        simp [acceptRejectAcceptedMove, A]
        ring
      _ ≤ min A B := hflow_le_min
      _ = A * min 1 (B / A) :=
        (nonneg_mul_acceptance_eq_min hA hB).symm
      _ = w x * mhAsymmetricAcceptedMove w q x y := by
        simp [mhAsymmetricAcceptedMove, mhAsymmetricAcceptance, A, B]
        ring
  nlinarith [hw x, hweighted]

/-- On every off-diagonal entry, the MH transition dominates the transition
from any other admissible acceptance rule with the same proposal. -/
theorem mhTransition_offDiagonal_dominates
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (q a : ι → ι → ℝ)
    (hw : ∀ x, 0 < w x)
    (hq_nonneg : ∀ x y, 0 ≤ q x y)
    (ha : AdmissibleAcceptance w q a)
    {x y : ι} (hxy : x ≠ y) :
    acceptRejectTransition q a x y ≤ mhAsymmetricTransition w q x y := by
  rw [acceptRejectTransition_of_ne q a hxy]
  rw [mhAsymmetricTransition_of_ne w q hxy]
  exact mhAcceptedMove_maximal w q a hw hq_nonneg ha x y

end LeanMetro
