import LeanMetro.OffDiagonal

namespace LeanMetro

/-- The Metropolis acceptance probability is nonnegative for positive target weights. -/
theorem mhAcceptance_nonneg
    {ι : Type*} (w : ι → ℝ) {x y : ι}
    (hx : 0 < w x) (hy : 0 < w y) :
    0 ≤ mhAcceptance w x y := by
  unfold mhAcceptance
  exact le_min zero_le_one (div_nonneg hy.le hx.le)

/-- The Metropolis acceptance probability never exceeds one. -/
theorem mhAcceptance_le_one
    {ι : Type*} (w : ι → ℝ) (x y : ι) :
    mhAcceptance w x y ≤ 1 := by
  unfold mhAcceptance
  exact min_le_left _ _

/-- Probability mass that proposes and accepts a move from `x` to `y`. -/
noncomputable def mhAcceptedMove
    {ι : Type*} (w : ι → ℝ) (q : ι → ι → ℝ) (x y : ι) : ℝ :=
  q x y * mhAcceptance w x y

theorem mhAcceptedMove_nonneg
    {ι : Type*}
    (w : ι → ℝ) (q : ι → ι → ℝ)
    (hw : ∀ z, 0 < w z) (hq_nonneg : ∀ i j, 0 ≤ q i j)
    (x y : ι) :
    0 ≤ mhAcceptedMove w q x y := by
  exact mul_nonneg (hq_nonneg x y) (mhAcceptance_nonneg w (hw x) (hw y))

theorem mhAcceptedMove_le_proposal
    {ι : Type*}
    (w : ι → ℝ) (q : ι → ι → ℝ)
    (hq_nonneg : ∀ i j, 0 ≤ q i j)
    (x y : ι) :
    mhAcceptedMove w q x y ≤ q x y := by
  exact mul_le_of_le_one_right (hq_nonneg x y) (mhAcceptance_le_one w x y)

/-- Total accepted probability mass that leaves state `x`. -/
noncomputable def mhLeavingMass
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (q : ι → ι → ℝ) (x : ι) : ℝ :=
  ∑ y ∈ Finset.univ.erase x, mhAcceptedMove w q x y

theorem mhLeavingMass_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (q : ι → ι → ℝ)
    (hw : ∀ z, 0 < w z) (hq_nonneg : ∀ i j, 0 ≤ q i j)
    (x : ι) :
    0 ≤ mhLeavingMass w q x := by
  apply Finset.sum_nonneg
  intro y _
  exact mhAcceptedMove_nonneg w q hw hq_nonneg x y

theorem mhLeavingMass_le_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (q : ι → ι → ℝ)
    (hq_nonneg : ∀ i j, 0 ≤ q i j)
    (hq_row_sum : ∀ i, ∑ j, q i j = 1)
    (x : ι) :
    mhLeavingMass w q x ≤ 1 := by
  have haccepted_le :
      (∑ y ∈ Finset.univ.erase x, mhAcceptedMove w q x y) ≤
        ∑ y ∈ Finset.univ.erase x, q x y := by
    apply Finset.sum_le_sum
    intro y _
    exact mhAcceptedMove_le_proposal w q hq_nonneg x y
  have hsplit :
      (∑ y ∈ Finset.univ.erase x, q x y) + q x x = 1 := by
    calc
      (∑ y ∈ Finset.univ.erase x, q x y) + q x x =
          ∑ y ∈ Finset.univ, q x y :=
        Finset.sum_erase_add Finset.univ (fun y => q x y) (Finset.mem_univ x)
      _ = 1 := hq_row_sum x
  unfold mhLeavingMass
  linarith [hq_nonneg x x]

/-- Finite-state MH transition: accepted moves off diagonal and leftover mass on diagonal. -/
noncomputable def mhTransition
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (q : ι → ι → ℝ) (x y : ι) : ℝ :=
  if x = y then 1 - mhLeavingMass w q x else mhAcceptedMove w q x y

@[simp]
theorem mhTransition_self
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (q : ι → ι → ℝ) (x : ι) :
    mhTransition w q x x = 1 - mhLeavingMass w q x := by
  simp [mhTransition]

theorem mhTransition_of_ne
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (q : ι → ι → ℝ) {x y : ι} (hxy : x ≠ y) :
    mhTransition w q x y = mhAcceptedMove w q x y := by
  simp [mhTransition, hxy]

theorem mhTransition_self_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (q : ι → ι → ℝ)
    (hq_nonneg : ∀ i j, 0 ≤ q i j)
    (hq_row_sum : ∀ i, ∑ j, q i j = 1)
    (x : ι) :
    0 ≤ mhTransition w q x x := by
  rw [mhTransition_self]
  exact sub_nonneg.mpr (mhLeavingMass_le_one w q hq_nonneg hq_row_sum x)

theorem mhTransition_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (q : ι → ι → ℝ)
    (hw : ∀ z, 0 < w z)
    (hq_nonneg : ∀ i j, 0 ≤ q i j)
    (hq_row_sum : ∀ i, ∑ j, q i j = 1)
    (x y : ι) :
    0 ≤ mhTransition w q x y := by
  by_cases hxy : x = y
  · subst y
    exact mhTransition_self_nonneg w q hq_nonneg hq_row_sum x
  · rw [mhTransition_of_ne w q hxy]
    exact mhAcceptedMove_nonneg w q hw hq_nonneg x y

theorem mhTransition_row_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (q : ι → ι → ℝ) (x : ι) :
    ∑ y, mhTransition w q x y = 1 := by
  have hoffDiagonal :
      (∑ y ∈ Finset.univ.erase x, mhTransition w q x y) =
        mhLeavingMass w q x := by
    apply Finset.sum_congr rfl
    intro y hy
    rw [mhTransition_of_ne w q]
    exact (Finset.mem_erase.mp hy).1.symm
  calc
    ∑ y, mhTransition w q x y =
        (∑ y ∈ Finset.univ.erase x, mhTransition w q x y) +
          mhTransition w q x x :=
      (Finset.sum_erase_add Finset.univ (fun y => mhTransition w q x y)
        (Finset.mem_univ x)).symm
    _ = mhLeavingMass w q x + (1 - mhLeavingMass w q x) := by
      rw [hoffDiagonal, mhTransition_self]
    _ = 1 := by ring

end LeanMetro
