import LeanMetro.Transition

namespace LeanMetro

/-- The complete finite-state MH transition satisfies detailed balance for a
symmetric proposal.  Off the diagonal this is the scalar acceptance identity;
on the diagonal both sides are literally the same expression. -/
theorem mhTransition_detailed_balance
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (q : ι → ι → ℝ)
    (hw : ∀ z, 0 < w z)
    (hq_symmetric : ∀ i j, q i j = q j i)
    (x y : ι) :
    w x * mhTransition w q x y =
      w y * mhTransition w q y x := by
  by_cases hxy : x = y
  · subst y
    rfl
  · rw [mhTransition_of_ne w q hxy]
    rw [mhTransition_of_ne w q (Ne.symm hxy)]
    exact mh_balance_symmetric_proposal
      w q (hw x) (hw y) (hq_symmetric x y)

/-- Detailed balance and row normalization imply stationarity on a finite
state space. -/
theorem stationary_of_detailed_balance
    {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (P : ι → ι → ℝ)
    (hrow : ∀ x, ∑ y, P x y = 1)
    (hbalance : ∀ x y, π x * P x y = π y * P y x)
    (y : ι) :
    ∑ x, π x * P x y = π y := by
  calc
    ∑ x, π x * P x y = ∑ x, π y * P y x := by
      apply Finset.sum_congr rfl
      intro x _
      exact hbalance x y
    _ = π y * ∑ x, P y x := by
      rw [Finset.mul_sum]
    _ = π y := by
      rw [hrow y, mul_one]

/-- Total unnormalized target mass. -/
noncomputable def totalWeight
    {ι : Type*} [Fintype ι] (w : ι → ℝ) : ℝ :=
  ∑ x, w x

/-- Normalize positive finite weights to total mass one. -/
noncomputable def normalizedWeight
    {ι : Type*} [Fintype ι] (w : ι → ℝ) (x : ι) : ℝ :=
  w x / totalWeight w

theorem totalWeight_pos
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (w : ι → ℝ) (hw : ∀ x, 0 < w x) :
    0 < totalWeight w := by
  unfold totalWeight
  have huniv : (Finset.univ : Finset ι).Nonempty :=
    ⟨Classical.choice inferInstance, Finset.mem_univ _⟩
  exact Finset.sum_pos (fun x _ => hw x) huniv

theorem normalizedWeight_nonneg
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (w : ι → ℝ) (hw : ∀ x, 0 < w x) (x : ι) :
    0 ≤ normalizedWeight w x := by
  exact div_nonneg (hw x).le (totalWeight_pos w hw).le

theorem normalizedWeight_sum
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (w : ι → ℝ) (hw : ∀ x, 0 < w x) :
    ∑ x, normalizedWeight w x = 1 := by
  unfold normalizedWeight
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (totalWeight_pos w hw))

/-- Scaling all weights by the same normalizer preserves detailed balance. -/
theorem normalizedWeight_mhTransition_detailed_balance
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (q : ι → ι → ℝ)
    (hw : ∀ z, 0 < w z)
    (hq_symmetric : ∀ i j, q i j = q j i)
    (x y : ι) :
    normalizedWeight w x * mhTransition w q x y =
      normalizedWeight w y * mhTransition w q y x := by
  calc
    normalizedWeight w x * mhTransition w q x y =
        (w x * mhTransition w q x y) / totalWeight w := by
      simp [normalizedWeight]
      ring
    _ = (w y * mhTransition w q y x) / totalWeight w := by
      rw [mhTransition_detailed_balance w q hw hq_symmetric x y]
    _ = normalizedWeight w y * mhTransition w q y x := by
      simp [normalizedWeight]
      ring

/-- For a symmetric proposal, the normalized target weights are stationary for
the complete MH transition. -/
theorem mhTransition_stationary
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (q : ι → ι → ℝ)
    (hw : ∀ z, 0 < w z)
    (hq_symmetric : ∀ i j, q i j = q j i)
    (y : ι) :
    ∑ x, normalizedWeight w x * mhTransition w q x y =
      normalizedWeight w y := by
  exact stationary_of_detailed_balance
    (normalizedWeight w) (mhTransition w q)
    (mhTransition_row_sum w q)
    (normalizedWeight_mhTransition_detailed_balance w q hw hq_symmetric)
    y

/-- The assumptions that make the symmetric MH transition a stochastic
matrix, collected as a convenient final interface. -/
theorem mhTransition_is_stochastic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (q : ι → ι → ℝ)
    (hw : ∀ z, 0 < w z)
    (hq_nonneg : ∀ i j, 0 ≤ q i j)
    (hq_row_sum : ∀ i, ∑ j, q i j = 1) :
    (∀ x y, 0 ≤ mhTransition w q x y) ∧
      ∀ x, ∑ y, mhTransition w q x y = 1 := by
  constructor
  · exact mhTransition_nonneg w q hw hq_nonneg hq_row_sum
  · exact mhTransition_row_sum w q

/-- End-to-end correctness certificate for finite symmetric-proposal MH. -/
theorem mhTransition_correct
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (w : ι → ℝ) (q : ι → ι → ℝ)
    (hw : ∀ z, 0 < w z)
    (hq_nonneg : ∀ i j, 0 ≤ q i j)
    (hq_row_sum : ∀ i, ∑ j, q i j = 1)
    (hq_symmetric : ∀ i j, q i j = q j i) :
    (∀ x, 0 ≤ normalizedWeight w x) ∧
    (∑ x, normalizedWeight w x = 1) ∧
    (∀ x y, 0 ≤ mhTransition w q x y) ∧
    (∀ x, ∑ y, mhTransition w q x y = 1) ∧
    (∀ x y,
      normalizedWeight w x * mhTransition w q x y =
        normalizedWeight w y * mhTransition w q y x) ∧
    (∀ y, ∑ x, normalizedWeight w x * mhTransition w q x y =
      normalizedWeight w y) := by
  constructor
  · exact normalizedWeight_nonneg w hw
  constructor
  · exact normalizedWeight_sum w hw
  constructor
  · exact mhTransition_nonneg w q hw hq_nonneg hq_row_sum
  constructor
  · exact mhTransition_row_sum w q
  constructor
  · exact normalizedWeight_mhTransition_detailed_balance
      w q hw hq_symmetric
  · exact mhTransition_stationary w q hw hq_symmetric

end LeanMetro
