import LeanMetro.WeightedSpace

namespace LeanMetro

/-- The Dirichlet form of a finite kernel, written in its symmetric
sum-of-squared-differences form. -/
noncomputable def dirichletForm
    {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (P : FiniteKernel ι) (f : ι → ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    ∑ x, ∑ y, π x * P.prob x y * (f x - f y) ^ 2

theorem weightedTransition_sourceSquare
    {ι : Type*} [Fintype ι]
    (π f : ι → ℝ) (P : FiniteKernel ι) :
    (∑ x, ∑ y, π x * P.prob x y * (f x) ^ 2) =
      weightedInner π f f := by
  unfold weightedInner
  apply Finset.sum_congr rfl
  intro x _
  calc
    (∑ y, π x * P.prob x y * (f x) ^ 2) =
        (π x * (f x) ^ 2) * ∑ y, P.prob x y := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ = π x * (f x) ^ 2 := by rw [P.row_sum x, mul_one]
    _ = π x * f x * f x := by ring

theorem weightedTransition_targetSquare
    {ι : Type*} [Fintype ι]
    (π f : ι → ℝ) (P : FiniteKernel ι)
    (hstat : P.StationaryFor π) :
    (∑ x, ∑ y, π x * P.prob x y * (f y) ^ 2) =
      weightedInner π f f := by
  rw [Finset.sum_comm]
  unfold weightedInner
  apply Finset.sum_congr rfl
  intro y _
  calc
    (∑ x, π x * P.prob x y * (f y) ^ 2) =
        (∑ x, π x * P.prob x y) * (f y) ^ 2 := by
      rw [Finset.sum_mul]
    _ = π y * (f y) ^ 2 := by rw [hstat y]
    _ = π y * f y * f y := by ring

theorem weightedTransition_cross
    {ι : Type*} [Fintype ι]
    (π f : ι → ℝ) (P : FiniteKernel ι) :
    (∑ x, ∑ y, π x * P.prob x y * f x * f y) =
      weightedInner π f (markovOperator P f) := by
  unfold weightedInner markovOperator
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

/-- For a reversible kernel, the squared-difference definition of the
Dirichlet form equals `<f,f>_π - <f,Pf>_π`. -/
theorem dirichletForm_eq_weightedInner_sub
    {ι : Type*} [Fintype ι]
    (π f : ι → ℝ) (P : FiniteKernel ι)
    (hrev : P.ReversibleFor π) :
    dirichletForm π P f =
      weightedInner π f f - weightedInner π f (markovOperator P f) := by
  have hexpand :
      (∑ x, ∑ y, π x * P.prob x y * (f x - f y) ^ 2) =
        (∑ x, ∑ y, π x * P.prob x y * (f x) ^ 2) -
          ((∑ x, ∑ y, π x * P.prob x y * f x * f y) +
            (∑ x, ∑ y, π x * P.prob x y * f x * f y)) +
          (∑ x, ∑ y, π x * P.prob x y * (f y) ^ 2) := by
    calc
      (∑ x, ∑ y, π x * P.prob x y * (f x - f y) ^ 2) =
          ∑ x, ∑ y,
            (π x * P.prob x y * (f x) ^ 2 -
              (π x * P.prob x y * f x * f y +
                π x * P.prob x y * f x * f y) +
              π x * P.prob x y * (f y) ^ 2) := by
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro y _
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  unfold dirichletForm
  rw [hexpand]
  rw [weightedTransition_sourceSquare π f P]
  rw [weightedTransition_cross π f P]
  rw [weightedTransition_targetSquare π f P hrev.stationary]
  ring

/-- Increasing every off-diagonal transition probability increases the
Dirichlet form for every test function. -/
theorem dirichletForm_mono_of_peskunDominates
    {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (P₁ P₂ : FiniteKernel ι)
    (hπ_nonneg : ∀ x, 0 ≤ π x)
    (hdom : PeskunDominates P₁ P₂)
    (f : ι → ℝ) :
    dirichletForm π P₂ f ≤ dirichletForm π P₁ f := by
  unfold dirichletForm
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro x _
  apply Finset.sum_le_sum
  intro y _
  by_cases hxy : x = y
  · subst y
    simp
  · have hprob : P₂.prob x y ≤ P₁.prob x y := hdom hxy
    have hweighted :
        π x * P₂.prob x y ≤ π x * P₁.prob x y :=
      mul_le_mul_of_nonneg_left hprob (hπ_nonneg x)
    exact mul_le_mul_of_nonneg_right hweighted (sq_nonneg (f x - f y))

/-- With fixed target and proposal, MH maximizes the Dirichlet form among all
admissible accept/reject rules. -/
theorem metropolisHastings_dirichletForm_maximal
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (w : ι → ℝ) (q a : ι → ι → ℝ)
    (hw : ∀ x, 0 < w x)
    (hq_nonneg : ∀ x y, 0 ≤ q x y)
    (hq_row_sum : ∀ x, ∑ y, q x y = 1)
    (ha : AdmissibleAcceptance w q a)
    (f : ι → ℝ) :
    dirichletForm (normalizedWeight w)
        (acceptRejectKernel q a hq_nonneg hq_row_sum ha.nonneg ha.le_one) f ≤
      dirichletForm (normalizedWeight w)
        (metropolisHastingsKernel w q hw hq_nonneg hq_row_sum) f := by
  exact dirichletForm_mono_of_peskunDominates
    (normalizedWeight w)
    (metropolisHastingsKernel w q hw hq_nonneg hq_row_sum)
    (acceptRejectKernel q a hq_nonneg hq_row_sum ha.nonneg ha.le_one)
    (normalizedWeight_nonneg w hw)
    (metropolisHastingsKernel_peskunDominates
      w q a hw hq_nonneg hq_row_sum ha)
    f

end LeanMetro
