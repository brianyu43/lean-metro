import LeanMetro.MarkovKernel

namespace LeanMetro

/-- Real bilinear pairing weighted by a finite mass function `π`. -/
noncomputable def weightedInner
    {ι : Type*} [Fintype ι]
    (π f g : ι → ℝ) : ℝ :=
  ∑ x, π x * f x * g x

/-- The Markov operator associated with a finite kernel. -/
noncomputable def markovOperator
    {ι : Type*} [Fintype ι]
    (P : FiniteKernel ι) (f : ι → ℝ) (x : ι) : ℝ :=
  ∑ y, P.prob x y * f y

theorem weightedInner_comm
    {ι : Type*} [Fintype ι]
    (π f g : ι → ℝ) :
    weightedInner π f g = weightedInner π g f := by
  unfold weightedInner
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem weightedInner_add_left
    {ι : Type*} [Fintype ι]
    (π f g h : ι → ℝ) :
    weightedInner π (fun x => f x + g x) h =
      weightedInner π f h + weightedInner π g h := by
  unfold weightedInner
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem weightedInner_add_right
    {ι : Type*} [Fintype ι]
    (π f g h : ι → ℝ) :
    weightedInner π f (fun x => g x + h x) =
      weightedInner π f g + weightedInner π f h := by
  unfold weightedInner
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem weightedInner_sub_left
    {ι : Type*} [Fintype ι]
    (π f g h : ι → ℝ) :
    weightedInner π (fun x => f x - g x) h =
      weightedInner π f h - weightedInner π g h := by
  unfold weightedInner
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem weightedInner_sub_right
    {ι : Type*} [Fintype ι]
    (π f g h : ι → ℝ) :
    weightedInner π f (fun x => g x - h x) =
      weightedInner π f g - weightedInner π f h := by
  unfold weightedInner
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem weightedInner_smul_left
    {ι : Type*} [Fintype ι]
    (π f g : ι → ℝ) (c : ℝ) :
    weightedInner π (fun x => c * f x) g =
      c * weightedInner π f g := by
  unfold weightedInner
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem markovOperator_add
    {ι : Type*} [Fintype ι]
    (P : FiniteKernel ι) (f g : ι → ℝ) (x : ι) :
    markovOperator P (fun y => f y + g y) x =
      markovOperator P f x + markovOperator P g x := by
  unfold markovOperator
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem markovOperator_sub
    {ι : Type*} [Fintype ι]
    (P : FiniteKernel ι) (f g : ι → ℝ) (x : ι) :
    markovOperator P (fun y => f y - g y) x =
      markovOperator P f x - markovOperator P g x := by
  unfold markovOperator
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem markovOperator_smul
    {ι : Type*} [Fintype ι]
    (P : FiniteKernel ι) (f : ι → ℝ) (c : ℝ) (x : ι) :
    markovOperator P (fun y => c * f y) x =
      c * markovOperator P f x := by
  unfold markovOperator
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem markovOperator_one
    {ι : Type*} [Fintype ι]
    (P : FiniteKernel ι) (x : ι) :
    markovOperator P (fun _ => 1) x = 1 := by
  simpa [markovOperator] using P.row_sum x

/-- Reversibility is exactly self-adjointness of the Markov operator in the
`π`-weighted pairing. -/
theorem weightedInner_markovOperator_selfAdjoint
    {ι : Type*} [Fintype ι]
    (P : FiniteKernel ι) (π f g : ι → ℝ)
    (hrev : P.ReversibleFor π) :
    weightedInner π f (markovOperator P g) =
      weightedInner π (markovOperator P f) g := by
  calc
    weightedInner π f (markovOperator P g) =
        ∑ x, ∑ y, π x * P.prob x y * f x * g y := by
      unfold weightedInner markovOperator
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ = ∑ y, ∑ x, π x * P.prob x y * f x * g y := by
      rw [Finset.sum_comm]
    _ = ∑ y, ∑ x, π y * P.prob y x * f x * g y := by
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro x _
      rw [hrev x y]
    _ = weightedInner π (markovOperator P f) g := by
      unfold weightedInner markovOperator
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      ring

end LeanMetro
