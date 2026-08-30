import LeanMetro.DirichletForm

namespace LeanMetro

/-- The expectation of a real function with respect to a finite mass
function. -/
noncomputable def weightedMean
    {ι : Type*} [Fintype ι]
    (π f : ι → ℝ) : ℝ :=
  ∑ x, π x * f x

/-- A function is centered when its weighted mean is zero. -/
def MeanZero
    {ι : Type*} [Fintype ι]
    (π f : ι → ℝ) : Prop :=
  weightedMean π f = 0

theorem weightedMean_add
    {ι : Type*} [Fintype ι]
    (π f g : ι → ℝ) :
    weightedMean π (fun x => f x + g x) =
      weightedMean π f + weightedMean π g := by
  unfold weightedMean
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem weightedMean_sub
    {ι : Type*} [Fintype ι]
    (π f g : ι → ℝ) :
    weightedMean π (fun x => f x - g x) =
      weightedMean π f - weightedMean π g := by
  unfold weightedMean
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem weightedMean_smul
    {ι : Type*} [Fintype ι]
    (π f : ι → ℝ) (c : ℝ) :
    weightedMean π (fun x => c * f x) = c * weightedMean π f := by
  unfold weightedMean
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

namespace MeanZero

theorem zero
    {ι : Type*} [Fintype ι] (π : ι → ℝ) :
    MeanZero π (fun _ => 0) := by
  simp [MeanZero, weightedMean]

theorem add
    {ι : Type*} [Fintype ι] {π f g : ι → ℝ}
    (hf : MeanZero π f) (hg : MeanZero π g) :
    MeanZero π (fun x => f x + g x) := by
  unfold MeanZero at *
  rw [weightedMean_add, hf, hg, add_zero]

theorem sub
    {ι : Type*} [Fintype ι] {π f g : ι → ℝ}
    (hf : MeanZero π f) (hg : MeanZero π g) :
    MeanZero π (fun x => f x - g x) := by
  unfold MeanZero at *
  rw [weightedMean_sub, hf, hg, sub_zero]

theorem smul
    {ι : Type*} [Fintype ι] {π f : ι → ℝ}
    (hf : MeanZero π f) (c : ℝ) :
    MeanZero π (fun x => c * f x) := by
  unfold MeanZero at *
  rw [weightedMean_smul, hf, mul_zero]

end MeanZero

/-- The discrete Laplacian `I - P` associated with a finite Markov kernel. -/
noncomputable def laplacianOperator
    {ι : Type*} [Fintype ι]
    (P : FiniteKernel ι) (f : ι → ℝ) (x : ι) : ℝ :=
  f x - markovOperator P f x

theorem laplacianOperator_sub
    {ι : Type*} [Fintype ι]
    (P : FiniteKernel ι) (f g : ι → ℝ) :
    laplacianOperator P (fun x => f x - g x) =
      fun x => laplacianOperator P f x - laplacianOperator P g x := by
  funext x
  unfold laplacianOperator
  rw [markovOperator_sub]
  ring

theorem laplacianOperator_constant
    {ι : Type*} [Fintype ι]
    (P : FiniteKernel ι) (c : ℝ) :
    laplacianOperator P (fun _ => c) = fun _ => 0 := by
  funext x
  unfold laplacianOperator markovOperator
  calc
    c - ∑ y, P.prob x y * c =
        c - (∑ y, P.prob x y) * c := by rw [Finset.sum_mul]
    _ = 0 := by rw [P.row_sum x]; ring

theorem weightedMean_markovOperator
    {ι : Type*} [Fintype ι]
    (π f : ι → ℝ) (P : FiniteKernel ι)
    (hstat : P.StationaryFor π) :
    weightedMean π (markovOperator P f) = weightedMean π f := by
  unfold weightedMean markovOperator
  calc
    (∑ x, π x * ∑ y, P.prob x y * f y) =
        ∑ x, ∑ y, π x * P.prob x y * f y := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ = ∑ y, ∑ x, π x * P.prob x y * f y := by
      rw [Finset.sum_comm]
    _ = ∑ y, (∑ x, π x * P.prob x y) * f y := by
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.sum_mul]
    _ = ∑ y, π y * f y := by
      apply Finset.sum_congr rfl
      intro y _
      rw [hstat y]

theorem laplacianOperator_meanZero
    {ι : Type*} [Fintype ι]
    (π f : ι → ℝ) (P : FiniteKernel ι)
    (hstat : P.StationaryFor π) :
    MeanZero π (laplacianOperator P f) := by
  unfold MeanZero laplacianOperator
  rw [weightedMean_sub]
  rw [weightedMean_markovOperator π f P hstat]
  exact sub_self _

/-- A spectral-style assumption saying that the only fixed functions of `P`
are constants. Finite irreducible chains satisfy this property, but the first
Poisson layer keeps it as an explicit hypothesis. -/
def FixedPointsAreConstants
    {ι : Type*} [Fintype ι]
    (P : FiniteKernel ι) : Prop :=
  ∀ f : ι → ℝ,
    (∀ x, markovOperator P f x = f x) →
      ∃ c : ℝ, ∀ x, f x = c

/-- Under the fixed-point hypothesis, `I-P` is injective after restricting to
mean-zero functions. -/
theorem laplacianOperator_injective_on_meanZero
    {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (P : FiniteKernel ι)
    (hπ_sum : ∑ x, π x = 1)
    (hfixed : FixedPointsAreConstants P)
    {f g : ι → ℝ}
    (hf : MeanZero π f) (hg : MeanZero π g)
    (hL : laplacianOperator P f = laplacianOperator P g) :
    f = g := by
  let d : ι → ℝ := fun x => f x - g x
  have hd_mean : MeanZero π d := by
    exact hf.sub hg
  have hd_fixed : ∀ x, markovOperator P d x = d x := by
    intro x
    have hpoint := congrFun hL x
    have hzero : laplacianOperator P d x = 0 := by
      rw [show laplacianOperator P d =
          fun z => laplacianOperator P f z - laplacianOperator P g z by
        simpa [d] using laplacianOperator_sub P f g]
      change laplacianOperator P f x - laplacianOperator P g x = 0
      rw [hpoint, sub_self]
    unfold laplacianOperator at hzero
    linarith
  obtain ⟨c, hc⟩ := hfixed d hd_fixed
  have hmean_eq_c : weightedMean π d = c := by
    calc
      weightedMean π d = ∑ x, π x * c := by
        unfold weightedMean
        apply Finset.sum_congr rfl
        intro x _
        rw [hc x]
      _ = (∑ x, π x) * c := by rw [Finset.sum_mul]
      _ = c := by rw [hπ_sum, one_mul]
  have hc_zero : c = 0 := by
    calc
      c = weightedMean π d := hmean_eq_c.symm
      _ = 0 := hd_mean
  funext x
  have hdx := hc x
  rw [hc_zero] at hdx
  exact sub_eq_zero.mp hdx

theorem dirichletForm_eq_weightedInner_laplacian
    {ι : Type*} [Fintype ι]
    (π f : ι → ℝ) (P : FiniteKernel ι)
    (hrev : P.ReversibleFor π) :
    dirichletForm π P f =
      weightedInner π f (laplacianOperator P f) := by
  rw [dirichletForm_eq_weightedInner_sub π f P hrev]
  unfold laplacianOperator
  rw [weightedInner_sub_right]

end LeanMetro
