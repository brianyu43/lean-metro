import LeanMetro.Poisson

namespace LeanMetro

theorem weightedInner_laplacian_selfAdjoint
    {ι : Type*} [Fintype ι]
    (π f g : ι → ℝ) (P : FiniteKernel ι)
    (hrev : P.ReversibleFor π) :
    weightedInner π f (laplacianOperator P g) =
      weightedInner π (laplacianOperator P f) g := by
  unfold laplacianOperator
  rw [weightedInner_sub_right, weightedInner_sub_left]
  rw [weightedInner_markovOperator_selfAdjoint P π f g hrev]

theorem dirichletForm_nonneg
    {ι : Type*} [Fintype ι]
    (π f : ι → ℝ) (P : FiniteKernel ι)
    (hπ_nonneg : ∀ x, 0 ≤ π x) :
    0 ≤ dirichletForm π P f := by
  unfold dirichletForm
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro x _
  apply Finset.sum_nonneg
  intro y _
  exact mul_nonneg
    (mul_nonneg (hπ_nonneg x) (P.nonneg x y))
    (sq_nonneg (f x - f y))

/-- Polarization of the Dirichlet form, expressed through `I-P`. -/
theorem dirichletForm_sub
    {ι : Type*} [Fintype ι]
    (π f g : ι → ℝ) (P : FiniteKernel ι)
    (hrev : P.ReversibleFor π) :
    dirichletForm π P (fun x => f x - g x) =
      dirichletForm π P f + dirichletForm π P g -
        weightedInner π f (laplacianOperator P g) -
        weightedInner π g (laplacianOperator P f) := by
  rw [dirichletForm_eq_weightedInner_laplacian π
    (fun x => f x - g x) P hrev]
  rw [laplacianOperator_sub]
  rw [weightedInner_sub_left]
  rw [weightedInner_sub_right, weightedInner_sub_right]
  rw [← dirichletForm_eq_weightedInner_laplacian π f P hrev]
  rw [← dirichletForm_eq_weightedInner_laplacian π g P hrev]
  ring

/-- The inverse quadratic form `<f,(I-P)⁻¹f>_π`, with the inverse represented
by the unique centered Poisson solution. -/
noncomputable def inverseQuadraticForm
    {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (P : FiniteKernel ι)
    (hinv : MeanZeroPoissonInvertible π P)
    (f : ι → ℝ) (hf : MeanZero π f) : ℝ :=
  weightedInner π f (poissonSolution π P hinv f hf)

/-- The finite-state algebraic asymptotic variance. The probabilistic
variance-limit interpretation is deliberately a later theorem layer. -/
noncomputable def algebraicAsymptoticVariance
    {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (P : FiniteKernel ι)
    (hinv : MeanZeroPoissonInvertible π P)
    (f : ι → ℝ) (hf : MeanZero π f) : ℝ :=
  2 * inverseQuadraticForm π P hinv f hf - weightedInner π f f

/-- The central inverse-ordering lemma: larger Dirichlet form implies smaller
inverse quadratic form on centered functions. -/
theorem inverseQuadraticForm_mono_of_peskunDominates
    {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (P₁ P₂ : FiniteKernel ι)
    (hπ_nonneg : ∀ x, 0 ≤ π x)
    (hrev₁ : P₁.ReversibleFor π)
    (hrev₂ : P₂.ReversibleFor π)
    (hdom : PeskunDominates P₁ P₂)
    (hinv₁ : MeanZeroPoissonInvertible π P₁)
    (hinv₂ : MeanZeroPoissonInvertible π P₂)
    (f : ι → ℝ) (hf : MeanZero π f) :
    inverseQuadraticForm π P₁ hinv₁ f hf ≤
      inverseQuadraticForm π P₂ hinv₂ f hf := by
  let g₁ := poissonSolution π P₁ hinv₁ f hf
  let g₂ := poissonSolution π P₂ hinv₂ f hf
  have hpoisson₁ : PoissonEquation P₁ f g₁ :=
    poissonSolution_equation π P₁ hinv₁ f hf
  have hpoisson₂ : PoissonEquation P₂ f g₂ :=
    poissonSolution_equation π P₂ hinv₂ f hf
  have hdiff_nonneg :
      0 ≤ dirichletForm π P₂ (fun x => g₂ x - g₁ x) :=
    dirichletForm_nonneg π (fun x => g₂ x - g₁ x) P₂ hπ_nonneg
  have horder :
      dirichletForm π P₂ g₁ ≤ dirichletForm π P₁ g₁ :=
    dirichletForm_mono_of_peskunDominates
      π P₁ P₂ hπ_nonneg hdom g₁
  have hE₂g₂ :
      dirichletForm π P₂ g₂ = weightedInner π f g₂ := by
    rw [dirichletForm_eq_weightedInner_laplacian π g₂ P₂ hrev₂]
    rw [hpoisson₂]
    exact weightedInner_comm π g₂ f
  have hE₁g₁ :
      dirichletForm π P₁ g₁ = weightedInner π f g₁ := by
    rw [dirichletForm_eq_weightedInner_laplacian π g₁ P₁ hrev₁]
    rw [hpoisson₁]
    exact weightedInner_comm π g₁ f
  have hcross₂₁ :
      weightedInner π g₂ (laplacianOperator P₂ g₁) =
        weightedInner π f g₁ := by
    calc
      weightedInner π g₂ (laplacianOperator P₂ g₁) =
          weightedInner π (laplacianOperator P₂ g₂) g₁ :=
        weightedInner_laplacian_selfAdjoint π g₂ g₁ P₂ hrev₂
      _ = weightedInner π f g₁ := by rw [hpoisson₂]
  have hcross₁₂ :
      weightedInner π g₁ (laplacianOperator P₂ g₂) =
        weightedInner π f g₁ := by
    rw [hpoisson₂]
    exact weightedInner_comm π g₁ f
  have hdecomposition :
      dirichletForm π P₂ (fun x => g₂ x - g₁ x) +
          (dirichletForm π P₁ g₁ - dirichletForm π P₂ g₁) =
        weightedInner π f g₂ - weightedInner π f g₁ := by
    rw [dirichletForm_sub π g₂ g₁ P₂ hrev₂]
    rw [hE₂g₂, hE₁g₁, hcross₂₁, hcross₁₂]
    ring
  have hnonneg :
      0 ≤ dirichletForm π P₂ (fun x => g₂ x - g₁ x) +
        (dirichletForm π P₁ g₁ - dirichletForm π P₂ g₁) :=
    add_nonneg hdiff_nonneg (sub_nonneg.mpr horder)
  rw [hdecomposition] at hnonneg
  unfold inverseQuadraticForm
  exact sub_nonneg.mp hnonneg

theorem algebraicAsymptoticVariance_mono_of_peskunDominates
    {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (P₁ P₂ : FiniteKernel ι)
    (hπ_nonneg : ∀ x, 0 ≤ π x)
    (hrev₁ : P₁.ReversibleFor π)
    (hrev₂ : P₂.ReversibleFor π)
    (hdom : PeskunDominates P₁ P₂)
    (hinv₁ : MeanZeroPoissonInvertible π P₁)
    (hinv₂ : MeanZeroPoissonInvertible π P₂)
    (f : ι → ℝ) (hf : MeanZero π f) :
    algebraicAsymptoticVariance π P₁ hinv₁ f hf ≤
      algebraicAsymptoticVariance π P₂ hinv₂ f hf := by
  unfold algebraicAsymptoticVariance
  have h := inverseQuadraticForm_mono_of_peskunDominates
    π P₁ P₂ hπ_nonneg hrev₁ hrev₂ hdom hinv₁ hinv₂ f hf
  linarith

end LeanMetro
