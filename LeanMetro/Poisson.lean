import LeanMetro.MeanZero

namespace LeanMetro

/-- `g` solves the Poisson equation for right-hand side `f` when
`(I - P)g = f`. -/
def PoissonEquation
    {ι : Type*} [Fintype ι]
    (P : FiniteKernel ι) (f g : ι → ℝ) : Prop :=
  laplacianOperator P g = f

/-- Every centered right-hand side has at least one centered Poisson
solution. This is the existence half of invertibility on the mean-zero
space. -/
def MeanZeroPoissonSolvable
    {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (P : FiniteKernel ι) : Prop :=
  ∀ f : ι → ℝ, MeanZero π f →
    ∃ g : ι → ℝ, MeanZero π g ∧ PoissonEquation P f g

/-- Exact interface needed for a well-defined inverse of `I-P` on centered
functions: existence and uniqueness of a centered solution. -/
structure MeanZeroPoissonInvertible
    {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (P : FiniteKernel ι) : Prop where
  exists_solution :
    ∀ f : ι → ℝ, MeanZero π f →
      ∃ g : ι → ℝ, MeanZero π g ∧ PoissonEquation P f g
  unique_solution :
    ∀ {f g h : ι → ℝ},
      MeanZero π g → MeanZero π h →
      PoissonEquation P f g → PoissonEquation P f h →
      g = h

theorem poissonEquation_rhs_meanZero
    {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (P : FiniteKernel ι)
    (hstat : P.StationaryFor π)
    {f g : ι → ℝ}
    (hpoisson : PoissonEquation P f g) :
    MeanZero π f := by
  rw [← hpoisson]
  exact laplacianOperator_meanZero π g P hstat

theorem poissonEquation_unique_on_meanZero
    {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (P : FiniteKernel ι)
    (hπ_sum : ∑ x, π x = 1)
    (hfixed : FixedPointsAreConstants P)
    {f g h : ι → ℝ}
    (hg : MeanZero π g) (hh : MeanZero π h)
    (hgf : PoissonEquation P f g)
    (hhf : PoissonEquation P f h) :
    g = h := by
  apply laplacianOperator_injective_on_meanZero π P hπ_sum hfixed hg hh
  exact hgf.trans hhf.symm

/-- Existence plus the fixed-point condition upgrades to a genuine inverse on
the centered subspace. -/
theorem meanZeroPoissonInvertible_of_solvable_of_fixedPoints
    {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (P : FiniteKernel ι)
    (hπ_sum : ∑ x, π x = 1)
    (hfixed : FixedPointsAreConstants P)
    (hsolvable : MeanZeroPoissonSolvable π P) :
    MeanZeroPoissonInvertible π P where
  exists_solution := hsolvable
  unique_solution := by
    intro f g h hg hh hgf hhf
    exact poissonEquation_unique_on_meanZero
      π P hπ_sum hfixed hg hh hgf hhf

/-- The canonical centered Poisson solution selected from the invertibility
interface. -/
noncomputable def poissonSolution
    {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (P : FiniteKernel ι)
    (hinv : MeanZeroPoissonInvertible π P)
    (f : ι → ℝ) (hf : MeanZero π f) : ι → ℝ :=
  Classical.choose (hinv.exists_solution f hf)

theorem poissonSolution_meanZero
    {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (P : FiniteKernel ι)
    (hinv : MeanZeroPoissonInvertible π P)
    (f : ι → ℝ) (hf : MeanZero π f) :
    MeanZero π (poissonSolution π P hinv f hf) :=
  (Classical.choose_spec (hinv.exists_solution f hf)).1

theorem poissonSolution_equation
    {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (P : FiniteKernel ι)
    (hinv : MeanZeroPoissonInvertible π P)
    (f : ι → ℝ) (hf : MeanZero π f) :
    PoissonEquation P f (poissonSolution π P hinv f hf) :=
  (Classical.choose_spec (hinv.exists_solution f hf)).2

theorem poissonSolution_eq_of_meanZero_solution
    {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (P : FiniteKernel ι)
    (hinv : MeanZeroPoissonInvertible π P)
    (f : ι → ℝ) (hf : MeanZero π f)
    (g : ι → ℝ) (hg : MeanZero π g)
    (hgf : PoissonEquation P f g) :
    poissonSolution π P hinv f hf = g := by
  exact hinv.unique_solution
    (poissonSolution_meanZero π P hinv f hf) hg
    (poissonSolution_equation π P hinv f hf) hgf

end LeanMetro
