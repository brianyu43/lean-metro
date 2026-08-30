import LeanMetro.Poisson
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs

namespace LeanMetro

namespace FiniteKernel

variable {ι : Type*} [Fintype ι]

/-- A finite kernel is irreducible when its nonnegative transition matrix is
irreducible in mathlib's standard sense: the quiver of strictly positive
entries is strongly connected. -/
def Irreducible (P : FiniteKernel ι) : Prop :=
  Matrix.IsIrreducible P.prob

/-- The standard algebraic characterization: every ordered pair of states
has a strictly positive entry in some positive power of the transition
matrix. -/
theorem irreducible_iff_exists_pow_pos
    [DecidableEq ι] (P : FiniteKernel ι) :
    let A : Matrix ι ι ℝ := P.prob
    P.Irreducible ↔
      ∀ x y, ∃ n > 0, 0 < (A ^ n) x y := by
  exact Matrix.isIrreducible_iff_exists_pow_pos P.nonneg

end FiniteKernel

/-- The centered functions form a genuine finite-dimensional linear
subspace. This bundle is the adapter needed to apply finite-dimensional
injective-implies-surjective reasoning to `I - P`. -/
def meanZeroSubmodule
    {ι : Type*} [Fintype ι]
    (π : ι → ℝ) : Submodule ℝ (ι → ℝ) where
  carrier := {f | MeanZero π f}
  zero_mem' := MeanZero.zero π
  add_mem' := fun hf hg => hf.add hg
  smul_mem' := by
    intro c f hf
    change MeanZero π (fun x => c * f x)
    exact hf.smul c

/-- The discrete Laplacian as a linear endomorphism of all real-valued
functions on the finite state space. -/
noncomputable def laplacianLinearMap
    {ι : Type*} [Fintype ι]
    (P : FiniteKernel ι) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun := laplacianOperator P
  map_add' := by
    intro f g
    funext x
    change (f x + g x) -
        markovOperator P (fun y => f y + g y) x =
      (f x - markovOperator P f x) +
        (g x - markovOperator P g x)
    rw [markovOperator_add]
    ring
  map_smul' := by
    intro c f
    funext x
    change c * f x - markovOperator P (fun y => c * f y) x =
      c * (f x - markovOperator P f x)
    rw [markovOperator_smul]
    ring

/-- Stationarity makes `I - P` preserve the centered subspace. -/
noncomputable def meanZeroLaplacianLinearMap
    {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (P : FiniteKernel ι)
    (hstat : P.StationaryFor π) :
    meanZeroSubmodule π →ₗ[ℝ] meanZeroSubmodule π where
  toFun := fun f =>
    ⟨laplacianOperator P f, laplacianOperator_meanZero π f P hstat⟩
  map_add' := by
    intro f g
    apply Subtype.ext
    exact (laplacianLinearMap P).map_add f g
  map_smul' := by
    intro c f
    apply Subtype.ext
    exact (laplacianLinearMap P).map_smul c f

/-- A fixed harmonic function cannot drop across a transition of positive
probability when its value at the source is globally maximal. -/
private theorem fixed_eq_of_positive_transition
    {ι : Type*} [Fintype ι]
    (P : FiniteKernel ι) (f : ι → ℝ)
    (hfixed : ∀ x, markovOperator P f x = f x)
    {x y : ι} (hmax : ∀ z, f z ≤ f x)
    (hxy : 0 < P.prob x y) :
    f y = f x := by
  have hnonneg :
      ∀ z ∈ Finset.univ, 0 ≤ P.prob x z * (f x - f z) := by
    intro z _
    exact mul_nonneg (P.nonneg x z) (sub_nonneg.mpr (hmax z))
  have hsum_zero :
      ∑ z, P.prob x z * (f x - f z) = 0 := by
    calc
      ∑ z, P.prob x z * (f x - f z) =
          f x * (∑ z, P.prob x z) -
            ∑ z, P.prob x z * f z := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro z _
        ring
      _ = f x - markovOperator P f x := by
        rw [P.row_sum x, mul_one]
        rfl
      _ = 0 := by rw [hfixed x, sub_self]
  have hterm_zero : P.prob x y * (f x - f y) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum_zero
      y (Finset.mem_univ y)
  rcases mul_eq_zero.mp hterm_zero with hprob | hgap
  · exact (hxy.ne' hprob).elim
  · exact (sub_eq_zero.mp hgap).symm

/-- Finite irreducibility implies the maximum principle: the only fixed
functions of the Markov operator are constants. -/
theorem fixedPointsAreConstants_of_irreducible
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (P : FiniteKernel ι) (hirr : P.Irreducible) :
    FixedPointsAreConstants P := by
  intro f hfixed
  obtain ⟨x₀, _, hx₀⟩ :=
    Finset.exists_max_image (Finset.univ : Finset ι) f Finset.univ_nonempty
  refine ⟨f x₀, ?_⟩
  intro y
  have hpropagate :
      ∀ {u v : ι}, f u = f x₀ → 0 < P.prob u v → f v = f x₀ := by
    intro u v hu huv
    have humax : ∀ z, f z ≤ f u := by
      intro z
      rw [hu]
      exact hx₀ z (Finset.mem_univ z)
    exact (fixed_eq_of_positive_transition P f hfixed humax huv).trans hu
  let : Quiver ι := Matrix.toQuiver P.prob
  obtain ⟨p, hp⟩ := hirr.connected x₀ y
  clear hp
  induction p with
  | nil => rfl
  | cons _ e ih => exact hpropagate ih e.down

/-- On the finite-dimensional centered subspace, fixed-point uniqueness makes
`I - P` injective and hence surjective. Therefore every centered right-hand
side has a centered Poisson solution. -/
theorem meanZeroPoissonSolvable_of_fixedPoints
    {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (P : FiniteKernel ι)
    (hπ_sum : ∑ x, π x = 1)
    (hstat : P.StationaryFor π)
    (hfixed : FixedPointsAreConstants P) :
    MeanZeroPoissonSolvable π P := by
  let L := meanZeroLaplacianLinearMap π P hstat
  have hL_injective : Function.Injective L := by
    intro f g hfg
    apply Subtype.ext
    apply laplacianOperator_injective_on_meanZero
      π P hπ_sum hfixed f.property g.property
    exact congrArg Subtype.val hfg
  have hL_surjective : Function.Surjective L :=
    LinearMap.surjective_of_injective hL_injective
  intro f hf
  obtain ⟨g, hg⟩ := hL_surjective ⟨f, hf⟩
  refine ⟨g, g.property, ?_⟩
  exact congrArg Subtype.val hg

/-- Fixed-point uniqueness, stationarity, and normalization automatically
produce the full centered Poisson inverse on a finite state space. -/
theorem meanZeroPoissonInvertible_of_fixedPoints
    {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (P : FiniteKernel ι)
    (hπ_sum : ∑ x, π x = 1)
    (hstat : P.StationaryFor π)
    (hfixed : FixedPointsAreConstants P) :
    MeanZeroPoissonInvertible π P :=
  meanZeroPoissonInvertible_of_solvable_of_fixedPoints
    π P hπ_sum hfixed
      (meanZeroPoissonSolvable_of_fixedPoints
        π P hπ_sum hstat hfixed)

/-- Main irreducibility adapter: for a finite irreducible stationary chain,
the Poisson operator is automatically invertible on centered functions. -/
theorem meanZeroPoissonInvertible_of_irreducible
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (π : ι → ℝ) (P : FiniteKernel ι)
    (hπ_sum : ∑ x, π x = 1)
    (hstat : P.StationaryFor π)
    (hirr : P.Irreducible) :
    MeanZeroPoissonInvertible π P :=
  meanZeroPoissonInvertible_of_fixedPoints
    π P hπ_sum hstat (fixedPointsAreConstants_of_irreducible P hirr)

end LeanMetro
