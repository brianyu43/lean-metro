import LeanMetro.VarianceLimit
import Mathlib.Probability.ProbabilityMassFunction.Integrals

namespace LeanMetro

open MeasureTheory

universe u

/-- A path of `n + 1` states, stored with the most recent state first. -/
inductive ChainPath (ι : Type u) : ℕ → Type u
  | start : ι → ChainPath ι 0
  | step {n : ℕ} : ι → ChainPath ι n → ChainPath ι (n + 1)

def chainPathZeroEquiv {ι : Type*} : ι ≃ ChainPath ι 0 where
  toFun := ChainPath.start
  invFun := fun p => by cases p with | start x => exact x
  left_inv := by intro x; rfl
  right_inv := by intro p; cases p; rfl

def chainPathSuccEquiv {ι : Type*} {n : ℕ} :
    (ι × ChainPath ι n) ≃ ChainPath ι (n + 1) where
  toFun := fun p => ChainPath.step p.1 p.2
  invFun := fun p => by cases p with | step x q => exact (x, q)
  left_inv := by intro p; cases p; rfl
  right_inv := by intro p; cases p; rfl

@[instance_reducible] noncomputable def chainPathFintype
    {ι : Type*} [Fintype ι] : (n : ℕ) → Fintype (ChainPath ι n)
  | 0 => Fintype.ofEquiv ι chainPathZeroEquiv
  | n + 1 =>
      letI : Fintype (ChainPath ι n) := chainPathFintype n
      Fintype.ofEquiv (ι × ChainPath ι n) chainPathSuccEquiv

noncomputable instance
    {ι : Type*} [Fintype ι] (n : ℕ) : Fintype (ChainPath ι n) :=
  chainPathFintype n

instance {ι : Type*} {n : ℕ} : MeasurableSpace (ChainPath ι n) := ⊤

theorem chainPath_sum_zero
    {ι M : Type*} [Fintype ι] [AddCommMonoid M]
    (F : ChainPath ι 0 → M) :
    (∑ p, F p) = ∑ x, F (.start x) := by
  exact (chainPathZeroEquiv.sum_comp F).symm

theorem chainPath_sum_succ
    {ι M : Type*} [Fintype ι] [AddCommMonoid M]
    {n : ℕ} (F : ChainPath ι (n + 1) → M) :
    (∑ p, F p) = ∑ q : ChainPath ι n, ∑ y : ι, F (.step y q) := by
  rw [← (chainPathSuccEquiv.sum_comp F)]
  exact Fintype.sum_prod_type_right _

/-- Most recent state of a finite path. -/
def chainPathCurrent
    {ι : Type*} : {n : ℕ} → ChainPath ι n → ι
  | 0, .start x => x
  | _ + 1, .step x _ => x

/-- Sum of an observable along all states in a finite path. -/
def chainPathSum
    {ι : Type*} (f : ι → ℝ) : {n : ℕ} → ChainPath ι n → ℝ
  | 0, .start x => f x
  | _ + 1, .step x p => chainPathSum f p + f x

/-- Probability mass of a path: initial mass times all transition
probabilities. -/
noncomputable def chainPathMass
    {ι : Type*} [Fintype ι] (π : ι → ℝ) (P : FiniteKernel ι) :
    {n : ℕ} → ChainPath ι n → ℝ
  | 0, .start x => π x
  | _ + 1, .step y p =>
      chainPathMass π P p * P.prob (chainPathCurrent p) y

theorem chainPathMass_nonneg
    {ι : Type*} [Fintype ι] (π : ι → ℝ) (P : FiniteKernel ι)
    (hπ_nonneg : ∀ x, 0 ≤ π x) :
    ∀ {n : ℕ} (p : ChainPath ι n), 0 ≤ chainPathMass π P p := by
  intro n p
  induction p with
  | start x => exact hπ_nonneg x
  | step y p ih => exact mul_nonneg ih (P.nonneg _ _)

theorem chainPathMass_sum_one
    {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (P : FiniteKernel ι)
    (hπ_sum : ∑ x, π x = 1) :
    ∀ n : ℕ, ∑ p : ChainPath ι n, chainPathMass π P p = 1 := by
  intro n
  induction n with
  | zero =>
      rw [chainPath_sum_zero]
      simpa [chainPathMass] using hπ_sum
  | succ n ih =>
      rw [chainPath_sum_succ]
      calc
        (∑ q : ChainPath ι n, ∑ y : ι,
            chainPathMass π P (.step y q)) =
            ∑ q : ChainPath ι n,
              chainPathMass π P q * ∑ y : ι, P.prob (chainPathCurrent q) y := by
          apply Finset.sum_congr rfl
          intro q _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y _
          rfl
        _ = ∑ q : ChainPath ι n, chainPathMass π P q := by
          apply Finset.sum_congr rfl
          intro q _
          rw [P.row_sum, mul_one]
        _ = 1 := ih

/-- The actual PMF of a stationary-initialized finite Markov path. -/
noncomputable def stationaryPathPMF
    {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (P : FiniteKernel ι)
    (hπ_nonneg : ∀ x, 0 ≤ π x)
    (hπ_sum : ∑ x, π x = 1)
    (n : ℕ) : PMF (ChainPath ι n) :=
  PMF.ofFintype
    (fun p => ENNReal.ofReal (chainPathMass π P p))
    (by
      rw [← ENNReal.ofReal_sum_of_nonneg]
      · rw [chainPathMass_sum_one π P hπ_sum n]
        norm_num
      · intro p _
        exact chainPathMass_nonneg π P hπ_nonneg p)

@[simp]
theorem stationaryPathPMF_apply_toReal
    {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (P : FiniteKernel ι)
    (hπ_nonneg : ∀ x, 0 ≤ π x)
    (hπ_sum : ∑ x, π x = 1)
    (n : ℕ) (p : ChainPath ι n) :
    (stationaryPathPMF π P hπ_nonneg hπ_sum n p).toReal =
      chainPathMass π P p := by
  simp [stationaryPathPMF, chainPathMass_nonneg π P hπ_nonneg p]

/-- Probability measure associated with the finite-horizon path PMF. -/
noncomputable def stationaryPathMeasure
    {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (P : FiniteKernel ι)
    (hπ_nonneg : ∀ x, 0 ≤ π x)
    (hπ_sum : ∑ x, π x = 1)
    (n : ℕ) : Measure (ChainPath ι n) :=
  (stationaryPathPMF π P hπ_nonneg hπ_sum n).toMeasure

noncomputable instance stationaryPathMeasure_isProbabilityMeasure
    {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (P : FiniteKernel ι)
    (hπ_nonneg : ∀ x, 0 ≤ π x)
    (hπ_sum : ∑ x, π x = 1)
    (n : ℕ) :
    IsProbabilityMeasure
      (stationaryPathMeasure π P hπ_nonneg hπ_sum n) := by
  unfold stationaryPathMeasure
  infer_instance

theorem stationaryPath_integral_eq_sum
    {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (P : FiniteKernel ι)
    (hπ_nonneg : ∀ x, 0 ≤ π x)
    (hπ_sum : ∑ x, π x = 1)
    (n : ℕ) (F : ChainPath ι n → ℝ) :
    ∫ p, F p ∂(stationaryPathMeasure π P hπ_nonneg hπ_sum n) =
      ∑ p, chainPathMass π P p * F p := by
  unfold stationaryPathMeasure
  rw [PMF.integral_eq_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [stationaryPathPMF_apply_toReal]
  simp [smul_eq_mul]

end LeanMetro
