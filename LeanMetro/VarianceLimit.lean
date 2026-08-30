import LeanMetro.Peskun
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

namespace LeanMetro

open Filter
open scoped Topology

/-- Repeated application of a finite Markov operator. -/
noncomputable def markovIterate
    {ι : Type*} [Fintype ι]
    (P : FiniteKernel ι) : ℕ → (ι → ℝ) → (ι → ℝ)
  | 0, f => f
  | n + 1, f => markovOperator P (markovIterate P n f)

@[simp]
theorem markovIterate_zero
    {ι : Type*} [Fintype ι]
    (P : FiniteKernel ι) (f : ι → ℝ) :
    markovIterate P 0 f = f := by
  rfl

@[simp]
theorem markovIterate_succ
    {ι : Type*} [Fintype ι]
    (P : FiniteKernel ι) (n : ℕ) (f : ι → ℝ) :
    markovIterate P (n + 1) f =
      markovOperator P (markovIterate P n f) := by
  rfl

theorem markovIterate_poisson
    {ι : Type*} [Fintype ι]
    (P : FiniteKernel ι) {f g : ι → ℝ}
    (hpoisson : PoissonEquation P f g) (n : ℕ) :
    markovIterate P n f =
      fun x => markovIterate P n g x - markovIterate P (n + 1) g x := by
  induction n with
  | zero =>
      funext x
      have hpoint := congrFun hpoisson x
      simpa [PoissonEquation, laplacianOperator] using hpoint.symm
  | succ n ih =>
      rw [markovIterate_succ, ih]
      funext x
      rw [markovOperator_sub]
      rfl

/-- The lag-`n` covariance expression of a centered observable in a stationary
finite chain. -/
noncomputable def lagCovariance
    {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (P : FiniteKernel ι) (f : ι → ℝ) (n : ℕ) : ℝ :=
  weightedInner π f (markovIterate P n f)

/-- The standard covariance formula for `N * Var(sample mean)`, indexed by
`N = n + 1` so division by zero never occurs. -/
noncomputable def stationaryScaledVariance
    {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (P : FiniteKernel ι) (f : ι → ℝ) (n : ℕ) : ℝ :=
  weightedInner π f f +
    2 * (((n + 1 : ℕ) : ℝ)⁻¹) *
      ∑ k ∈ Finset.range n,
        ((n : ℝ) - (k : ℝ)) * lagCovariance π P f (k + 1)

theorem sum_shifted_sub
    (d : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n, (d (k + 1) - d (k + 2))) =
      d 1 - d (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring

theorem weighted_sum_shifted_sub
    (d : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n,
        ((n : ℝ) - (k : ℝ)) * (d (k + 1) - d (k + 2))) =
      (n : ℝ) * d 1 - ∑ k ∈ Finset.range n, d (k + 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hsplit :
          (∑ k ∈ Finset.range n,
              (((n + 1 : ℕ) : ℝ) - (k : ℝ)) *
                (d (k + 1) - d (k + 2))) =
            (∑ k ∈ Finset.range n,
              ((n : ℝ) - (k : ℝ)) *
                (d (k + 1) - d (k + 2))) +
              ∑ k ∈ Finset.range n, (d (k + 1) - d (k + 2)) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        norm_num [Nat.cast_add, Nat.cast_one]
        ring
      rw [hsplit, ih, sum_shifted_sub]
      rw [Finset.sum_range_succ]
      norm_num [Nat.cast_add, Nat.cast_one]
      ring

theorem lagCovariance_eq_poisson_difference
    {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (P : FiniteKernel ι)
    {f g : ι → ℝ} (hpoisson : PoissonEquation P f g)
    (n : ℕ) :
    lagCovariance π P f n =
      weightedInner π f (markovIterate P n g) -
        weightedInner π f (markovIterate P (n + 1) g) := by
  unfold lagCovariance
  rw [markovIterate_poisson P hpoisson n]
  rw [weightedInner_sub_right]

/-- Exact finite-time bridge from the covariance expression to the Poisson
formula, with a Cesàro remainder. -/
theorem stationaryScaledVariance_eq_algebraic_sub_remainder
    {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (P : FiniteKernel ι)
    (hinv : MeanZeroPoissonInvertible π P)
    (f : ι → ℝ) (hf : MeanZero π f) (n : ℕ) :
    stationaryScaledVariance π P f n =
      algebraicAsymptoticVariance π P hinv f hf -
        2 * (((n + 1 : ℕ) : ℝ)⁻¹) *
          ∑ k ∈ Finset.range (n + 1),
            weightedInner π f
              (markovIterate P (k + 1)
                (poissonSolution π P hinv f hf)) := by
  let g := poissonSolution π P hinv f hf
  let d : ℕ → ℝ := fun k => weightedInner π f (markovIterate P k g)
  have hpoisson : PoissonEquation P f g :=
    poissonSolution_equation π P hinv f hf
  have hcov : ∀ k, lagCovariance π P f k = d k - d (k + 1) := by
    intro k
    simpa [d] using lagCovariance_eq_poisson_difference
      π P hpoisson k
  have hff : weightedInner π f f = d 0 - d 1 := by
    calc
      weightedInner π f f = lagCovariance π P f 0 := by
        simp [lagCovariance]
      _ = d 0 - d 1 := hcov 0
  have hweighted :
      (∑ k ∈ Finset.range n,
          ((n : ℝ) - (k : ℝ)) * lagCovariance π P f (k + 1)) =
        (n : ℝ) * d 1 - ∑ k ∈ Finset.range n, d (k + 2) := by
    calc
      (∑ k ∈ Finset.range n,
          ((n : ℝ) - (k : ℝ)) * lagCovariance π P f (k + 1)) =
          ∑ k ∈ Finset.range n,
            ((n : ℝ) - (k : ℝ)) * (d (k + 1) - d (k + 2)) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [hcov (k + 1)]
      _ = (n : ℝ) * d 1 - ∑ k ∈ Finset.range n, d (k + 2) :=
        weighted_sum_shifted_sub d n
  unfold stationaryScaledVariance algebraicAsymptoticVariance
    inverseQuadraticForm
  change weightedInner π f f +
      2 * (((n + 1 : ℕ) : ℝ)⁻¹) *
        (∑ k ∈ Finset.range n,
          ((n : ℝ) - (k : ℝ)) * lagCovariance π P f (k + 1)) =
    2 * d 0 - weightedInner π f f -
      2 * (((n + 1 : ℕ) : ℝ)⁻¹) *
        ∑ k ∈ Finset.range (n + 1), d (k + 1)
  rw [hff, hweighted, Finset.sum_range_succ']
  norm_num [Nat.cast_add, Nat.cast_one]
  field_simp
  ring

/-- If the Poisson remainder covariance tends to zero, the stationary
finite-time covariance formula converges to the algebraic asymptotic
variance. -/
theorem stationaryScaledVariance_tendsto_algebraicAsymptoticVariance
    {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (P : FiniteKernel ι)
    (hinv : MeanZeroPoissonInvertible π P)
    (f : ι → ℝ) (hf : MeanZero π f)
    (hdecay : Tendsto
      (fun n => weightedInner π f
        (markovIterate P n (poissonSolution π P hinv f hf)))
      atTop (𝓝 0)) :
    Tendsto (stationaryScaledVariance π P f) atTop
      (𝓝 (algebraicAsymptoticVariance π P hinv f hf)) := by
  let d : ℕ → ℝ := fun n => weightedInner π f
    (markovIterate P n (poissonSolution π P hinv f hf))
  have hshift : Tendsto (fun n => d (n + 1)) atTop (𝓝 0) := by
    exact hdecay.comp (tendsto_add_atTop_nat 1)
  have hcesaro := hshift.cesaro
  have hcesaro_shift := hcesaro.comp (tendsto_add_atTop_nat 1)
  have htwo : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2) :=
    tendsto_const_nhds
  have hscaled : Tendsto
      (fun n => 2 * (((n + 1 : ℕ) : ℝ)⁻¹) *
        ∑ k ∈ Finset.range (n + 1), d (k + 1))
      atTop (𝓝 0) := by
    convert htwo.mul hcesaro_shift using 1 <;>
      norm_num [Function.comp_def, d, mul_assoc]
  rw [show stationaryScaledVariance π P f =
      fun n => algebraicAsymptoticVariance π P hinv f hf -
        2 * (((n + 1 : ℕ) : ℝ)⁻¹) *
          ∑ k ∈ Finset.range (n + 1), d (k + 1) by
    funext n
    simpa [d] using
      stationaryScaledVariance_eq_algebraic_sub_remainder
        π P hinv f hf n]
  convert tendsto_const_nhds.sub hscaled using 1
  all_goals norm_num

end LeanMetro
