import LeanMetro.VarianceLimit

namespace LeanMetro

open Filter
open scoped Topology

/-- A finite Markov operator preserves every uniform absolute bound. -/
theorem abs_markovOperator_le_of_forall_abs_le
    {ι : Type*} [Fintype ι]
    (P : FiniteKernel ι) (f : ι → ℝ) (C : ℝ)
    (hf : ∀ y, |f y| ≤ C) (x : ι) :
    |markovOperator P f x| ≤ C := by
  calc
    |markovOperator P f x| = |∑ y, P.prob x y * f y| := by
      rfl
    _ ≤ ∑ y, |P.prob x y * f y| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ y, P.prob x y * |f y| := by
      apply Finset.sum_congr rfl
      intro y _
      rw [abs_mul, abs_of_nonneg (P.nonneg x y)]
    _ ≤ ∑ y, P.prob x y * C := by
      apply Finset.sum_le_sum
      intro y _
      exact mul_le_mul_of_nonneg_left (hf y) (P.nonneg x y)
    _ = C := by
      rw [← Finset.sum_mul, P.row_sum x, one_mul]

/-- Every iterate of a finite Markov operator is bounded by the sum of the
absolute values of the starting function. This deliberately uses a simple
finite bound rather than introducing a separate sup-norm API. -/
theorem abs_markovIterate_le_sum_abs
    {ι : Type*} [Fintype ι]
    (P : FiniteKernel ι) (g : ι → ℝ) (n : ℕ) (x : ι) :
    |markovIterate P n g x| ≤ ∑ y, |g y| := by
  classical
  let C : ℝ := ∑ y, |g y|
  have hg : ∀ y, |g y| ≤ C := by
    intro y
    exact Finset.single_le_sum (fun z _ => abs_nonneg (g z))
      (Finset.mem_univ y)
  induction n generalizing x with
  | zero =>
      simpa [C] using hg x
  | succ n ih =>
      rw [markovIterate_succ]
      exact abs_markovOperator_le_of_forall_abs_le
        P (markovIterate P n g) C (fun y => ih y) x

/-- The quadratic expressions `<g,P^n g>_π` are uniformly bounded. No sign
or normalization assumption on `π` is needed for this purely finite bound. -/
theorem abs_weightedInner_markovIterate_le
    {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (P : FiniteKernel ι) (g : ι → ℝ) (n : ℕ) :
    |weightedInner π g (markovIterate P n g)| ≤
      (∑ x, |π x * g x|) * (∑ y, |g y|) := by
  classical
  let C : ℝ := ∑ y, |g y|
  calc
    |weightedInner π g (markovIterate P n g)| =
        |∑ x, π x * g x * markovIterate P n g x| := by
      rfl
    _ ≤ ∑ x, |π x * g x * markovIterate P n g x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, |π x * g x| * |markovIterate P n g x| := by
      apply Finset.sum_congr rfl
      intro x _
      rw [abs_mul]
    _ ≤ ∑ x, |π x * g x| * C := by
      apply Finset.sum_le_sum
      intro x _
      exact mul_le_mul_of_nonneg_left
        (by simpa [C] using abs_markovIterate_le_sum_abs P g n x)
        (abs_nonneg (π x * g x))
    _ = (∑ x, |π x * g x|) * (∑ y, |g y|) := by
      rw [Finset.sum_mul]

/-- For a reversible kernel, pairing the Poisson right-hand side with an
iterate is a discrete derivative of `<g,P^n g>_π`. -/
theorem weightedInner_markovIterate_eq_quadratic_sub_succ
    {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (P : FiniteKernel ι)
    {f g : ι → ℝ}
    (hrev : P.ReversibleFor π)
    (hpoisson : PoissonEquation P f g) (n : ℕ) :
    weightedInner π f (markovIterate P n g) =
      weightedInner π g (markovIterate P n g) -
        weightedInner π g (markovIterate P (n + 1) g) := by
  calc
    weightedInner π f (markovIterate P n g) =
        weightedInner π (laplacianOperator P g)
          (markovIterate P n g) := by rw [hpoisson]
    _ = weightedInner π g (markovIterate P n g) -
        weightedInner π (markovOperator P g)
          (markovIterate P n g) := by
      unfold laplacianOperator
      rw [weightedInner_sub_left]
    _ = weightedInner π g (markovIterate P n g) -
        weightedInner π g
          (markovOperator P (markovIterate P n g)) := by
      rw [weightedInner_markovOperator_selfAdjoint P π g
        (markovIterate P n g) hrev]
    _ = weightedInner π g (markovIterate P n g) -
        weightedInner π g (markovIterate P (n + 1) g) := by
      rfl

/-- The entire Cesàro remainder telescopes to two endpoint quadratic terms. -/
theorem sum_weightedInner_markovIterate_eq_endpoints
    {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (P : FiniteKernel ι)
    {f g : ι → ℝ}
    (hrev : P.ReversibleFor π)
    (hpoisson : PoissonEquation P f g) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
        weightedInner π f (markovIterate P (k + 1) g)) =
      weightedInner π g (markovIterate P 1 g) -
        weightedInner π g (markovIterate P (n + 2) g) := by
  let d : ℕ → ℝ := fun k => weightedInner π g (markovIterate P k g)
  calc
    (∑ k ∈ Finset.range (n + 1),
        weightedInner π f (markovIterate P (k + 1) g)) =
        ∑ k ∈ Finset.range (n + 1), (d (k + 1) - d (k + 2)) := by
      apply Finset.sum_congr rfl
      intro k _
      simpa [d] using weightedInner_markovIterate_eq_quadratic_sub_succ
        π P hrev hpoisson (k + 1)
    _ = d 1 - d ((n + 1) + 1) := sum_shifted_sub d (n + 1)
    _ = weightedInner π g (markovIterate P 1 g) -
        weightedInner π g (markovIterate P (n + 2) g) := by
      simp only [d]

/-- Reversibility makes the exact Poisson remainder telescope. Since finite
Markov iterates are uniformly bounded, division by the horizon sends this
two-endpoint remainder to zero. Pointwise covariance decay, aperiodicity, and
spectral assumptions are unnecessary for this variance limit. -/
theorem stationaryScaledVariance_tendsto_algebraicAsymptoticVariance_of_reversible
    {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (P : FiniteKernel ι)
    (hrev : P.ReversibleFor π)
    (hinv : MeanZeroPoissonInvertible π P)
    (f : ι → ℝ) (hf : MeanZero π f) :
    Tendsto (stationaryScaledVariance π P f) atTop
      (𝓝 (algebraicAsymptoticVariance π P hinv f hf)) := by
  let g := poissonSolution π P hinv f hf
  let d : ℕ → ℝ := fun n => weightedInner π g (markovIterate P n g)
  let B : ℝ := (∑ x, |π x * g x|) * (∑ y, |g y|)
  have hB_nonneg : 0 ≤ B := mul_nonneg
    (Finset.sum_nonneg fun x _ => abs_nonneg (π x * g x))
    (Finset.sum_nonneg fun y _ => abs_nonneg (g y))
  have hd_bound : ∀ n, |d n| ≤ B := by
    intro n
    simpa [d, B] using abs_weightedInner_markovIterate_le π P g n
  have hpoisson : PoissonEquation P f g :=
    poissonSolution_equation π P hinv f hf
  have hsum : ∀ n,
      (∑ k ∈ Finset.range (n + 1),
          weightedInner π f (markovIterate P (k + 1) g)) =
        d 1 - d (n + 2) := by
    intro n
    simpa [d] using sum_weightedInner_markovIterate_eq_endpoints
      π P hrev hpoisson n
  have hnum_bound : ∀ n, |2 * (d 1 - d (n + 2))| ≤ 4 * B := by
    intro n
    calc
      |2 * (d 1 - d (n + 2))| = 2 * |d 1 - d (n + 2)| := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ 2 * (|d 1| + |d (n + 2)|) := by
        gcongr
        exact abs_sub (d 1) (d (n + 2))
      _ ≤ 2 * (B + B) := by
        gcongr
        · exact hd_bound 1
        · exact hd_bound (n + 2)
      _ = 4 * B := by ring
  have hinv_tendsto : Tendsto
      (fun n : ℕ => (((n + 1 : ℕ) : ℝ)⁻¹)) atTop (𝓝 0) := by
    exact tendsto_inv_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)
  have hremainder : Tendsto
      (fun n => 2 * (((n + 1 : ℕ) : ℝ)⁻¹) *
        ∑ k ∈ Finset.range (n + 1),
          weightedInner π f (markovIterate P (k + 1) g))
      atTop (𝓝 0) := by
    have hproduct := bdd_le_mul_tendsto_zero' (4 * B)
      (Eventually.of_forall hnum_bound) hinv_tendsto
    convert hproduct using 1
    funext n
    rw [hsum n]
    ring
  rw [show stationaryScaledVariance π P f =
      fun n => algebraicAsymptoticVariance π P hinv f hf -
        2 * (((n + 1 : ℕ) : ℝ)⁻¹) *
          ∑ k ∈ Finset.range (n + 1),
            weightedInner π f (markovIterate P (k + 1) g) by
    funext n
    simpa [g] using
      stationaryScaledVariance_eq_algebraic_sub_remainder
        π P hinv f hf n]
  convert tendsto_const_nhds.sub hremainder using 1
  all_goals norm_num

end LeanMetro
