import LeanMetro.FinitePath

namespace LeanMetro

open MeasureTheory

/-- Expectation on the actual finite-horizon path probability measure. -/
noncomputable def stationaryPathExpectation
    {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (P : FiniteKernel ι)
    (hπ_nonneg : ∀ x, 0 ≤ π x)
    (hπ_sum : ∑ x, π x = 1)
    (n : ℕ) (F : ChainPath ι n → ℝ) : ℝ :=
  ∫ p, F p ∂(stationaryPathMeasure π P hπ_nonneg hπ_sum n)

theorem stationaryPathExpectation_eq_sum
    {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (P : FiniteKernel ι)
    (hπ_nonneg : ∀ x, 0 ≤ π x)
    (hπ_sum : ∑ x, π x = 1)
    (n : ℕ) (F : ChainPath ι n → ℝ) :
    stationaryPathExpectation π P hπ_nonneg hπ_sum n F =
      ∑ p, chainPathMass π P p * F p := by
  exact stationaryPath_integral_eq_sum
    π P hπ_nonneg hπ_sum n F

theorem stationaryPathExpectation_add
    {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (P : FiniteKernel ι)
    (hπ_nonneg : ∀ x, 0 ≤ π x)
    (hπ_sum : ∑ x, π x = 1)
    (n : ℕ) (F G : ChainPath ι n → ℝ) :
    stationaryPathExpectation π P hπ_nonneg hπ_sum n
        (fun p => F p + G p) =
      stationaryPathExpectation π P hπ_nonneg hπ_sum n F +
        stationaryPathExpectation π P hπ_nonneg hπ_sum n G := by
  simp_rw [stationaryPathExpectation_eq_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  ring

theorem stationaryPathExpectation_smul
    {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (P : FiniteKernel ι)
    (hπ_nonneg : ∀ x, 0 ≤ π x)
    (hπ_sum : ∑ x, π x = 1)
    (n : ℕ) (c : ℝ) (F : ChainPath ι n → ℝ) :
    stationaryPathExpectation π P hπ_nonneg hπ_sum n
        (fun p => c * F p) =
      c * stationaryPathExpectation π P hπ_nonneg hπ_sum n F := by
  simp_rw [stationaryPathExpectation_eq_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  ring

/-- One-step disintegration of finite-path expectation. -/
theorem stationaryPathExpectation_succ
    {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (P : FiniteKernel ι)
    (hπ_nonneg : ∀ x, 0 ≤ π x)
    (hπ_sum : ∑ x, π x = 1)
    (n : ℕ) (F : ChainPath ι (n + 1) → ℝ) :
    stationaryPathExpectation π P hπ_nonneg hπ_sum (n + 1) F =
      stationaryPathExpectation π P hπ_nonneg hπ_sum n
        (fun p => ∑ y, P.prob (chainPathCurrent p) y * F (.step y p)) := by
  rw [stationaryPathExpectation_eq_sum]
  rw [chainPath_sum_succ]
  rw [stationaryPathExpectation_eq_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  simp [chainPathMass]
  ring

/-- Stationarity says the most recent state has distribution `π` at every
horizon. -/
theorem stationaryPath_current_expectation
    {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (P : FiniteKernel ι)
    (hπ_nonneg : ∀ x, 0 ≤ π x)
    (hπ_sum : ∑ x, π x = 1)
    (hstat : P.StationaryFor π)
    (n : ℕ) (h : ι → ℝ) :
    stationaryPathExpectation π P hπ_nonneg hπ_sum n
        (fun p => h (chainPathCurrent p)) =
      weightedMean π h := by
  induction n generalizing h with
  | zero =>
      rw [stationaryPathExpectation_eq_sum, chainPath_sum_zero]
      rfl
  | succ n ih =>
      rw [stationaryPathExpectation_succ]
      change stationaryPathExpectation π P hπ_nonneg hπ_sum n
          (fun p => markovOperator P h (chainPathCurrent p)) =
        weightedMean π h
      rw [ih (markovOperator P h)]
      exact weightedMean_markovOperator π h P hstat

theorem markovIterate_markovOperator
    {ι : Type*} [Fintype ι]
    (P : FiniteKernel ι) (h : ι → ℝ) (n : ℕ) :
    markovIterate P n (markovOperator P h) =
      markovIterate P (n + 1) h := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih =>
      rw [markovIterate_succ, ih]
      rfl

theorem markovIterate_one
    {ι : Type*} [Fintype ι]
    (P : FiniteKernel ι) (n : ℕ) :
    markovIterate P n (fun _ => 1) = fun _ => 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [markovIterate_succ, ih]
      funext x
      exact markovOperator_one P x

/-- Cross moment between the path sum and a function of the current state. -/
theorem stationaryPath_sum_mul_current
    {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (P : FiniteKernel ι)
    (hπ_nonneg : ∀ x, 0 ≤ π x)
    (hπ_sum : ∑ x, π x = 1)
    (hstat : P.StationaryFor π)
    (f h : ι → ℝ) (n : ℕ) :
    stationaryPathExpectation π P hπ_nonneg hπ_sum n
        (fun p => chainPathSum f p * h (chainPathCurrent p)) =
      ∑ k ∈ Finset.range (n + 1),
        weightedInner π f (markovIterate P k h) := by
  induction n generalizing h with
  | zero =>
      rw [stationaryPathExpectation_eq_sum, chainPath_sum_zero]
      simp [chainPathMass, chainPathSum, chainPathCurrent,
        markovIterate, weightedInner]
      ring_nf
  | succ n ih =>
      rw [stationaryPathExpectation_succ]
      have hconditional :
          (fun p : ChainPath ι n =>
            ∑ y, P.prob (chainPathCurrent p) y *
              (chainPathSum f (.step y p) *
                h (chainPathCurrent (.step y p)))) =
          fun p =>
            chainPathSum f p *
                markovOperator P h (chainPathCurrent p) +
              markovOperator P (fun y => f y * h y)
                (chainPathCurrent p) := by
        funext p
        unfold markovOperator
        calc
          (∑ y, P.prob (chainPathCurrent p) y *
              (chainPathSum f (.step y p) *
                h (chainPathCurrent (.step y p)))) =
              ∑ y,
                (chainPathSum f p *
                    (P.prob (chainPathCurrent p) y * h y) +
                  P.prob (chainPathCurrent p) y * (f y * h y)) := by
            apply Finset.sum_congr rfl
            intro y _
            simp [chainPathSum, chainPathCurrent]
            ring
          _ = (∑ y, chainPathSum f p *
                (P.prob (chainPathCurrent p) y * h y)) +
              ∑ y, P.prob (chainPathCurrent p) y * (f y * h y) := by
            rw [Finset.sum_add_distrib]
          _ = chainPathSum f p *
                (∑ y, P.prob (chainPathCurrent p) y * h y) +
              ∑ y, P.prob (chainPathCurrent p) y * (f y * h y) := by
            rw [Finset.mul_sum]
      rw [hconditional]
      rw [stationaryPathExpectation_add]
      rw [ih (markovOperator P h)]
      rw [stationaryPath_current_expectation
        π P hπ_nonneg hπ_sum hstat n
        (markovOperator P (fun y => f y * h y))]
      rw [weightedMean_markovOperator
        π (fun y => f y * h y) P hstat]
      have hshift :
          (∑ k ∈ Finset.range (n + 1),
              weightedInner π f
                (markovIterate P k (markovOperator P h))) =
            ∑ k ∈ Finset.range (n + 1),
              weightedInner π f (markovIterate P (k + 1) h) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [markovIterate_markovOperator]
      rw [hshift]
      have hmean_inner :
          weightedMean π (fun y => f y * h y) =
            weightedInner π f h := by
        unfold weightedMean weightedInner
        apply Finset.sum_congr rfl
        intro x _
        ring
      rw [hmean_inner]
      change (∑ k ∈ Finset.range (n + 1),
          weightedInner π f (markovIterate P (k + 1) h)) +
          weightedInner π f h =
        ∑ k ∈ Finset.range (n + 2),
          weightedInner π f (markovIterate P k h)
      conv_rhs => rw [Finset.sum_range_succ']
      simp only [markovIterate_zero]

theorem stationaryPath_sum_expectation
    {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (P : FiniteKernel ι)
    (hπ_nonneg : ∀ x, 0 ≤ π x)
    (hπ_sum : ∑ x, π x = 1)
    (hstat : P.StationaryFor π)
    (f : ι → ℝ) (n : ℕ) :
    stationaryPathExpectation π P hπ_nonneg hπ_sum n
        (chainPathSum f) =
      ((n + 1 : ℕ) : ℝ) * weightedMean π f := by
  have hcross := stationaryPath_sum_mul_current
    π P hπ_nonneg hπ_sum hstat f (fun _ => 1) n
  simp_rw [markovIterate_one] at hcross
  have hinner : weightedInner π f (fun _ => 1) = weightedMean π f := by
    unfold weightedInner weightedMean
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hinner] at hcross
  simpa [Finset.sum_const, nsmul_eq_mul] using hcross

theorem weighted_lag_sum_succ
    (c : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
        (((n + 1 : ℕ) : ℝ) - (k : ℝ)) * c (k + 1)) =
      (∑ k ∈ Finset.range n,
        ((n : ℝ) - (k : ℝ)) * c (k + 1)) +
        ∑ k ∈ Finset.range (n + 1), c (k + 1) := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  have hmain :
      (∑ k ∈ Finset.range n,
          (((n + 1 : ℕ) : ℝ) - (k : ℝ)) * c (k + 1)) =
        (∑ k ∈ Finset.range n,
          ((n : ℝ) - (k : ℝ)) * c (k + 1)) +
          ∑ k ∈ Finset.range n, c (k + 1) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    norm_num [Nat.cast_add, Nat.cast_one]
    ring
  rw [hmain]
  norm_num [Nat.cast_add, Nat.cast_one]
  ring

/-- Exact second moment of the stationary path sum. -/
theorem stationaryPath_sum_secondMoment
    {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (P : FiniteKernel ι)
    (hπ_nonneg : ∀ x, 0 ≤ π x)
    (hπ_sum : ∑ x, π x = 1)
    (hstat : P.StationaryFor π)
    (f : ι → ℝ) (n : ℕ) :
    stationaryPathExpectation π P hπ_nonneg hπ_sum n
        (fun p => (chainPathSum f p) ^ 2) =
      ((n + 1 : ℕ) : ℝ) * weightedInner π f f +
        2 * ∑ k ∈ Finset.range n,
          ((n : ℝ) - (k : ℝ)) * lagCovariance π P f (k + 1) := by
  induction n with
  | zero =>
      rw [stationaryPathExpectation_eq_sum, chainPath_sum_zero]
      simp [chainPathMass, chainPathSum, weightedInner, lagCovariance]
      ring_nf
  | succ n ih =>
      rw [stationaryPathExpectation_succ]
      have hconditional :
          (fun p : ChainPath ι n =>
            ∑ y, P.prob (chainPathCurrent p) y *
              (chainPathSum f (.step y p)) ^ 2) =
          fun p =>
            (chainPathSum f p) ^ 2 +
              2 * (chainPathSum f p *
                markovOperator P f (chainPathCurrent p)) +
              markovOperator P (fun y => (f y) ^ 2)
                (chainPathCurrent p) := by
        funext p
        unfold markovOperator
        calc
          (∑ y, P.prob (chainPathCurrent p) y *
              (chainPathSum f (.step y p)) ^ 2) =
              ∑ y,
                (P.prob (chainPathCurrent p) y *
                    (chainPathSum f p) ^ 2 +
                  (2 * chainPathSum f p) *
                    (P.prob (chainPathCurrent p) y * f y) +
                  P.prob (chainPathCurrent p) y * (f y) ^ 2) := by
            apply Finset.sum_congr rfl
            intro y _
            simp [chainPathSum]
            ring
          _ = (∑ y, P.prob (chainPathCurrent p) y *
                  (chainPathSum f p) ^ 2) +
                (∑ y, (2 * chainPathSum f p) *
                  (P.prob (chainPathCurrent p) y * f y)) +
              ∑ y, P.prob (chainPathCurrent p) y * (f y) ^ 2 := by
            simp only [Finset.sum_add_distrib]
          _ = (∑ y, P.prob (chainPathCurrent p) y) *
                  (chainPathSum f p) ^ 2 +
                (2 * chainPathSum f p) *
                  (∑ y, P.prob (chainPathCurrent p) y * f y) +
              ∑ y, P.prob (chainPathCurrent p) y * (f y) ^ 2 := by
            rw [Finset.sum_mul, Finset.mul_sum]
          _ = (chainPathSum f p) ^ 2 +
                2 * (chainPathSum f p *
                  (∑ y, P.prob (chainPathCurrent p) y * f y)) +
              ∑ y, P.prob (chainPathCurrent p) y * (f y) ^ 2 := by
            rw [P.row_sum]
            ring
      rw [hconditional]
      rw [stationaryPathExpectation_add, stationaryPathExpectation_add]
      rw [ih]
      rw [stationaryPathExpectation_smul]
      rw [stationaryPath_sum_mul_current
        π P hπ_nonneg hπ_sum hstat f (markovOperator P f) n]
      rw [stationaryPath_current_expectation
        π P hπ_nonneg hπ_sum hstat n
        (markovOperator P (fun y => (f y) ^ 2))]
      rw [weightedMean_markovOperator π (fun y => (f y) ^ 2) P hstat]
      have hshift :
          (∑ k ∈ Finset.range (n + 1),
              weightedInner π f
                (markovIterate P k (markovOperator P f))) =
            ∑ k ∈ Finset.range (n + 1),
              lagCovariance π P f (k + 1) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [markovIterate_markovOperator]
        rfl
      rw [hshift]
      rw [weighted_lag_sum_succ]
      have hsquare : weightedMean π (fun y => (f y) ^ 2) =
          weightedInner π f f := by
        unfold weightedMean weightedInner
        apply Finset.sum_congr rfl
        intro x _
        ring
      rw [hsquare]
      norm_num [Nat.cast_add, Nat.cast_one]
      ring

end LeanMetro
