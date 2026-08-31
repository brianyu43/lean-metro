import LeanMetro.IrreduciblePeskun
import LeanMetro.IrreducibilityExample

namespace LeanMetro

open Filter
open scoped Topology

private theorem finiteKernel_ext_prob
    {ι : Type*} [Fintype ι] {P Q : FiniteKernel ι}
    (h : P.prob = Q.prob) : P = Q := by
  cases P
  cases Q
  cases h
  rfl

/-! ## End-to-end use of the probabilistic Peskun theorem

This file is an integration test for the public crown theorem.  The target is
the original two-state weight `(1, 3)`, the proposal always switches state,
and the competitor accepts each proposal with one half of the MH acceptance
probability.  Consequently the MH and competitor kernels are exactly the
previously studied `twoStateFiniteKernel` and `twoStateLazyKernel`.
-/

/-- A deliberately slower, but still admissible, acceptance rule: one half of
the Metropolis--Hastings acceptance probability. -/
noncomputable def twoStateHalfMHAcceptance (x y : Fin 2) : ℝ :=
  (1 / 2 : ℝ) *
    mhAsymmetricAcceptance twoStateWeight twoStateProposal x y

theorem two_state_halfMHAcceptance_admissible :
    AdmissibleAcceptance twoStateWeight twoStateProposal
      twoStateHalfMHAcceptance := by
  constructor
  · intro x y
    fin_cases x <;> fin_cases y <;>
      norm_num [twoStateHalfMHAcceptance, mhAsymmetricAcceptance,
        twoStateWeight, twoStateProposal]
  · intro x y
    fin_cases x <;> fin_cases y <;>
      norm_num [twoStateHalfMHAcceptance, mhAsymmetricAcceptance,
        twoStateWeight, twoStateProposal]
  · intro x y
    fin_cases x <;> fin_cases y <;>
      norm_num [twoStateHalfMHAcceptance, mhAsymmetricAcceptance,
        twoStateWeight, twoStateProposal]

/-- The exact MH kernel appearing in the crown theorem. -/
noncomputable abbrev twoStateCrownMHKernel : FiniteKernel (Fin 2) :=
  metropolisHastingsKernel twoStateWeight twoStateProposal
    two_state_weight_pos two_state_proposal_nonneg
    two_state_proposal_row_sum

/-- The exact competitor kernel appearing in the crown theorem. -/
noncomputable abbrev twoStateCrownCompetitorKernel : FiniteKernel (Fin 2) :=
  acceptRejectKernel twoStateProposal twoStateHalfMHAcceptance
    two_state_proposal_nonneg two_state_proposal_row_sum
    two_state_halfMHAcceptance_admissible.nonneg
    two_state_halfMHAcceptance_admissible.le_one

theorem two_state_crown_mhKernel_eq :
    twoStateCrownMHKernel = twoStateFiniteKernel := by
  apply finiteKernel_ext_prob
  funext x y
  fin_cases x <;> fin_cases y <;>
    norm_num [twoStateCrownMHKernel, metropolisHastingsKernel,
      mhAsymmetricTransition, mhAsymmetricLeavingMass,
      mhAsymmetricAcceptedMove, mhAsymmetricAcceptance,
      twoStateFiniteKernel, twoStateTransition, twoStateWeight,
      twoStateProposal]

theorem two_state_crown_competitorKernel_eq :
    twoStateCrownCompetitorKernel = twoStateLazyKernel := by
  apply finiteKernel_ext_prob
  funext x y
  fin_cases x <;> fin_cases y <;>
    norm_num [twoStateCrownCompetitorKernel, acceptRejectKernel,
      acceptRejectTransition, acceptRejectLeavingMass,
      acceptRejectAcceptedMove, twoStateHalfMHAcceptance,
      mhAsymmetricAcceptance, twoStateLazyKernel, twoStateWeight,
      twoStateProposal]

theorem two_state_normalizedWeight_eq_stationary :
    normalizedWeight twoStateWeight = twoStateStationary := by
  funext x
  exact two_state_stationary_eq_normalized x

theorem two_state_stationary_nonneg :
    ∀ x, 0 ≤ twoStateStationary x := by
  intro x
  fin_cases x <;> norm_num [twoStateStationary]

theorem two_state_stationary_sum :
    ∑ x, twoStateStationary x = 1 := by
  norm_num [twoStateStationary, Fin.sum_univ_two]

theorem two_state_crown_mh_meanZeroPoissonInvertible :
    MeanZeroPoissonInvertible
      (normalizedWeight twoStateWeight) twoStateCrownMHKernel := by
  rw [two_state_normalizedWeight_eq_stationary,
    two_state_crown_mhKernel_eq]
  exact two_state_mh_meanZeroPoissonInvertible_from_irreducible

theorem two_state_crown_competitor_meanZeroPoissonInvertible :
    MeanZeroPoissonInvertible
      (normalizedWeight twoStateWeight) twoStateCrownCompetitorKernel := by
  rw [two_state_normalizedWeight_eq_stationary,
    two_state_crown_competitorKernel_eq]
  exact two_state_lazy_meanZeroPoissonInvertible_from_irreducible

theorem two_state_crown_observable_meanZero :
    MeanZero (normalizedWeight twoStateWeight)
      twoStateCenteredObservable := by
  rw [two_state_normalizedWeight_eq_stationary]
  exact two_state_observable_meanZero

theorem two_state_crown_mh_selectedSolution_eq :
    poissonSolution
        (normalizedWeight twoStateWeight) twoStateCrownMHKernel
        two_state_crown_mh_meanZeroPoissonInvertible
        twoStateCenteredObservable two_state_crown_observable_meanZero =
      twoStateMHPoissonSolution := by
  apply poissonSolution_eq_of_meanZero_solution
  · rw [two_state_normalizedWeight_eq_stationary]
    exact two_state_mh_explicitSolution_meanZero
  · rw [two_state_crown_mhKernel_eq]
    exact two_state_mh_explicitSolution_equation

theorem two_state_crown_competitor_selectedSolution_eq :
    poissonSolution
        (normalizedWeight twoStateWeight) twoStateCrownCompetitorKernel
        two_state_crown_competitor_meanZeroPoissonInvertible
        twoStateCenteredObservable two_state_crown_observable_meanZero =
      twoStateLazyPoissonSolution := by
  apply poissonSolution_eq_of_meanZero_solution
  · rw [two_state_normalizedWeight_eq_stationary]
    exact two_state_lazy_explicitSolution_meanZero
  · rw [two_state_crown_competitorKernel_eq]
    exact two_state_lazy_explicitSolution_equation

theorem two_state_mh_iterate_solution (n : ℕ) :
    markovIterate twoStateFiniteKernel n twoStateMHPoissonSolution =
      fun x => ((-1 / 3 : ℝ) ^ n) * twoStateMHPoissonSolution x := by
  induction n with
  | zero =>
      funext x
      simp [markovIterate]
  | succ n ih =>
      rw [markovIterate_succ, ih]
      funext x
      fin_cases x <;>
        norm_num [markovOperator, twoStateFiniteKernel,
          twoStateTransition, twoStateMHPoissonSolution,
          Fin.sum_univ_two, pow_succ] <;> ring

theorem two_state_competitor_iterate_solution (n : ℕ) :
    markovIterate twoStateLazyKernel n twoStateLazyPoissonSolution =
      fun x => ((1 / 3 : ℝ) ^ n) * twoStateLazyPoissonSolution x := by
  induction n with
  | zero =>
      funext x
      simp [markovIterate]
  | succ n ih =>
      rw [markovIterate_succ, ih]
      funext x
      fin_cases x <;>
        norm_num [markovOperator, twoStateLazyKernel,
          twoStateLazyPoissonSolution, Fin.sum_univ_two,
          pow_succ] <;> ring

theorem two_state_mh_poisson_covariance_formula (n : ℕ) :
    weightedInner twoStateStationary twoStateCenteredObservable
        (markovIterate twoStateFiniteKernel n twoStateMHPoissonSolution) =
      (9 / 4 : ℝ) * (-1 / 3 : ℝ) ^ n := by
  rw [two_state_mh_iterate_solution]
  norm_num [weightedInner, twoStateStationary,
    twoStateCenteredObservable, twoStateMHPoissonSolution,
    Fin.sum_univ_two]
  ring

theorem two_state_competitor_poisson_covariance_formula (n : ℕ) :
    weightedInner twoStateStationary twoStateCenteredObservable
        (markovIterate twoStateLazyKernel n twoStateLazyPoissonSolution) =
      (9 / 2 : ℝ) * (1 / 3 : ℝ) ^ n := by
  rw [two_state_competitor_iterate_solution]
  norm_num [weightedInner, twoStateStationary,
    twoStateCenteredObservable, twoStateLazyPoissonSolution,
    Fin.sum_univ_two]
  ring

theorem two_state_crown_mh_poisson_covariance_tendsto_zero :
    Tendsto
      (fun n => weightedInner (normalizedWeight twoStateWeight)
        twoStateCenteredObservable
        (markovIterate twoStateCrownMHKernel n
          (poissonSolution
            (normalizedWeight twoStateWeight) twoStateCrownMHKernel
            two_state_crown_mh_meanZeroPoissonInvertible
            twoStateCenteredObservable two_state_crown_observable_meanZero)))
      atTop (𝓝 0) := by
  rw [two_state_crown_mh_selectedSolution_eq]
  have hpow : Tendsto (fun n : ℕ => (-1 / 3 : ℝ) ^ n)
      atTop (𝓝 0) := by
    exact tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num)
  have hscaled : Tendsto
      (fun n : ℕ => (9 / 4 : ℝ) * (-1 / 3 : ℝ) ^ n)
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hpow : Tendsto
      (fun n : ℕ => (9 / 4 : ℝ) * (-1 / 3 : ℝ) ^ n)
      atTop (𝓝 ((9 / 4 : ℝ) * 0)))
  simpa only [two_state_normalizedWeight_eq_stationary,
    two_state_crown_mhKernel_eq,
    two_state_mh_poisson_covariance_formula] using hscaled

theorem two_state_crown_competitor_poisson_covariance_tendsto_zero :
    Tendsto
      (fun n => weightedInner (normalizedWeight twoStateWeight)
        twoStateCenteredObservable
        (markovIterate twoStateCrownCompetitorKernel n
          (poissonSolution
            (normalizedWeight twoStateWeight) twoStateCrownCompetitorKernel
            two_state_crown_competitor_meanZeroPoissonInvertible
            twoStateCenteredObservable two_state_crown_observable_meanZero)))
      atTop (𝓝 0) := by
  rw [two_state_crown_competitor_selectedSolution_eq]
  have hpow : Tendsto (fun n : ℕ => (1 / 3 : ℝ) ^ n)
      atTop (𝓝 0) := by
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hscaled : Tendsto
      (fun n : ℕ => (9 / 2 : ℝ) * (1 / 3 : ℝ) ^ n)
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hpow : Tendsto
      (fun n : ℕ => (9 / 2 : ℝ) * (1 / 3 : ℝ) ^ n)
      atTop (𝓝 ((9 / 2 : ℝ) * 0)))
  simpa only [two_state_normalizedWeight_eq_stationary,
    two_state_crown_competitorKernel_eq,
    two_state_competitor_poisson_covariance_formula] using hscaled

/-- Direct invocation of the public crown theorem on a concrete MH rule and a
concrete admissible competitor derived from the same target and proposal. -/
theorem two_state_crown_theorem :
    HasSampleMeanAsymptoticVariance
        (normalizedWeight twoStateWeight) twoStateCrownMHKernel
        (normalizedWeight_nonneg twoStateWeight two_state_weight_pos)
        (normalizedWeight_sum twoStateWeight two_state_weight_pos)
        twoStateCenteredObservable
        (algebraicAsymptoticVariance
          (normalizedWeight twoStateWeight) twoStateCrownMHKernel
          two_state_crown_mh_meanZeroPoissonInvertible
          twoStateCenteredObservable two_state_crown_observable_meanZero) ∧
      HasSampleMeanAsymptoticVariance
        (normalizedWeight twoStateWeight) twoStateCrownCompetitorKernel
        (normalizedWeight_nonneg twoStateWeight two_state_weight_pos)
        (normalizedWeight_sum twoStateWeight two_state_weight_pos)
        twoStateCenteredObservable
        (algebraicAsymptoticVariance
          (normalizedWeight twoStateWeight) twoStateCrownCompetitorKernel
          two_state_crown_competitor_meanZeroPoissonInvertible
          twoStateCenteredObservable two_state_crown_observable_meanZero) ∧
      algebraicAsymptoticVariance
          (normalizedWeight twoStateWeight) twoStateCrownMHKernel
          two_state_crown_mh_meanZeroPoissonInvertible
          twoStateCenteredObservable two_state_crown_observable_meanZero ≤
        algebraicAsymptoticVariance
          (normalizedWeight twoStateWeight) twoStateCrownCompetitorKernel
          two_state_crown_competitor_meanZeroPoissonInvertible
          twoStateCenteredObservable two_state_crown_observable_meanZero := by
  exact metropolisHastings_minimizes_sampleMeanAsymptoticVariance
    twoStateWeight twoStateProposal twoStateHalfMHAcceptance
    two_state_weight_pos two_state_proposal_nonneg
    two_state_proposal_row_sum
    two_state_halfMHAcceptance_admissible
    two_state_crown_mh_meanZeroPoissonInvertible
    two_state_crown_competitor_meanZeroPoissonInvertible
    twoStateCenteredObservable two_state_crown_observable_meanZero
    two_state_crown_mh_poisson_covariance_tendsto_zero
    two_state_crown_competitor_poisson_covariance_tendsto_zero

/-- Concrete consequence of the crown-theorem invocation: the actual scaled
sample-mean variances converge to `3/2` for MH and `6` for the half-acceptance
competitor, with the promised non-strict ordering. -/
theorem two_state_crown_actual_limits_and_order :
    HasSampleMeanAsymptoticVariance
        twoStateStationary twoStateFiniteKernel
        two_state_stationary_nonneg two_state_stationary_sum
        twoStateCenteredObservable (3 / 2 : ℝ) ∧
      HasSampleMeanAsymptoticVariance
        twoStateStationary twoStateLazyKernel
        two_state_stationary_nonneg two_state_stationary_sum
        twoStateCenteredObservable 6 ∧
      (3 / 2 : ℝ) ≤ 6 := by
  simpa only [two_state_normalizedWeight_eq_stationary,
    two_state_crown_mhKernel_eq,
    two_state_crown_competitorKernel_eq,
    two_state_mh_algebraicAsymptoticVariance,
    two_state_lazy_algebraicAsymptoticVariance] using
      two_state_crown_theorem

theorem two_state_crown_mh_irreducible :
    twoStateCrownMHKernel.Irreducible := by
  rw [two_state_crown_mhKernel_eq]
  exact two_state_mh_irreducible

theorem two_state_crown_competitor_irreducible :
    twoStateCrownCompetitorKernel.Irreducible := by
  rw [two_state_crown_competitorKernel_eq]
  exact two_state_lazy_irreducible

/-- Direct use of the v1.3 standard-assumption wrapper. Unlike
`two_state_crown_theorem`, this proof supplies neither Poisson inverses nor
pointwise covariance-decay theorems. -/
theorem two_state_crown_theorem_of_irreducible :
    HasSampleMeanAsymptoticVariance
        (normalizedWeight twoStateWeight) twoStateCrownMHKernel
        (normalizedWeight_nonneg twoStateWeight two_state_weight_pos)
        (normalizedWeight_sum twoStateWeight two_state_weight_pos)
        twoStateCenteredObservable
        (algebraicAsymptoticVariance
          (normalizedWeight twoStateWeight) twoStateCrownMHKernel
          two_state_crown_mh_meanZeroPoissonInvertible
          twoStateCenteredObservable two_state_crown_observable_meanZero) ∧
      HasSampleMeanAsymptoticVariance
        (normalizedWeight twoStateWeight) twoStateCrownCompetitorKernel
        (normalizedWeight_nonneg twoStateWeight two_state_weight_pos)
        (normalizedWeight_sum twoStateWeight two_state_weight_pos)
        twoStateCenteredObservable
        (algebraicAsymptoticVariance
          (normalizedWeight twoStateWeight) twoStateCrownCompetitorKernel
          two_state_crown_competitor_meanZeroPoissonInvertible
          twoStateCenteredObservable two_state_crown_observable_meanZero) ∧
      algebraicAsymptoticVariance
          (normalizedWeight twoStateWeight) twoStateCrownMHKernel
          two_state_crown_mh_meanZeroPoissonInvertible
          twoStateCenteredObservable two_state_crown_observable_meanZero ≤
        algebraicAsymptoticVariance
          (normalizedWeight twoStateWeight) twoStateCrownCompetitorKernel
          two_state_crown_competitor_meanZeroPoissonInvertible
          twoStateCenteredObservable two_state_crown_observable_meanZero := by
  simpa only using
    metropolisHastings_minimizes_sampleMeanAsymptoticVariance_of_irreducible
      twoStateWeight twoStateProposal twoStateHalfMHAcceptance
      two_state_weight_pos two_state_proposal_nonneg
      two_state_proposal_row_sum
      two_state_halfMHAcceptance_admissible
      two_state_crown_mh_irreducible
      two_state_crown_competitor_irreducible
      twoStateCenteredObservable two_state_crown_observable_meanZero

/-- End-to-end concrete consequence of the irreducibility-facing wrapper:
actual scaled sample-mean variance limits `3/2` and `6`, without any decay or
Poisson-inverse argument at the call site. -/
theorem two_state_crown_actual_limits_and_order_of_irreducible :
    HasSampleMeanAsymptoticVariance
        twoStateStationary twoStateFiniteKernel
        two_state_stationary_nonneg two_state_stationary_sum
        twoStateCenteredObservable (3 / 2 : ℝ) ∧
      HasSampleMeanAsymptoticVariance
        twoStateStationary twoStateLazyKernel
        two_state_stationary_nonneg two_state_stationary_sum
        twoStateCenteredObservable 6 ∧
      (3 / 2 : ℝ) ≤ 6 := by
  simpa only [two_state_normalizedWeight_eq_stationary,
    two_state_crown_mhKernel_eq,
    two_state_crown_competitorKernel_eq,
    two_state_mh_algebraicAsymptoticVariance,
    two_state_lazy_algebraicAsymptoticVariance] using
      two_state_crown_theorem_of_irreducible

end LeanMetro
