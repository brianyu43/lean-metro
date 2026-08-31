import LeanMetroGeneral.AcceptedFlow
import LeanMetro.AcceptanceRule
import Mathlib.MeasureTheory.Measure.Count

namespace LeanMetroGeneral

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι]

/-- Turn a finite table of nonnegative real weights into a measure-valued
kernel. `ENNReal.ofReal` makes the definition total; stochasticity is not
needed for the accepted-flow comparison itself. -/
def finiteProposalKernel (q : ι → ι → ℝ) : Kernel ι ι :=
  Kernel.ofFunOfCountable fun x =>
    ∑ y, ENNReal.ofReal (q x y) • Measure.dirac y

@[simp]
theorem finiteProposalKernel_apply_singleton
    (q : ι → ι → ℝ) (x y : ι) :
    finiteProposalKernel q x {y} = ENNReal.ofReal (q x y) := by
  classical
  simp [finiteProposalKernel, Kernel.ofFunOfCountable]
  rw [Finset.sum_eq_single y]
  · simp
  · intro b _ hby
    simp [Pi.single_eq_of_ne hby]
  · simp

instance finiteProposalKernel_isFiniteKernel (q : ι → ι → ℝ) :
    IsFiniteKernel (finiteProposalKernel q) := by
  constructor
  let C : ℝ≥0∞ := ∑ x, ∑ y, ENNReal.ofReal (q x y)
  refine ⟨C, ?_, fun x => ?_⟩
  · dsimp [C]
    simp only [ENNReal.sum_lt_top]
    exact fun _ _ _ _ => ENNReal.ofReal_lt_top
  · calc
      finiteProposalKernel q x Set.univ = ∑ y, ENNReal.ofReal (q x y) := by
        classical
        simp [finiteProposalKernel, Kernel.ofFunOfCountable]
      _ ≤ C := by
        dsimp [C]
        refine Finset.single_le_sum
          (f := fun i : ι => ∑ y, ENNReal.ofReal (q i y)) ?_
          (Finset.mem_univ x)
        intro i _
        exact bot_le

@[simp]
theorem proposalFlow_count_finiteProposalKernel_apply_singleton
    (q : ι → ι → ℝ) (x y : ι) :
    proposalFlow Measure.count (finiteProposalKernel q) {(x, y)} =
      ENNReal.ofReal (q x y) := by
  rw [show ({(x, y)} : Set (ι × ι)) = {x} ×ˢ {y} by ext z; simp]
  rw [proposalFlow, Measure.compProd_apply_prod
    (measurableSet_singleton x) (measurableSet_singleton y)]
  simp

/-- A symmetric finite table induces a swap-symmetric joint proposal flow
under counting measure. -/
theorem finiteProposalKernel_referenceReversible
    (q : ι → ι → ℝ) (hq_symm : ∀ x y, q x y = q y x) :
    ReferenceReversible Measure.count (finiteProposalKernel q) := by
  unfold ReferenceReversible ReversibleFor FlowSymmetric
  apply Measure.ext_of_singleton
  intro z
  rcases z with ⟨x, y⟩
  rw [reverseFlow, Measure.map_apply measurable_swap (measurableSet_singleton (x, y))]
  rw [show Prod.swap ⁻¹' ({(x, y)} : Set (ι × ι)) = {(y, x)} by
    ext z
    rcases z with ⟨u, v⟩
    simp [and_comm]]
  simp [hq_symm]

def finiteTargetDensity (w : ι → ℝ) : ι → ℝ≥0∞ :=
  fun x => ENNReal.ofReal (w x)

def finiteAcceptanceDensity (a : ι → ι → ℝ) : ι → ι → ℝ≥0∞ :=
  fun x y => ENNReal.ofReal (a x y)

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- For a symmetric positive proposal, the finite weighted-flow balance law
reduces to the density balance law used by the reference-state theory. -/
theorem finite_density_balance_of_symmetric
    (w : ι → ℝ) (q a : ι → ι → ℝ)
    (hq_pos : ∀ x y, 0 < q x y)
    (hq_symm : ∀ x y, q x y = q y x)
    (ha : LeanMetro.AdmissibleAcceptance w q a)
    (x y : ι) :
    w x * a x y = w y * a y x := by
  have hcancel :
      q x y * (w x * a x y) = q x y * (w y * a y x) := by
    calc
      q x y * (w x * a x y) = (w x * q x y) * a x y := by ring
      _ = (w y * q y x) * a y x := ha.balance x y
      _ = q x y * (w y * a y x) := by rw [← hq_symm x y]; ring
  exact mul_left_cancel₀ (ne_of_gt (hq_pos x y)) hcancel

/-- A finite admissible rule for a positive symmetric proposal supplies the
measure-theoretic admissibility interface. -/
theorem finite_admissibleAcceptance_to_general
    (w : ι → ℝ) (q a : ι → ι → ℝ)
    (hw : ∀ x, 0 < w x)
    (hq_pos : ∀ x y, 0 < q x y)
    (hq_symm : ∀ x y, q x y = q y x)
    (ha : LeanMetro.AdmissibleAcceptance w q a) :
    AdmissibleAcceptance Measure.count (finiteProposalKernel q)
      (finiteTargetDensity w) (finiteAcceptanceDensity a) := by
  constructor
  · exact measurable_of_finite _
  · intro x y
    exact ENNReal.ofReal_le_one.mpr (ha.le_one x y)
  · exact Filter.Eventually.of_forall fun z => by
      change ENNReal.ofReal (w z.1) * ENNReal.ofReal (a z.1 z.2) =
        ENNReal.ofReal (w z.2) * ENNReal.ofReal (a z.2 z.1)
      rw [← ENNReal.ofReal_mul (hw z.1).le]
      rw [← ENNReal.ofReal_mul (hw z.2).le]
      exact congrArg ENNReal.ofReal
        (finite_density_balance_of_symmetric w q a hq_pos hq_symm ha z.1 z.2)

/-- The general accepted-flow theorem instantiated on a finite discrete state
space.  This is the first regression bridge from the new namespace to the
existing finite implementation. -/
theorem finite_referenceMH_acceptedFlow_maximal
    (w : ι → ℝ) (q a : ι → ι → ℝ)
    (hw : ∀ x, 0 < w x)
    (hq_pos : ∀ x y, 0 < q x y)
    (hq_symm : ∀ x y, q x y = q y x)
    (ha : LeanMetro.AdmissibleAcceptance w q a) :
    acceptedFlow Measure.count (finiteProposalKernel q)
        (finiteTargetDensity w) (finiteAcceptanceDensity a) ≤
      referenceMHAcceptedFlow Measure.count (finiteProposalKernel q)
        (finiteTargetDensity w) := by
  exact referenceMH_acceptedFlow_maximal
    (finite_admissibleAcceptance_to_general w q a hw hq_pos hq_symm ha)

/-- End-to-end finite regression for the new public theorem: both accepted
flows are symmetric and the MH accepted flow is maximal. -/
theorem finite_referenceMH_largest_reversibleAcceptedFlow
    (w : ι → ℝ) (q a : ι → ι → ℝ)
    (hw : ∀ x, 0 < w x)
    (hq_pos : ∀ x y, 0 < q x y)
    (hq_symm : ∀ x y, q x y = q y x)
    (ha : LeanMetro.AdmissibleAcceptance w q a) :
    FlowSymmetric
        (acceptedFlow Measure.count (finiteProposalKernel q)
          (finiteTargetDensity w) (finiteAcceptanceDensity a)) ∧
      FlowSymmetric
        (referenceMHAcceptedFlow Measure.count (finiteProposalKernel q)
          (finiteTargetDensity w)) ∧
      acceptedFlow Measure.count (finiteProposalKernel q)
          (finiteTargetDensity w) (finiteAcceptanceDensity a) ≤
        referenceMHAcceptedFlow Measure.count (finiteProposalKernel q)
          (finiteTargetDensity w) := by
  exact referenceMH_largest_reversibleAcceptedFlow
    (finiteProposalKernel_referenceReversible q hq_symm)
    (measurable_of_finite _)
    (finite_admissibleAcceptance_to_general w q a hw hq_pos hq_symm ha)

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- At an atom, the new density theorem recovers the same accepted-move
inequality as the existing finite theorem, for its reference-reversible
(symmetric positive proposal) specialization.  The fully asymmetric adapter
belongs to the later `ν ⊓ reverseFlow ν` layer. -/
theorem general_reference_maximality_recovers_finite_mhAcceptedMove_maximal
    (w : ι → ℝ) (q a : ι → ι → ℝ)
    (hw : ∀ x, 0 < w x)
    (hq_pos : ∀ x y, 0 < q x y)
    (hq_symm : ∀ x y, q x y = q y x)
    (ha : LeanMetro.AdmissibleAcceptance w q a)
    (x y : ι) :
    LeanMetro.acceptRejectAcceptedMove q a x y ≤
      LeanMetro.mhAsymmetricAcceptedMove w q x y := by
  have hbalance :=
    finite_density_balance_of_symmetric w q a hq_pos hq_symm ha x y
  have hbalanceENN :
      finiteTargetDensity w x * finiteAcceptanceDensity a x y =
        finiteTargetDensity w y * finiteAcceptanceDensity a y x := by
    change ENNReal.ofReal (w x) * ENNReal.ofReal (a x y) =
      ENNReal.ofReal (w y) * ENNReal.ofReal (a y x)
    rw [← ENNReal.ofReal_mul (hw x).le]
    rw [← ENNReal.ofReal_mul (hw y).le]
    exact congrArg ENNReal.ofReal hbalance
  have hdensity := acceptedFlowDensity_le_referenceMH_at x y
    (ENNReal.ofReal_le_one.mpr (ha.le_one x y))
    (ENNReal.ofReal_le_one.mpr (ha.le_one y x)) hbalanceENN
  have hflow : w x * a x y ≤ min (w x) (w y) := by
    apply (ENNReal.ofReal_le_ofReal_iff
      (le_min (hw x).le (hw y).le)).mp
    rw [ENNReal.ofReal_mul (hw x).le, ENNReal.ofReal_min]
    simpa [acceptedFlowDensity, referenceMHAcceptedDensity,
      finiteTargetDensity, finiteAcceptanceDensity] using hdensity
  have haccept : a x y ≤ min 1 (w y / w x) := by
    have hmul :
        w x * a x y ≤ w x * min 1 (w y / w x) := by
      rw [LeanMetro.nonneg_mul_acceptance_eq_min (hw x).le (hw y).le]
      exact hflow
    nlinarith [hw x]
  have hratio :
      (w y * q y x) / (w x * q x y) = w y / w x := by
    rw [← hq_symm x y]
    field_simp [ne_of_gt (hq_pos x y), ne_of_gt (hw x)]
  have hmove := mul_le_mul_of_nonneg_left haccept (hq_pos x y).le
  simpa [LeanMetro.acceptRejectAcceptedMove,
    LeanMetro.mhAsymmetricAcceptedMove, LeanMetro.mhAsymmetricAcceptance,
    hratio] using hmove

end

end LeanMetroGeneral
