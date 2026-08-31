import LeanMetroGeneral.ReferenceProposal

namespace LeanMetroGeneral

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

variable {X : Type*} [MeasurableSpace X]

/-- The density of moves accepted by a rule `a`, measured relative to the
reference proposal flow. -/
def acceptedFlowDensity
    (h : X → ℝ≥0∞) (a : X → X → ℝ≥0∞) (z : X × X) : ℝ≥0∞ :=
  h z.1 * a z.1 z.2

/-- The accepted off-diagonal flow associated with a target density `h` and
an acceptance rule `a`. -/
noncomputable def acceptedFlow
    (μ : Measure X) (Q : Kernel X X)
    (h : X → ℝ≥0∞) (a : X → X → ℝ≥0∞) :
    Measure (X × X) :=
  (proposalFlow μ Q).withDensity (acceptedFlowDensity h a)

/-- The reference-reversible Metropolis--Hastings accepted density. -/
def referenceMHAcceptedDensity (h : X → ℝ≥0∞) (z : X × X) : ℝ≥0∞ :=
  min (h z.1) (h z.2)

/-- The largest accepted flow allowed by the two directional target flows. -/
noncomputable def referenceMHAcceptedFlow
    (μ : Measure X) (Q : Kernel X X) (h : X → ℝ≥0∞) :
    Measure (X × X) :=
  (proposalFlow μ Q).withDensity (referenceMHAcceptedDensity h)

/-- An acceptance rule is admissible when it is measurable, takes values at
most one, and balances the accepted target flow in both directions.  The
pointwise bound is the natural statement that `a(x,y)` is a probability;
balance only needs to hold almost everywhere for the joint proposal flow. -/
structure AdmissibleAcceptance
    (μ : Measure X) (Q : Kernel X X)
    (h : X → ℝ≥0∞) (a : X → X → ℝ≥0∞) : Prop where
  measurable : Measurable (Function.uncurry a)
  le_one : ∀ x y, a x y ≤ 1
  balance :
    (fun z : X × X => h z.1 * a z.1 z.2) =ᵐ[proposalFlow μ Q]
      (fun z : X × X => h z.2 * a z.2 z.1)

theorem measurable_acceptedFlowDensity
    {h : X → ℝ≥0∞} {a : X → X → ℝ≥0∞}
    (hh : Measurable h) (ha : Measurable (Function.uncurry a)) :
    Measurable (acceptedFlowDensity h a) := by
  exact (hh.comp measurable_fst).mul ha

theorem measurable_referenceMHAcceptedDensity
    {h : X → ℝ≥0∞} (hh : Measurable h) :
    Measurable (referenceMHAcceptedDensity h) := by
  exact (hh.comp measurable_fst).min (hh.comp measurable_snd)

omit [MeasurableSpace X] in
/-- Pointwise scalar core of accepted-flow maximality.  This is the exact
general-state analogue of `Aa ≤ A`, `Aa = Baᵀ ≤ B`, hence `Aa ≤ min A B`. -/
theorem acceptedFlowDensity_le_referenceMH_at
    {h : X → ℝ≥0∞} {a : X → X → ℝ≥0∞} (x y : X)
    (hle_xy : a x y ≤ 1) (hle_yx : a y x ≤ 1)
    (hbalance : h x * a x y = h y * a y x) :
    acceptedFlowDensity h a (x, y) ≤ referenceMHAcceptedDensity h (x, y) := by
  apply le_min
  · calc
      h x * a x y ≤ h x * 1 := mul_le_mul_right hle_xy (h x)
      _ = h x := mul_one _
  · calc
      h x * a x y = h y * a y x := hbalance
      _ ≤ h y * 1 := mul_le_mul_right hle_yx (h y)
      _ = h y := mul_one _

/-- Density balance becomes symmetry of the accepted-flow measure whenever
the reference proposal flow itself is symmetric. -/
theorem acceptedFlow_symmetric
    {μ : Measure X} {Q : Kernel X X}
    {h : X → ℝ≥0∞} {a : X → X → ℝ≥0∞}
    (hrev : ReferenceReversible μ Q) (hh : Measurable h)
    (ha : AdmissibleAcceptance μ Q h a) :
    FlowSymmetric (acceptedFlow μ Q h a) := by
  unfold FlowSymmetric acceptedFlow
  rw [reverseFlow_withDensity _ _
    (measurable_acceptedFlowDensity hh ha.measurable)]
  rw [hrev]
  apply withDensity_congr_ae
  filter_upwards [ha.balance] with z hbalance
  simpa [acceptedFlowDensity, Function.comp_def] using hbalance.symm

/-- The reference Metropolis--Hastings accepted flow is itself symmetric. -/
theorem referenceMHAcceptedFlow_symmetric
    {μ : Measure X} {Q : Kernel X X} {h : X → ℝ≥0∞}
    (hrev : ReferenceReversible μ Q) (hh : Measurable h) :
    FlowSymmetric (referenceMHAcceptedFlow μ Q h) := by
  unfold FlowSymmetric referenceMHAcceptedFlow
  rw [reverseFlow_withDensity _ _
    (measurable_referenceMHAcceptedDensity hh)]
  rw [hrev]
  apply withDensity_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    simp [referenceMHAcceptedDensity, min_comm]

/-- The scalar `min(A,B)` argument, now stated almost everywhere for a joint
proposal measure. -/
theorem acceptedFlowDensity_le_referenceMH
    {μ : Measure X} {Q : Kernel X X}
    {h : X → ℝ≥0∞} {a : X → X → ℝ≥0∞}
    (ha : AdmissibleAcceptance μ Q h a) :
    acceptedFlowDensity h a ≤ᵐ[proposalFlow μ Q]
      referenceMHAcceptedDensity h := by
  filter_upwards [ha.balance] with z hbalance
  exact acceptedFlowDensity_le_referenceMH_at z.1 z.2
    (ha.le_one z.1 z.2) (ha.le_one z.2 z.1) hbalance

/-- **Reference-state MH accepted-flow maximality.**  Any admissible balanced
acceptance rule accepts no more flow than Metropolis--Hastings. -/
theorem referenceMH_acceptedFlow_maximal
    {μ : Measure X} {Q : Kernel X X}
    {h : X → ℝ≥0∞} {a : X → X → ℝ≥0∞}
    (ha : AdmissibleAcceptance μ Q h a) :
    acceptedFlow μ Q h a ≤ referenceMHAcceptedFlow μ Q h := by
  exact withDensity_mono (acceptedFlowDensity_le_referenceMH ha)

/-- Full reference-state interpretation: both flows are reversible and the
Metropolis--Hastings one is the largest accepted flow. -/
theorem referenceMH_largest_reversibleAcceptedFlow
    {μ : Measure X} {Q : Kernel X X}
    {h : X → ℝ≥0∞} {a : X → X → ℝ≥0∞}
    (hrev : ReferenceReversible μ Q) (hh : Measurable h)
    (ha : AdmissibleAcceptance μ Q h a) :
    FlowSymmetric (acceptedFlow μ Q h a) ∧
      FlowSymmetric (referenceMHAcceptedFlow μ Q h) ∧
      acceptedFlow μ Q h a ≤ referenceMHAcceptedFlow μ Q h := by
  exact ⟨acceptedFlow_symmetric hrev hh ha,
    referenceMHAcceptedFlow_symmetric hrev hh,
    referenceMH_acceptedFlow_maximal ha⟩

end

end LeanMetroGeneral
