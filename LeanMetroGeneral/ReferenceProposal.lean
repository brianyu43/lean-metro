import LeanMetroGeneral.Reversibility
import Mathlib.MeasureTheory.Measure.WithDensity

namespace LeanMetroGeneral

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

variable {X : Type*} [MeasurableSpace X]

/-- A proposal is reference-reversible when its joint proposal flow under the
reference measure is invariant under exchanging the current and proposed
states. -/
def ReferenceReversible (μ : Measure X) (Q : Kernel X X) : Prop :=
  ReversibleFor μ Q

/-- The density of the target-proposal flow with respect to a symmetric
reference proposal flow. -/
def targetFlowDensity (h : X → ℝ≥0∞) (z : X × X) : ℝ≥0∞ :=
  h z.1

/-- The density obtained after reversing the two coordinates. -/
def reverseTargetFlowDensity (h : X → ℝ≥0∞) (z : X × X) : ℝ≥0∞ :=
  h z.2

/-- The joint target-proposal flow `h(x) μ(dx) Q(x,dy)`.  Normalization of
`h` is deliberately not needed for accepted-flow maximality. -/
noncomputable def referenceTargetFlow
    (μ : Measure X) (Q : Kernel X X) (h : X → ℝ≥0∞) :
    Measure (X × X) :=
  (proposalFlow μ Q).withDensity (targetFlowDensity h)

theorem measurable_targetFlowDensity {h : X → ℝ≥0∞} (hh : Measurable h) :
    Measurable (targetFlowDensity h) := by
  exact hh.comp measurable_fst

theorem measurable_reverseTargetFlowDensity {h : X → ℝ≥0∞} (hh : Measurable h) :
    Measurable (reverseTargetFlowDensity h) := by
  exact hh.comp measurable_snd

/-- Under a reference-reversible proposal, reversing the target flow changes
its density from `h(x)` to `h(y)`. -/
theorem reverse_referenceTargetFlow
    {μ : Measure X} {Q : Kernel X X} {h : X → ℝ≥0∞}
    (hrev : ReferenceReversible μ Q) (hh : Measurable h) :
    reverseFlow (referenceTargetFlow μ Q h) =
      (proposalFlow μ Q).withDensity (reverseTargetFlowDensity h) := by
  rw [referenceTargetFlow]
  rw [reverseFlow_withDensity _ _ (measurable_targetFlowDensity hh)]
  rw [hrev]
  congr 1

/-- Reference reversibility is ordinary measure-level reversibility for the
reference measure. -/
theorem ReferenceReversible.stationaryFor
    (μ : Measure X) [SFinite μ]
    (Q : Kernel X X) [IsMarkovKernel Q]
    (hrev : ReferenceReversible μ Q) :
    StationaryFor μ Q :=
  ReversibleFor.stationaryFor μ Q hrev

end LeanMetroGeneral
