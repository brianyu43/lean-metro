import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

namespace LeanMetroGeneral

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

variable {X : Type*} [MeasurableSpace X]

/-- The joint measure `π(dx) Q(x,dy)` of a state and its proposal. -/
noncomputable def proposalFlow (π : Measure X) (Q : Kernel X X) :
    Measure (X × X) :=
  π ⊗ₘ Q

/-- Reverse a joint flow by swapping its source and destination coordinates. -/
noncomputable def reverseFlow (ν : Measure (X × X)) : Measure (X × X) :=
  ν.map Prod.swap

/-- A joint flow is symmetric when reversing its two coordinates changes
nothing. -/
def FlowSymmetric (ν : Measure (X × X)) : Prop :=
  reverseFlow ν = ν

@[simp]
theorem reverseFlow_reverseFlow (ν : Measure (X × X)) :
    reverseFlow (reverseFlow ν) = ν := by
  rw [reverseFlow, reverseFlow, Measure.map_map measurable_swap measurable_swap]
  simp only [Prod.swap_swap_eq, Measure.map_id]

theorem reverseFlow_mono {ν ρ : Measure (X × X)} (h : ν ≤ ρ) :
    reverseFlow ν ≤ reverseFlow ρ := by
  exact Measure.map_mono h measurable_swap

/-- Reversing a measure with density transports the density through the swap.
This is the change-of-variables lemma used throughout the accepted-flow layer. -/
theorem reverseFlow_withDensity
    (ν : Measure (X × X)) (f : (X × X) → ℝ≥0∞) (hf : Measurable f) :
    reverseFlow (ν.withDensity f) =
      (reverseFlow ν).withDensity (f ∘ Prod.swap) := by
  ext s hs
  rw [reverseFlow, Measure.map_apply measurable_swap hs]
  rw [withDensity_apply _ (measurable_swap hs)]
  rw [withDensity_apply _ hs]
  rw [reverseFlow, setLIntegral_map hs (hf.comp measurable_swap) measurable_swap]
  simp only [Function.comp_apply, Prod.swap_swap]

theorem flowSymmetric_reverseFlow {ν : Measure (X × X)}
    (hν : FlowSymmetric ν) :
    FlowSymmetric (reverseFlow ν) := by
  unfold FlowSymmetric
  rw [reverseFlow_reverseFlow]
  exact hν.symm

theorem flowSymmetric_iff_reverseFlow_eq (ν : Measure (X × X)) :
    FlowSymmetric ν ↔ reverseFlow ν = ν :=
  Iff.rfl

end LeanMetroGeneral
