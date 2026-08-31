import LeanMetroGeneral.JointFlow
import Mathlib.Probability.Kernel.Composition.MeasureComp

namespace LeanMetroGeneral

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

variable {X : Type*} [MeasurableSpace X]

/-- A kernel is reversible for `π` when its joint state-transition flow is
invariant under swapping the two coordinates. -/
def ReversibleFor (π : Measure X) (P : Kernel X X) : Prop :=
  FlowSymmetric (proposalFlow π P)

/-- A measure is stationary for a kernel when one kernel step preserves it. -/
def StationaryFor (π : Measure X) (P : Kernel X X) : Prop :=
  P ∘ₘ π = π

/-- Measure-level detailed balance implies stationarity. -/
theorem ReversibleFor.stationaryFor
    (π : Measure X) [SFinite π]
    (P : Kernel X X) [IsMarkovKernel P]
    (hrev : ReversibleFor π P) :
    StationaryFor π P := by
  unfold StationaryFor
  calc
    P ∘ₘ π = (proposalFlow π P).snd := by
      rw [proposalFlow, Measure.snd_compProd]
    _ = (reverseFlow (proposalFlow π P)).fst := by
      simp only [reverseFlow, Measure.fst_map_swap]
    _ = (proposalFlow π P).fst := by
      exact congrArg Measure.fst hrev
    _ = π := by
      rw [proposalFlow, Measure.fst_compProd]

theorem reversibleFor_implies_stationaryFor
    (π : Measure X) [SFinite π]
    (P : Kernel X X) [IsMarkovKernel P]
    (hrev : ReversibleFor π P) :
    StationaryFor π P :=
  hrev.stationaryFor π P

end LeanMetroGeneral
