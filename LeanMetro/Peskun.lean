import LeanMetro.AsymptoticVariance

namespace LeanMetro

/-- Final algebraic Peskun theorem for the project: with fixed target and
proposal, MH has no larger algebraic asymptotic variance than any admissible
accept/reject rule, whenever both centered Poisson problems are invertible. -/
theorem metropolisHastings_minimizes_algebraicAsymptoticVariance
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (w : ι → ℝ) (q a : ι → ι → ℝ)
    (hw : ∀ x, 0 < w x)
    (hq_nonneg : ∀ x y, 0 ≤ q x y)
    (hq_row_sum : ∀ x, ∑ y, q x y = 1)
    (ha : AdmissibleAcceptance w q a)
    (hinvMH : MeanZeroPoissonInvertible
      (normalizedWeight w)
      (metropolisHastingsKernel w q hw hq_nonneg hq_row_sum))
    (hinvA : MeanZeroPoissonInvertible
      (normalizedWeight w)
      (acceptRejectKernel
        q a hq_nonneg hq_row_sum ha.nonneg ha.le_one))
    (f : ι → ℝ) (hf : MeanZero (normalizedWeight w) f) :
    algebraicAsymptoticVariance
        (normalizedWeight w)
        (metropolisHastingsKernel w q hw hq_nonneg hq_row_sum)
        hinvMH f hf ≤
      algebraicAsymptoticVariance
        (normalizedWeight w)
        (acceptRejectKernel
          q a hq_nonneg hq_row_sum ha.nonneg ha.le_one)
        hinvA f hf := by
  apply algebraicAsymptoticVariance_mono_of_peskunDominates
  · exact normalizedWeight_nonneg w hw
  · exact (metropolisHastingsReversibleKernel
      w q hw hq_nonneg hq_row_sum).reversible
  · exact (admissibleAcceptRejectReversibleKernel
      w q a hq_nonneg hq_row_sum ha).reversible
  · exact metropolisHastingsKernel_peskunDominates
      w q a hw hq_nonneg hq_row_sum ha

end LeanMetro
