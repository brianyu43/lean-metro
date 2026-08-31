import LeanMetro.ProbabilisticPeskun
import LeanMetro.Irreducibility
import LeanMetro.ReversibleSampleMeanVariance

namespace LeanMetro

open ProbabilityTheory

/-- Reversibility turns the exact Poisson remainder into a telescoping sum.
Consequently the actual stationary finite-path sample-mean variances converge
to the algebraic asymptotic variance without a separate covariance-decay
assumption. -/
theorem hasSampleMeanAsymptoticVariance_of_reversible
    {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (P : FiniteKernel ι)
    (hπ_nonneg : ∀ x, 0 ≤ π x)
    (hπ_sum : ∑ x, π x = 1)
    (hrev : P.ReversibleFor π)
    (hinv : MeanZeroPoissonInvertible π P)
    (f : ι → ℝ) (hf : MeanZero π f) :
    HasSampleMeanAsymptoticVariance
      π P hπ_nonneg hπ_sum f
      (algebraicAsymptoticVariance π P hinv f hf) := by
  unfold HasSampleMeanAsymptoticVariance
  exact chainSampleMean_scaledVariance_tendsto_of_reversible
    π P hπ_nonneg hπ_sum hrev hinv f hf

/-- A normalized finite reversible irreducible kernel automatically has the
actual stationary sample-mean asymptotic variance given by its centered
Poisson formula. The inverse is constructed internally from irreducibility. -/
theorem hasSampleMeanAsymptoticVariance_of_irreducible
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (π : ι → ℝ) (P : FiniteKernel ι)
    (hπ_nonneg : ∀ x, 0 ≤ π x)
    (hπ_sum : ∑ x, π x = 1)
    (hrev : P.ReversibleFor π)
    (hirr : P.Irreducible)
    (f : ι → ℝ) (hf : MeanZero π f) :
    let hinv := meanZeroPoissonInvertible_of_irreducible
      π P hπ_sum hrev.stationary hirr
    HasSampleMeanAsymptoticVariance
      π P hπ_nonneg hπ_sum f
      (algebraicAsymptoticVariance π P hinv f hf) := by
  dsimp only
  exact hasSampleMeanAsymptoticVariance_of_reversible
    π P hπ_nonneg hπ_sum hrev
    (meanZeroPoissonInvertible_of_irreducible
      π P hπ_sum hrev.stationary hirr)
    f hf

/-- Decay-free probabilistic Peskun theorem at the Poisson-invertibility
interface. Reversibility makes the finite-horizon remainder telescope, so no
pointwise covariance-decay hypothesis is needed. -/
theorem metropolisHastings_minimizes_sampleMeanAsymptoticVariance_of_invertible
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
    HasSampleMeanAsymptoticVariance
        (normalizedWeight w)
        (metropolisHastingsKernel w q hw hq_nonneg hq_row_sum)
        (normalizedWeight_nonneg w hw)
        (normalizedWeight_sum w hw)
        f
        (algebraicAsymptoticVariance
          (normalizedWeight w)
          (metropolisHastingsKernel w q hw hq_nonneg hq_row_sum)
          hinvMH f hf) ∧
      HasSampleMeanAsymptoticVariance
        (normalizedWeight w)
        (acceptRejectKernel
          q a hq_nonneg hq_row_sum ha.nonneg ha.le_one)
        (normalizedWeight_nonneg w hw)
        (normalizedWeight_sum w hw)
        f
        (algebraicAsymptoticVariance
          (normalizedWeight w)
          (acceptRejectKernel
            q a hq_nonneg hq_row_sum ha.nonneg ha.le_one)
          hinvA f hf) ∧
      algebraicAsymptoticVariance
          (normalizedWeight w)
          (metropolisHastingsKernel w q hw hq_nonneg hq_row_sum)
          hinvMH f hf ≤
        algebraicAsymptoticVariance
          (normalizedWeight w)
          (acceptRejectKernel
            q a hq_nonneg hq_row_sum ha.nonneg ha.le_one)
          hinvA f hf := by
  constructor
  · exact hasSampleMeanAsymptoticVariance_of_reversible
      (normalizedWeight w)
      (metropolisHastingsKernel w q hw hq_nonneg hq_row_sum)
      (normalizedWeight_nonneg w hw)
      (normalizedWeight_sum w hw)
      (metropolisHastingsReversibleKernel
        w q hw hq_nonneg hq_row_sum).reversible
      hinvMH f hf
  constructor
  · exact hasSampleMeanAsymptoticVariance_of_reversible
      (normalizedWeight w)
      (acceptRejectKernel
        q a hq_nonneg hq_row_sum ha.nonneg ha.le_one)
      (normalizedWeight_nonneg w hw)
      (normalizedWeight_sum w hw)
      (admissibleAcceptRejectReversibleKernel
        w q a hq_nonneg hq_row_sum ha).reversible
      hinvA f hf
  · exact metropolisHastings_minimizes_algebraicAsymptoticVariance
      w q a hw hq_nonneg hq_row_sum ha hinvMH hinvA f hf

/-- Standard-assumption probabilistic Peskun theorem for finite state spaces.
Irreducibility and normalized stationarity construct both centered Poisson
inverses internally; reversibility then removes the former covariance-decay
assumptions by telescoping the exact finite-horizon remainder. -/
theorem metropolisHastings_minimizes_sampleMeanAsymptoticVariance_of_irreducible
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (w : ι → ℝ) (q a : ι → ι → ℝ)
    (hw : ∀ x, 0 < w x)
    (hq_nonneg : ∀ x y, 0 ≤ q x y)
    (hq_row_sum : ∀ x, ∑ y, q x y = 1)
    (ha : AdmissibleAcceptance w q a)
    (hirrMH :
      (metropolisHastingsKernel
        w q hw hq_nonneg hq_row_sum).Irreducible)
    (hirrA :
      (acceptRejectKernel
        q a hq_nonneg hq_row_sum ha.nonneg ha.le_one).Irreducible)
    (f : ι → ℝ) (hf : MeanZero (normalizedWeight w) f) :
    let hinvMH := meanZeroPoissonInvertible_of_irreducible
      (normalizedWeight w)
      (metropolisHastingsKernel w q hw hq_nonneg hq_row_sum)
      (normalizedWeight_sum w hw)
      (metropolisHastingsKernel_stationary
        w q hw hq_nonneg hq_row_sum)
      hirrMH
    let hinvA := meanZeroPoissonInvertible_of_irreducible
      (normalizedWeight w)
      (acceptRejectKernel
        q a hq_nonneg hq_row_sum ha.nonneg ha.le_one)
      (normalizedWeight_sum w hw)
      (admissibleAcceptRejectReversibleKernel
        w q a hq_nonneg hq_row_sum ha).stationary
      hirrA
    HasSampleMeanAsymptoticVariance
        (normalizedWeight w)
        (metropolisHastingsKernel w q hw hq_nonneg hq_row_sum)
        (normalizedWeight_nonneg w hw)
        (normalizedWeight_sum w hw)
        f
        (algebraicAsymptoticVariance
          (normalizedWeight w)
          (metropolisHastingsKernel w q hw hq_nonneg hq_row_sum)
          hinvMH f hf) ∧
      HasSampleMeanAsymptoticVariance
        (normalizedWeight w)
        (acceptRejectKernel
          q a hq_nonneg hq_row_sum ha.nonneg ha.le_one)
        (normalizedWeight_nonneg w hw)
        (normalizedWeight_sum w hw)
        f
        (algebraicAsymptoticVariance
          (normalizedWeight w)
          (acceptRejectKernel
            q a hq_nonneg hq_row_sum ha.nonneg ha.le_one)
          hinvA f hf) ∧
      algebraicAsymptoticVariance
          (normalizedWeight w)
          (metropolisHastingsKernel w q hw hq_nonneg hq_row_sum)
          hinvMH f hf ≤
        algebraicAsymptoticVariance
          (normalizedWeight w)
          (acceptRejectKernel
            q a hq_nonneg hq_row_sum ha.nonneg ha.le_one)
          hinvA f hf := by
  dsimp only
  let hinvMH := meanZeroPoissonInvertible_of_irreducible
    (normalizedWeight w)
    (metropolisHastingsKernel w q hw hq_nonneg hq_row_sum)
    (normalizedWeight_sum w hw)
    (metropolisHastingsKernel_stationary
      w q hw hq_nonneg hq_row_sum)
    hirrMH
  let hinvA := meanZeroPoissonInvertible_of_irreducible
    (normalizedWeight w)
    (acceptRejectKernel
      q a hq_nonneg hq_row_sum ha.nonneg ha.le_one)
    (normalizedWeight_sum w hw)
    (admissibleAcceptRejectReversibleKernel
      w q a hq_nonneg hq_row_sum ha).stationary
    hirrA
  exact metropolisHastings_minimizes_sampleMeanAsymptoticVariance_of_invertible
    w q a hw hq_nonneg hq_row_sum ha hinvMH hinvA f hf

end LeanMetro
