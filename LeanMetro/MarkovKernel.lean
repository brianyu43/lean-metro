import LeanMetro.AcceptanceRule

namespace LeanMetro

/-- A finite real-valued Markov kernel: every entry is nonnegative and every
row sums to one. -/
structure FiniteKernel (ι : Type*) [Fintype ι] where
  prob : ι → ι → ℝ
  nonneg : ∀ x y, 0 ≤ prob x y
  row_sum : ∀ x, ∑ y, prob x y = 1

namespace FiniteKernel

variable {ι : Type*} [Fintype ι]

/-- Pointwise detailed balance of `P` with respect to mass function `π`. -/
def ReversibleFor (P : FiniteKernel ι) (π : ι → ℝ) : Prop :=
  ∀ x y, π x * P.prob x y = π y * P.prob y x

/-- Invariance of mass function `π` under one step of `P`. -/
def StationaryFor (P : FiniteKernel ι) (π : ι → ℝ) : Prop :=
  ∀ y, ∑ x, π x * P.prob x y = π y

theorem ReversibleFor.stationary
    {P : FiniteKernel ι} {π : ι → ℝ}
    (hrev : P.ReversibleFor π) : P.StationaryFor π := by
  intro y
  exact stationary_of_detailed_balance π P.prob P.row_sum hrev y

end FiniteKernel

/-- A finite Markov kernel bundled with a detailed-balance proof for `π`. -/
structure ReversibleKernel
    (ι : Type*) [Fintype ι] (π : ι → ℝ)
    extends FiniteKernel ι where
  reversible : toFiniteKernel.ReversibleFor π

namespace ReversibleKernel

variable {ι : Type*} [Fintype ι] {π : ι → ℝ}

theorem stationary (P : ReversibleKernel ι π) :
    P.toFiniteKernel.StationaryFor π :=
  P.reversible.stationary

end ReversibleKernel

/-- `P₁` Peskun-dominates `P₂` when every off-diagonal transition probability
of `P₁` is at least the corresponding probability of `P₂`. -/
def PeskunDominates
    {ι : Type*} [Fintype ι] (P₁ P₂ : FiniteKernel ι) : Prop :=
  ∀ ⦃x y : ι⦄, x ≠ y → P₂.prob x y ≤ P₁.prob x y

theorem peskunDominates_refl
    {ι : Type*} [Fintype ι] (P : FiniteKernel ι) :
    PeskunDominates P P := by
  intro x y _
  exact le_rfl

theorem peskunDominates_trans
    {ι : Type*} [Fintype ι] {P₁ P₂ P₃ : FiniteKernel ι}
    (h₁₂ : PeskunDominates P₁ P₂)
    (h₂₃ : PeskunDominates P₂ P₃) :
    PeskunDominates P₁ P₃ := by
  intro x y hxy
  exact (h₂₃ hxy).trans (h₁₂ hxy)

/-- Bundle a generic accept/reject transition as a finite Markov kernel. -/
noncomputable def acceptRejectKernel
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q a : ι → ι → ℝ)
    (hq_nonneg : ∀ x y, 0 ≤ q x y)
    (hq_row_sum : ∀ x, ∑ y, q x y = 1)
    (ha_nonneg : ∀ x y, 0 ≤ a x y)
    (ha_le_one : ∀ x y, a x y ≤ 1) :
    FiniteKernel ι where
  prob := acceptRejectTransition q a
  nonneg := acceptRejectTransition_nonneg
    q a hq_nonneg hq_row_sum ha_nonneg ha_le_one
  row_sum := acceptRejectTransition_row_sum q a

/-- A generic admissible accept/reject rule bundled as a reversible kernel. -/
noncomputable def admissibleAcceptRejectReversibleKernel
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (q a : ι → ι → ℝ)
    (hq_nonneg : ∀ x y, 0 ≤ q x y)
    (hq_row_sum : ∀ x, ∑ y, q x y = 1)
    (ha : AdmissibleAcceptance w q a) :
    ReversibleKernel ι (normalizedWeight w) where
  toFiniteKernel := acceptRejectKernel
    q a hq_nonneg hq_row_sum ha.nonneg ha.le_one
  reversible := normalizedWeight_acceptRejectTransition_detailed_balance
    w q a ha

/-- Bundle the already verified asymmetric MH transition as a finite kernel. -/
noncomputable def metropolisHastingsKernel
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (q : ι → ι → ℝ)
    (hw : ∀ x, 0 < w x)
    (hq_nonneg : ∀ x y, 0 ≤ q x y)
    (hq_row_sum : ∀ x, ∑ y, q x y = 1) :
    FiniteKernel ι where
  prob := mhAsymmetricTransition w q
  nonneg := mhAsymmetricTransition_nonneg
    w q hw hq_nonneg hq_row_sum
  row_sum := mhAsymmetricTransition_row_sum w q

/-- The MH finite kernel bundled with its reversibility proof. -/
noncomputable def metropolisHastingsReversibleKernel
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (q : ι → ι → ℝ)
    (hw : ∀ x, 0 < w x)
    (hq_nonneg : ∀ x y, 0 ≤ q x y)
    (hq_row_sum : ∀ x, ∑ y, q x y = 1) :
    ReversibleKernel ι (normalizedWeight w) where
  toFiniteKernel := metropolisHastingsKernel
    w q hw hq_nonneg hq_row_sum
  reversible := normalizedWeight_mhAsymmetricTransition_detailed_balance
    w q hw hq_nonneg

theorem metropolisHastingsKernel_stationary
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (q : ι → ι → ℝ)
    (hw : ∀ x, 0 < w x)
    (hq_nonneg : ∀ x y, 0 ≤ q x y)
    (hq_row_sum : ∀ x, ∑ y, q x y = 1) :
    (metropolisHastingsKernel w q hw hq_nonneg hq_row_sum).StationaryFor
      (normalizedWeight w) :=
  (metropolisHastingsReversibleKernel
    w q hw hq_nonneg hq_row_sum).stationary

/-- Structured Peskun maximality: with a fixed target and proposal, the MH
kernel dominates the kernel from every admissible acceptance rule. -/
theorem metropolisHastingsKernel_peskunDominates
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (q a : ι → ι → ℝ)
    (hw : ∀ x, 0 < w x)
    (hq_nonneg : ∀ x y, 0 ≤ q x y)
    (hq_row_sum : ∀ x, ∑ y, q x y = 1)
    (ha : AdmissibleAcceptance w q a) :
    PeskunDominates
      (metropolisHastingsKernel w q hw hq_nonneg hq_row_sum)
      (acceptRejectKernel q a hq_nonneg hq_row_sum ha.nonneg ha.le_one) := by
  intro x y hxy
  exact mhTransition_offDiagonal_dominates
    w q a hw hq_nonneg ha hxy

end LeanMetro
