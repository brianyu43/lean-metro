import LeanMetro.Balance

namespace LeanMetro

/-- Metropolis acceptance probability for positive real-valued target weights. -/
noncomputable def mhAcceptance {ι : Type*} (w : ι → ℝ) (x y : ι) : ℝ :=
  min 1 (w y / w x)

/-- A symmetric proposal lifts the scalar MH identity to off-diagonal detailed balance. -/
theorem mh_balance_symmetric_proposal
    {ι : Type*}
    (w : ι → ℝ)
    (q : ι → ι → ℝ)
    {x y : ι}
    (hx : 0 < w x)
    (hy : 0 < w y)
    (hq : q x y = q y x) :
    w x * (q x y * mhAcceptance w x y) =
      w y * (q y x * mhAcceptance w y x) := by
  unfold mhAcceptance
  rw [hq]
  calc
    w x * (q y x * min 1 (w y / w x)) =
        q y x * (w x * min 1 (w y / w x)) := by ring
    _ = q y x * (w y * min 1 (w x / w y)) := by
      rw [mh_balance_scalar hx hy]
    _ = w y * (q y x * min 1 (w x / w y)) := by ring

end LeanMetro
