module

public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

/-! # Logarithmic slope bounds from two profile monotonicities -/

@[expose] public section

open Set

namespace FourthRatio

/-- A positive decreasing factor whose product with the radius increases has
logarithmic slope in the unit interval. -/
lemma log_slope_bounds_of_monotone_factor {H H1 : ℝ → ℝ} {a b : ℝ}
    (ha : 0 ≤ a) (hH : ∀ t ∈ Ioo a b, HasDerivAt H (H1 t) t)
    (hp : ∀ t ∈ Ioo a b, 0 < H t)
    (hm : AntitoneOn H (Ioo a b)) (hwm : MonotoneOn (fun t => t * H t) (Ioo a b)) :
    ∀ t ∈ Ioo a b, 1 + t * (H1 t / H t) ∈ Icc 0 1 := by
  intro t ht
  have ht0 : 0 < t := ha.trans_lt ht.1
  have hH0 := hp t ht
  have hneg : H1 t ≤ 0 := by
    have h : derivWithin H (Ioo a b) t ≤ 0 := hm.derivWithin_nonpos
    rw [derivWithin_of_isOpen isOpen_Ioo ht, (hH t ht).deriv] at h
    exact h
  have hwd : HasDerivAt (fun s => s * H s) (H t + t * H1 t) t := by
    convert (hasDerivAt_id t).mul (hH t ht) using 1 <;> (try rfl)
    simp only [id, one_mul]
  have hnonneg : 0 ≤ H t + t * H1 t := by
    have h : 0 ≤ derivWithin (fun s => s * H s) (Ioo a b) t := hwm.derivWithin_nonneg
    rw [derivWithin_of_isOpen isOpen_Ioo ht, hwd.deriv] at h
    exact h
  refine ⟨?_, ?_⟩
  · have heq : 1 + t * (H1 t / H t) = (H t + t * H1 t) / H t := by
      field_simp [hH0.ne'] <;> ring
    rw [heq]
    exact div_nonneg hnonneg hH0.le
  · have h : t * (H1 t / H t) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos ht0.le (div_nonpos_of_nonpos_of_nonneg hneg hH0.le)
    linarith

end FourthRatio
