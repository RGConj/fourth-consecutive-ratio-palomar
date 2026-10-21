module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! # The Riccati equation for an adjacent-dimensional quotient -/

@[expose] public section

namespace FourthRatio

lemma quotient_log_slope_deriv {A A1 A2 C C1 C2 : ℝ → ℝ} {a b d t : ℝ}
    (ht : t ≠ 0) (hAne : A t ≠ 0) (hCne : C t ≠ 0)
    (hA : HasDerivAt A (A1 t) t) (hA1 : HasDerivAt A1 (A2 t) t)
    (hC : HasDerivAt C (C1 t) t) (hC1 : HasDerivAt C1 (C2 t) t)
    (hodeA : t * A2 t + d * A1 t + a * t * A t = 0)
    (hodeC : t * C2 t + (d + 2) * C1 t + b * t * C t = 0) :
    let q : ℝ → ℝ := fun s => 1 + s * (C1 s / C s - A1 s / A s)
    HasDerivAt q ((a - b) * t + (1 - q t) * (q t + d) / t -
      2 * q t * A1 t / A t) t := by
  dsimp only
  have h := ((hasDerivAt_id t).mul
    ((hC1.div hC hCne).sub (hA1.div hA hAne))).const_add 1
  have hA2 : A2 t = -(d * A1 t + a * t * A t) / t := by
    field_simp
    linarith
  have hC2 : C2 t = -((d + 2) * C1 t + b * t * C t) / t := by
    field_simp
    linarith
  convert h using 1 <;> (try rfl)
  simp only [id, one_mul, Pi.sub_apply, Pi.div_apply, Pi.mul_apply]
  rw [hA2, hC2]
  field_simp [ht, hAne, hCne]
  ring

end FourthRatio
