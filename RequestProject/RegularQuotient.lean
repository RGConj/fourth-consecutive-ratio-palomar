module

public import RequestProject.AnalyticSlope
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Tactic.FieldSimp

/-!
# Regular quotients through a common zero

The quotient of divided differences agrees with the original quotient away
from the common zero. Adjacent-dimensional radial ODEs determine its derivative
at the zero, giving the endpoint value of the logarithmic slope.
-/

@[expose] public section

open Set

noncomputable section

namespace FourthRatio

lemma quotient_dslope_eq {A C : ℝ → ℝ} {a t : ℝ}
    (hA : A a = 0) (hC : C a = 0) (ht : t ≠ a) :
    dslope C a t / dslope A a t = C t / A t := by
  rw [dslope_of_ne C ht, dslope_of_ne A ht]
  simp only [slope_def_field, hA, hC, sub_zero]
  exact div_div_div_cancel_right₀ (sub_ne_zero.mpr ht) _ _

/-- At the common endpoint, adjacent-dimensional ODE derivative identities
give `H' = -H` for the regular quotient `H`. -/
lemma regular_quotient_deriv_one {A A1 A2 C C1 C2 : ℝ → ℝ} {d : ℝ}
    (hAa : AnalyticOnNhd ℝ A univ) (hCa : AnalyticOnNhd ℝ C univ)
    (hA : ∀ t, HasDerivAt A (A1 t) t) (hA1 : ∀ t, HasDerivAt A1 (A2 t) t)
    (hC : ∀ t, HasDerivAt C (C1 t) t) (hC1 : ∀ t, HasDerivAt C1 (C2 t) t)
    (hAne : A1 1 ≠ 0) (hA2 : A2 1 = -d * A1 1)
    (hC2 : C2 1 = -(d + 2) * C1 1) :
    HasDerivAt (fun t => dslope C 1 t / dslope A 1 t)
      (-(dslope C 1 1 / dslope A 1 1)) 1 := by
  have hAd : dslope A 1 1 = A1 1 := by rw [dslope_same, (hA 1).deriv]
  have hCd : dslope C 1 1 = C1 1 := by rw [dslope_same, (hC 1).deriv]
  have h := (hasDerivAt_dslope_center hCa hC hC1 1).div
    (hasDerivAt_dslope_center hAa hA hA1 1) (by rw [hAd]; exact hAne)
  convert h using 1 <;> (try rfl)
  rw [hAd, hCd, hA2, hC2]
  field_simp [hAne]
  ring

/-- The regular quotient has logarithmic slope zero at the common endpoint. -/
lemma regular_quotient_log_slope_one {A A1 A2 C C1 C2 : ℝ → ℝ} {d : ℝ}
    (hAa : AnalyticOnNhd ℝ A univ) (hCa : AnalyticOnNhd ℝ C univ)
    (hA : ∀ t, HasDerivAt A (A1 t) t) (hA1 : ∀ t, HasDerivAt A1 (A2 t) t)
    (hC : ∀ t, HasDerivAt C (C1 t) t) (hC1 : ∀ t, HasDerivAt C1 (C2 t) t)
    (hAne : A1 1 ≠ 0) (hCne : C1 1 ≠ 0)
    (hA2 : A2 1 = -d * A1 1) (hC2 : C2 1 = -(d + 2) * C1 1) :
    let H : ℝ → ℝ := fun t => dslope C 1 t / dslope A 1 t
    1 + deriv H 1 / H 1 = 0 := by
  dsimp only
  have h := regular_quotient_deriv_one hAa hCa hA hA1 hC hC1 hAne hA2 hC2
  rw [h.deriv]
  have hne : dslope C 1 1 / dslope A 1 1 ≠ 0 := by
    rw [dslope_same, dslope_same, (hC 1).deriv, (hA 1).deriv]
    exact div_ne_zero hCne hAne
  rw [neg_div, div_self hne]
  norm_num

end FourthRatio

end
