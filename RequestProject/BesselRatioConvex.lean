module

public import RequestProject.BesselOrderRatio

/-!
# Convexity and slope monotonicity of the same-argument Bessel ratio

These are the geometric forms of the derivative positivity proved in
`BesselOrderRatio.lean`, used in the Ashbaugh--Benguria comparison argument.
-/

@[expose] public section

open Set

noncomputable section

namespace FourthRatio

lemma besselOrderRatio_zero (ν : ℝ) : besselOrderRatio ν 0 = 0 := by
  simp [besselOrderRatio, besselF1]

/-- The regular adjacent-order ratio is strictly convex up to its first pole. -/
theorem besselOrderRatio_strictConvexOn {ν : ℝ} (hν : 0 ≤ ν) :
    StrictConvexOn ℝ (Ico 0 (besselZero ν 1)) (besselOrderRatio ν) := by
  have hAc : Continuous (besselF ν) :=
    continuous_iff_continuousAt.mpr fun x => (hasDerivAt_besselF' hν x).continuousAt
  have hA1c : Continuous (besselF1 ν) :=
    continuous_iff_continuousAt.mpr fun x => (hasDerivAt_besselF1' hν x).continuousAt
  refine strictConvexOn_of_deriv2_pos (convex_Ico _ _)
    (hA1c.neg.continuousOn.div hAc.continuousOn (fun x hx =>
      (besselF_pos_before hν hx.1 hx.2).ne')) ?_
  intro x hx
  rw [interior_Ico] at hx
  exact (besselOrderRatio_derivatives_pos hν x hx).2

/-- Dividing the adjacent-order ratio by its argument gives a strictly
increasing function on the positive interval before the first pole. -/
theorem besselOrderRatio_div_strictMonoOn {ν : ℝ} (hν : 0 ≤ ν) :
    StrictMonoOn (fun x => besselOrderRatio ν x / x) (Ioo 0 (besselZero ν 1)) := by
  intro x hx y hy hxy
  have hc := besselOrderRatio_strictConvexOn hν
  have hzero : (0 : ℝ) ∈ Ico 0 (besselZero ν 1) := ⟨le_rfl, (besselZero_props hν).1⟩
  have ha : 0 < 1 - x / y := by
    have : x / y < 1 := (div_lt_one₀ hy.1).mpr hxy
    linarith
  have hb : 0 < x / y := div_pos hx.1 hy.1
  have h := hc.2 hzero ⟨hy.1.le, hy.2⟩ (ne_of_lt hy.1) ha hb (by ring)
  have he : (1 - x / y) • (0 : ℝ) + (x / y) • y = x := by
    simp only [smul_eq_mul, mul_zero, zero_add, div_mul_cancel₀ _ hy.1.ne']
  rw [he, besselOrderRatio_zero] at h
  simp only [smul_eq_mul, mul_zero, zero_add] at h
  have hm := mul_lt_mul_of_pos_right h hy.1
  have heq : (x / y * besselOrderRatio ν y) * y = x * besselOrderRatio ν y := by
    field_simp [hy.1.ne']
  rw [heq] at hm
  apply (div_lt_div_iff₀ hx.1 hy.1).mpr
  nlinarith

end FourthRatio

end
