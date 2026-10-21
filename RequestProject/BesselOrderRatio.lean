module

public import RequestProject.BesselRecurrence
public import RequestProject.RadialLogConvex

/-!
# Convexity of the adjacent-order Bessel quotient at the same argument

The entire normalization extends the quotient continuously to zero. This
module addresses Lemma 2.3 in Ashbaugh--Benguria's second proof, as an auxiliary
step toward the remaining energy-weight monotonicity statement.
-/

@[expose] public section

open Set Filter Topology

noncomputable section

namespace FourthRatio

/-- The adjacent-order Bessel quotient, with its regular value at the origin. -/
def besselOrderRatio (ν x : ℝ) : ℝ := -besselF1 ν x / besselF ν x

lemma besselOrderRatio_eq {ν : ℝ} (hν : 0 ≤ ν) (x : ℝ) :
    besselOrderRatio ν x = x / 2 * besselF (ν + 1) x / besselF ν x := by
  dsimp only [besselOrderRatio]
  rw [besselF1_succ hν]
  ring

/-- The first and second derivatives of the regular Bessel quotient are
strictly positive before the first zero of its denominator. -/
theorem besselOrderRatio_derivatives_pos {ν : ℝ} (hν : 0 ≤ ν) :
    ∀ x ∈ Ioo 0 (besselZero ν 1),
      0 < deriv (besselOrderRatio ν) x ∧
        0 < deriv (deriv (besselOrderRatio ν)) x := by
  set A := besselF ν
  set A1 := besselF1 ν
  set A2 := besselF2 ν
  set y := besselOrderRatio ν
  set y1 : ℝ → ℝ := fun x => (A1 x ^ 2 - A2 x * A x) / A x ^ 2
  set d := 2 * ν + 1
  set k := besselZero ν 1
  set y2 : ℝ → ℝ := fun x => 2 * y x * y1 x - d * y1 x / x + d * y x / x ^ 2
  have hd : 0 < d := by positivity
  have hA : ∀ x, HasDerivAt A (A1 x) x := hasDerivAt_besselF' hν
  have hA1 : ∀ x, HasDerivAt A1 (A2 x) x := hasDerivAt_besselF1' hν
  have hAc : Continuous A := continuous_iff_continuousAt.mpr fun x => (hA x).continuousAt
  have hA1c : Continuous A1 := continuous_iff_continuousAt.mpr fun x => (hA1 x).continuousAt
  have hA2c : Continuous A2 := by
    have hν1 : 0 ≤ ν + 1 := by linarith
    have hC : Continuous (besselF (ν + 1)) :=
      continuous_iff_continuousAt.mpr fun x => (hasDerivAt_besselF' hν1 x).continuousAt
    have hC1 : Continuous (besselF1 (ν + 1)) :=
      continuous_iff_continuousAt.mpr fun x => (hasDerivAt_besselF1' hν1 x).continuousAt
    have heq : A2 = fun x => -(1 / 2 * besselF (ν + 1) x +
        x / 2 * besselF1 (ν + 1) x) := by
      funext x
      have heq1 : (fun t => -(t / 2 * besselF (ν + 1) t)) = A1 := by
        funext t
        dsimp only [A1]
        rw [besselF1_succ hν]
        ring
      have h := (((hasDerivAt_id x).div_const 2).mul
        (hasDerivAt_besselF' hν1 x)).neg
      change HasDerivAt (fun t => -(t / 2 * besselF (ν + 1) t)) _ x at h
      rw [heq1] at h
      simpa using (hA1 x).unique h
    rw [heq]
    exact ((continuous_const.mul hC).add ((continuous_id.div_const 2).mul hC1)).neg
  have hAp : ∀ x ∈ Ico 0 k, 0 < A x := fun x hx => besselF_pos_before hν hx.1 hx.2
  have hAne : ∀ x ∈ Ico 0 k, A x ≠ 0 := fun x hx => (hAp x hx).ne'
  have hyc : ContinuousOn y (Ico 0 k) := hA1c.neg.continuousOn.div hAc.continuousOn hAne
  have hy1c : ContinuousOn y1 (Ico 0 k) :=
    ((hA1c.pow 2).sub (hA2c.mul hAc)).continuousOn.div
      (hAc.pow 2).continuousOn (fun x hx => pow_ne_zero 2 (hAne x hx))
  have hy : ∀ x ∈ Ioo 0 k, HasDerivAt y (y1 x) x := by
    intro x hx
    have h := (hA1 x).neg.div (hA x) (hAne x ⟨hx.1.le, hx.2⟩)
    convert h using 1
    · rfl
    · dsimp only [y1, Pi.neg_apply]
      ring
  have hAd : ∀ x ∈ Ioo 0 k, HasDerivAt A (-A x * y x) x := by
    intro x hx
    apply (hA x).congr_deriv
    have hne : besselF ν x ≠ 0 := hAne x ⟨hx.1.le, hx.2⟩
    dsimp only [y, besselOrderRatio, A, A1]
    field_simp [hne]
  have hRic : ∀ x ∈ Ioo 0 k, y1 x = 1 + y x ^ 2 - d * y x / x := by
    intro x hx
    have hode := besselF_ode' hν x
    change x * A2 x + d * A1 x + x * A x = 0 at hode
    dsimp only [y1, y, besselOrderRatio]
    change (A1 x ^ 2 - A2 x * A x) / A x ^ 2 =
      1 + (-A1 x / A x) ^ 2 - d * (-A1 x / A x) / x
    field_simp [hAne x ⟨hx.1.le, hx.2⟩, hx.1.ne']
    linear_combination -A x * hode
  have hy1 : ∀ x ∈ Ioo 0 k, HasDerivAt y1 (y2 x) x := by
    intro x hx
    have h := (((hy x hx).pow 2).const_add 1).sub
      (((hy x hx).const_mul d).div (hasDerivAt_id x) hx.1.ne')
    have heq : y1 =ᶠ[𝓝 x] (fun t => 1 + y t ^ 2 - d * y t / t) := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with t ht
      exact hRic t ht
    have h := h.congr_of_eventuallyEq heq
    convert h using 1
    dsimp only [y2]
    norm_num
    field_simp [hx.1.ne']
    ring
  have hyp : ∀ x ∈ Ioo 0 k, 0 < y x := by
    intro x hx
    rw [show y x = besselOrderRatio ν x from rfl, besselOrderRatio_eq hν]
    have hF : 0 < besselF (ν + 1) x :=
      besselF_pos_before (by linarith) hx.1.le (hx.2.trans (besselZero_lt_succ hν))
    exact div_pos (mul_pos (div_pos hx.1 (by norm_num)) hF) (hAp x ⟨hx.1.le, hx.2⟩)
  obtain ⟨hp1, hp2⟩ := radial_logderiv_strict_convex hd hAc.continuousOn hyc hy1c
    hAd hy hy1 (fun _ _ => rfl) (fun x hx => hAp x ⟨hx.1.le, hx.2⟩) hyp
  intro x hx
  have hfirst : deriv y x = y1 x := (hy x hx).deriv
  have heq : deriv y =ᶠ[𝓝 x] y1 := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with t ht
    exact (hy t ht).deriv
  have hsecond : deriv (deriv y) x = y2 x :=
    ((hy1 x hx).congr_of_eventuallyEq heq).deriv
  exact ⟨by rw [hfirst]; exact hp1 x hx, by rw [hsecond]; exact hp2 x hx⟩

end FourthRatio

end
