module

public import RequestProject.RegularQuotient
public import RequestProject.BesselABFactor

/-!
# Regular endpoint extension of the Ashbaugh--Benguria slope

The common simple zeros at one are removed with divided differences. The
regular factor stays positive on the closed interval, so its logarithmic slope
is continuous there and has the genuine endpoint values one and zero.
-/

@[expose] public section

open Set

noncomputable section

namespace FourthRatio

def abDenom (ν t : ℝ) : ℝ := besselF ν (besselZero ν 1 * t)

def abDenomD (ν t : ℝ) : ℝ := besselZero ν 1 * besselF1 ν (besselZero ν 1 * t)

def abDenomDD (ν t : ℝ) : ℝ := besselZero ν 1 ^ 2 * besselF2 ν (besselZero ν 1 * t)

lemma hasDerivAt_abDenom {ν : ℝ} (hν : 0 ≤ ν) (t : ℝ) :
    HasDerivAt (abDenom ν) (abDenomD ν t) t := by
  have h := (hasDerivAt_besselF' hν (besselZero ν 1 * t)).comp t
    ((hasDerivAt_id t).const_mul (besselZero ν 1))
  convert h using 1 <;> (try rfl) <;> (try dsimp only [abDenomD, id]) <;> ring

lemma hasDerivAt_abDenomD {ν : ℝ} (hν : 0 ≤ ν) (t : ℝ) :
    HasDerivAt (abDenomD ν) (abDenomDD ν t) t := by
  have h := ((hasDerivAt_besselF1' hν (besselZero ν 1 * t)).comp t
    ((hasDerivAt_id t).const_mul (besselZero ν 1))).const_mul (besselZero ν 1)
  convert h using 1 <;> (try rfl) <;> (try dsimp only [abDenomDD, id]) <;> ring

lemma abDenom_analytic {ν : ℝ} (hν : 0 ≤ ν) : AnalyticOnNhd ℝ (abDenom ν) univ := by
  intro t _
  exact (besselF_analytic hν (besselZero ν 1 * t) trivial).comp
    (analyticAt_const.mul analyticAt_id)

lemma abDenom_one {ν : ℝ} (hν : 0 ≤ ν) : abDenom ν 1 = 0 := by
  simpa only [abDenom, mul_one] using (besselZero_props hν).2.2.1

lemma abDenom_pos {ν : ℝ} (hν : 0 ≤ ν) {t : ℝ} (ht : t ∈ Ico 0 1) :
    0 < abDenom ν t := by
  have hj := (besselZero_props hν).1
  apply besselF_pos_before hν (mul_nonneg hj.le ht.1)
  simpa only [mul_one] using mul_lt_mul_of_pos_left ht.2 hj

lemma abDenomD_one_neg {ν : ℝ} (hν : 0 ≤ ν) : abDenomD ν 1 < 0 := by
  have hj := (besselZero_props hν).1
  have hμ : 0 ≤ ν + 1 := by linarith
  have hF : 0 < besselF (ν + 1) (besselZero ν 1) :=
    besselF_pos_before hμ hj.le (besselZero_lt_succ hν)
  dsimp only [abDenomD]
  rw [mul_one, besselF1_succ hν]
  apply mul_neg_of_pos_of_neg hj
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos (div_pos hj (by norm_num))) hF

lemma abDenomDD_one {ν : ℝ} (hν : 0 ≤ ν) :
    abDenomDD ν 1 = -(2 * ν + 1) * abDenomD ν 1 := by
  have h := besselF_ode' hν (besselZero ν 1)
  rw [(besselZero_props hν).2.2.1, mul_zero, add_zero] at h
  dsimp only [abDenomDD, abDenomD]
  simp only [mul_one]
  linear_combination besselZero ν 1 * h

/-- The radial quotient with its common zero at one divided out. -/
def abRegularFactor (ν t : ℝ) : ℝ :=
  dslope (abDenom (ν + 1)) 1 t / dslope (abDenom ν) 1 t

lemma abRegularFactor_eq {ν : ℝ} (hν : 0 ≤ ν) {t : ℝ} (ht : t ≠ 1) :
    abRegularFactor ν t = abDenom (ν + 1) t / abDenom ν t := by
  exact quotient_dslope_eq (abDenom_one hν) (abDenom_one (by linarith)) ht

lemma abDenom_dslope_ne_zero {ν : ℝ} (hν : 0 ≤ ν) {t : ℝ} (ht : t ∈ Icc 0 1) :
    dslope (abDenom ν) 1 t ≠ 0 := by
  by_cases ht1 : t = 1
  · subst t
    rw [dslope_same, (hasDerivAt_abDenom hν 1).deriv]
    exact (abDenomD_one_neg hν).ne
  · rw [dslope_of_ne _ ht1, slope_def_field, abDenom_one hν, sub_zero]
    exact div_ne_zero (abDenom_pos hν ⟨ht.1, lt_of_le_of_ne ht.2 ht1⟩).ne'
      (sub_ne_zero.mpr ht1)

lemma abRegularFactor_pos {ν : ℝ} (hν : 0 ≤ ν) {t : ℝ} (ht : t ∈ Icc 0 1) :
    0 < abRegularFactor ν t := by
  have hμ : 0 ≤ ν + 1 := by linarith
  by_cases ht1 : t = 1
  · subst t
    dsimp only [abRegularFactor]
    rw [dslope_same, dslope_same, (hasDerivAt_abDenom hμ 1).deriv,
      (hasDerivAt_abDenom hν 1).deriv]
    exact div_pos_of_neg_of_neg (abDenomD_one_neg hμ) (abDenomD_one_neg hν)
  · rw [abRegularFactor_eq hν ht1]
    have ht' : t ∈ Ico 0 1 := ⟨ht.1, lt_of_le_of_ne ht.2 ht1⟩
    exact div_pos (abDenom_pos hμ ht') (abDenom_pos hν ht')

lemma abRegularFactor_analytic {ν : ℝ} (hν : 0 ≤ ν) :
    AnalyticOnNhd ℝ (abRegularFactor ν) (Icc 0 1) := by
  intro t ht
  exact (((abDenom_analytic (show 0 ≤ ν + 1 by linarith)) t trivial).dslope 1).div
    (((abDenom_analytic hν) t trivial).dslope 1) (abDenom_dslope_ne_zero hν ht)

/-- The logarithmic slope of the regular profile `t H(t)`. -/
def abLogSlope (ν t : ℝ) : ℝ :=
  1 + t * (deriv (abRegularFactor ν) t / abRegularFactor ν t)

lemma abLogSlope_continuous {ν : ℝ} (hν : 0 ≤ ν) :
    ContinuousOn (abLogSlope ν) (Icc 0 1) := by
  intro t ht
  have hH := abRegularFactor_analytic hν t ht
  exact (analyticAt_const.add (analyticAt_id.mul
    (hH.deriv.div hH (abRegularFactor_pos hν ht).ne'))).continuousAt.continuousWithinAt

lemma abLogSlope_zero (ν : ℝ) : abLogSlope ν 0 = 1 := by
  simp [abLogSlope]

lemma abLogSlope_one {ν : ℝ} (hν : 0 ≤ ν) : abLogSlope ν 1 = 0 := by
  have hμ : 0 ≤ ν + 1 := by linarith
  have hC2 : abDenomDD (ν + 1) 1 = -((2 * ν + 1) + 2) * abDenomD (ν + 1) 1 := by
    convert abDenomDD_one hμ using 1 <;> ring
  have h := regular_quotient_log_slope_one (d := 2 * ν + 1)
    (abDenom_analytic hν) (abDenom_analytic hμ)
    (hasDerivAt_abDenom hν) (hasDerivAt_abDenomD hν)
    (hasDerivAt_abDenom hμ) (hasDerivAt_abDenomD hμ)
    (abDenomD_one_neg hν).ne (abDenomD_one_neg hμ).ne (abDenomDD_one hν) hC2
  dsimp only [abLogSlope]
  rw [one_mul]
  change 1 + deriv (fun t => dslope (abDenom (ν + 1)) 1 t / dslope (abDenom ν) 1 t) 1 /
    (dslope (abDenom (ν + 1)) 1 1 / dslope (abDenom ν) 1 1) = 0
  exact h

end FourthRatio

end
