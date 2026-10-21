module

public import RequestProject.PPWProfile

/-!
# Tools for the construction of the Ashbaugh–Benguria profile

* a smooth function `smoothFloor c` equal to the identity on `[c, ∞)` and bounded below by
  `c/2 > 0`;
* analyticity of `dslope` of an entire function;
* the sign of the derivative of a Bessel series at its first zero;
* extension of monotonicity from an open interval to its closure, for continuous functions.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology

noncomputable section

namespace FourthRatio

/-- A smooth function equal to `t` for `t ≥ c` and `≥ c/2` everywhere (for `c > 0`). -/
def smoothFloor (c t : ℝ) : ℝ :=
  t * Real.smoothTransition ((t - c / 2) / (c / 2)) +
    c / 2 * (1 - Real.smoothTransition ((t - c / 2) / (c / 2)))

lemma contDiff_smoothFloor (c : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (smoothFloor c) := by
  have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => Real.smoothTransition ((t - c / 2) / (c / 2))) :=
    Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)
  exact (contDiff_id.mul h).add (contDiff_const.mul (contDiff_const.sub h))

lemma smoothFloor_of_le {c t : ℝ} (hc : 0 < c) (h : c ≤ t) : smoothFloor c t = t := by
  have : 1 ≤ (t - c / 2) / (c / 2) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  rw [smoothFloor, Real.smoothTransition.one_of_one_le this]; ring

lemma smoothFloor_ge {c : ℝ} (hc : 0 < c) (t : ℝ) : c / 2 ≤ smoothFloor c t := by
  set θ := Real.smoothTransition ((t - c / 2) / (c / 2))
  have h0 : 0 ≤ θ := Real.smoothTransition.nonneg _
  have h1 : θ ≤ 1 := Real.smoothTransition.le_one _
  have e : smoothFloor c t = t * θ + c / 2 * (1 - θ) := rfl
  rw [e]
  rcases le_or_gt (c / 2) t with ht | ht
  · nlinarith [mul_le_mul_of_nonneg_right ht h0]
  · have : θ = 0 := Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity))
    rw [this]; simp

lemma smoothFloor_pos {c : ℝ} (hc : 0 < c) (t : ℝ) : 0 < smoothFloor c t :=
  lt_of_lt_of_le (by positivity) (smoothFloor_ge hc t)

/-- `dslope` of an entire function is entire. -/
lemma analyticOnNhd_dslope {f : ℝ → ℝ} (hf : AnalyticOnNhd ℝ f univ) (c : ℝ) :
    AnalyticOnNhd ℝ (dslope f c) univ := by
  intro b _
  by_cases hb : b = c
  · subst hb
    obtain ⟨p, hp⟩ := hf b trivial
    exact hp.has_fpower_series_dslope_fslope.analyticAt
  · have h1 : AnalyticAt ℝ (fun s => (s - c)⁻¹ * (f s - f c)) b :=
      ((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr hb)).mul
        ((hf b trivial).sub analyticAt_const)
    refine h1.congr ?_
    filter_upwards [(dslope_eventuallyEq_slope_of_ne f hb)] with s hs
    rw [hs, slope_def_field]
    field_simp

lemma contDiff_dslope {f : ℝ → ℝ} (hf : AnalyticOnNhd ℝ f univ) (c : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dslope f c) := by
  rw [← contDiffOn_univ]
  exact (analyticOnNhd_dslope hf c).contDiffOn uniqueDiffOn_univ

/-- The derivative of a Bessel series is negative at any point before which the series is
positive. -/
lemma besselSeriesD_neg {μ b s0 : ℝ} (hμ : 0 ≤ μ) (hb : 0 < b) (hs0 : 0 < s0)
    (hpos : ∀ s ∈ Ioo 0 s0, 0 < besselSeries μ b s) : besselSeriesD μ b s0 < 0 := by
  have h := pos_of_euler hμ hs0 (fun s => -besselSeriesD μ b s) (fun s => -besselSeriesDD μ b s)
    (fun s => b / 4 * besselSeries μ b s)
    (fun s => (hasDerivAt_besselSeries_deriv hμ hb.le s).neg)
    (fun s => by
      have := besselSeries_ode hμ hb.le s
      change 2 * (2 * μ + 2) * besselSeriesD μ b s + 4 * s * besselSeriesDD μ b s =
        -b * besselSeries μ b s at this
      linear_combination (-1 / 4 : ℝ) * this)
    (fun s hs => mul_pos (by positivity) (hpos s hs))
  linarith

/-- A continuous function monotone on an open interval is monotone on its closure. -/
lemma monotoneOn_Icc_of_Ioo {g : ℝ → ℝ} (hg : Continuous g) {a b : ℝ}
    (hm : MonotoneOn g (Ioo a b)) : MonotoneOn g (Icc a b) := by
  intro x hx y hy hxy
  rcases hxy.eq_or_lt with h | h
  · rw [h]
  set m := (x + y) / 2
  have hxm : x < m := by simp only [m]; linarith
  have hmy : m < y := by simp only [m]; linarith
  have hmI : m ∈ Ioo a b := ⟨by linarith [hx.1], by linarith [hy.2]⟩
  have h1 : g x ≤ g m := by
    have ht : Tendsto g (𝓝[>] x) (𝓝 (g x)) := hg.continuousAt.continuousWithinAt.tendsto
    refine le_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsGT hxm] with u hu
    exact hm ⟨by linarith [hx.1, hu.1], by linarith [hu.2, hmI.2]⟩ hmI hu.2.le
  have h2 : g m ≤ g y := by
    have ht : Tendsto g (𝓝[<] y) (𝓝 (g y)) := hg.continuousAt.continuousWithinAt.tendsto
    refine ge_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsLT hmy] with u hu
    exact hm hmI ⟨by linarith [hu.1, hmI.1], by linarith [hy.2, hu.2]⟩ hu.1.le
  exact h1.trans h2

/-- A continuous function antitone on an open interval is antitone on its closure. -/
lemma antitoneOn_Icc_of_Ioo {g : ℝ → ℝ} (hg : Continuous g) {a b : ℝ}
    (hm : AntitoneOn g (Ioo a b)) : AntitoneOn g (Icc a b) := by
  have := monotoneOn_Icc_of_Ioo hg.neg (a := a) (b := b) (fun x hx y hy hxy => by
    simp only [Pi.neg_apply, neg_le_neg_iff]; exact hm hx hy hxy)
  intro x hx y hy hxy
  have := this hx hy hxy
  simpa using this

end FourthRatio

end
