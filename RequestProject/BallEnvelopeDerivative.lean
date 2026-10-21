module

public import RequestProject.BallEnvelope
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-! # The first radius variation of the upper ball envelope -/

@[expose] public section

open Set Metric Filter Topology
open scoped NNReal RealInnerProductSpace

noncomputable section

namespace FourthRatio

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The Frechet remainder is uniformly small on sufficiently small balls. -/
lemma eventually_ball_gradient_remainder {f : E → ℝ} {g x : E}
    (hg : HasGradientAt f g x) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ h ∈ closedBall (0 : E) r,
      |f (x + h) - f x - ⟪g, h⟫| ≤ δ * r := by
  have hlittle := (hasFDerivAt_iff_isLittleO_nhds_zero.mp hg.hasFDerivAt).bound hδ
  have hb : ∀ᶠ h in 𝓝 (0 : E), |f (x + h) - f x - ⟪g, h⟫| ≤ δ * ‖h‖ := by
    simpa only [Real.norm_eq_abs, InnerProductSpace.toDual_apply_apply] using hlittle
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp hb
  filter_upwards [Ioo_mem_nhdsGT hε] with r hr
  intro h hh
  have hn : ‖h‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hh
  have hnear : dist h (0 : E) < ε := by
    simpa only [dist_zero_right] using hn.trans_lt hr.2
  exact (he hnear).trans (mul_le_mul_of_nonneg_left hn hδ.le)

/-- Uniform first-order bounds for the upper envelope. -/
lemma eventually_upperBallEnvelope_bounds {f : E → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {g x : E} (hg : HasGradientAt f g x) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      f x + (‖g‖ - δ) * r ≤ upperBallEnvelope f r x ∧
        upperBallEnvelope f r x ≤ f x + (‖g‖ + δ) * r := by
  filter_upwards [eventually_ball_gradient_remainder hg hδ,
    self_mem_nhdsWithin] with r hrem hr
  have hr0 : 0 < r := hr
  have hup : upperBallEnvelope f r x ≤ f x + (‖g‖ + δ) * r := by
    apply csSup_le (upperBallValues_nonempty f x hr0.le)
    rintro y ⟨h, hh, rfl⟩
    change f (x + h) ≤ f x + (‖g‖ + δ) * r
    have hn : ‖h‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hh
    have hi : ⟪g, h⟫ ≤ ‖g‖ * r :=
      (real_inner_le_norm g h).trans (mul_le_mul_of_nonneg_left hn (norm_nonneg g))
    have he := (abs_le.mp (hrem h hh)).2
    nlinarith
  refine ⟨?_, hup⟩
  by_cases hg0 : g = 0
  · subst g
    have hl := self_le_upperBallEnvelope hf x hr0.le
    simp only [norm_zero] at *
    nlinarith [mul_nonneg hδ.le hr0.le]
  · have hgn : 0 < ‖g‖ := norm_pos_iff.mpr hg0
    let v : E := ‖g‖⁻¹ • g
    have hvn : ‖v‖ = 1 := by
      dsimp only [v]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hgn), inv_mul_cancel₀ hgn.ne']
    have hvi : ⟪g, v⟫ = ‖g‖ := by
      dsimp only [v]
      rw [inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp [hgn.ne']
    have hvr : r • v ∈ closedBall (0 : E) r := by
      simpa only [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos hr0, hvn, mul_one] using (le_rfl : r ≤ r)
    have he := (abs_le.mp (hrem (r • v) hvr)).1
    rw [inner_smul_right, hvi] at he
    have hl := le_upperBallEnvelope hf x hvr
    nlinarith

/-- The first variation in ball radius is the norm of the gradient. -/
theorem tendsto_upperBallEnvelope_difference_quotient {f : E → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {g x : E} (hg : HasGradientAt f g x) :
    Tendsto (fun r : ℝ => (upperBallEnvelope f r x - f x) / r)
      (𝓝[>] 0) (𝓝 ‖g‖) := by
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  filter_upwards [eventually_upperBallEnvelope_bounds hf hg (half_pos hδ),
    self_mem_nhdsWithin] with r hb hr
  have hr0 : 0 < r := hr
  have hlo : ‖g‖ - δ / 2 ≤ (upperBallEnvelope f r x - f x) / r :=
    (le_div_iff₀ hr0).mpr (by nlinarith [hb.1])
  have hup : (upperBallEnvelope f r x - f x) / r ≤ ‖g‖ + δ / 2 :=
    (div_le_iff₀ hr0).mpr (by nlinarith [hb.2])
  change |(upperBallEnvelope f r x - f x) / r - ‖g‖| < δ
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

end FourthRatio

end
