module

public import Mathlib

/-!
# One-dimensional radial integrals for the ball–annulus lemma

The strict inequality `∫ ρ² r^{d-2} < R⁻² ∫ ρ² rᵈ` on the annulus `R < r < R'` used in the proof
of the ball–annulus lemma ("`r^{-2} < R^{-2}` on the support of the radial factor").
-/

@[expose] public section

open MeasureTheory Filter Topology

noncomputable section

namespace FourthRatio

lemma integral_pos_of_nonneg_of_pos_near {f : ℝ → ℝ} {a b r0 : ℝ}
    (hfi : IntervalIntegrable f volume a b) (hnn : ∀ r ∈ Set.Ioc a b, 0 ≤ f r)
    (hr0 : r0 ∈ Set.Ioo a b) (hc : ContinuousAt f r0) (hpos : 0 < f r0) :
    0 < ∫ r in a..b, f r := by
  have hab : a < b := hr0.1.trans hr0.2
  rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae' _ hfi]
  · refine ⟨hab, ?_⟩
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (hc.eventually (lt_mem_nhds hpos))
    set lo := max a (r0 - ε)
    set hi := min b (r0 + ε)
    have hlohi : lo < hi := by
      simp only [lo, hi, max_lt_iff, lt_min_iff]
      exact ⟨⟨hab, by linarith [hr0.2]⟩, by linarith [hr0.1], by linarith⟩
    have hsub : Set.Ioo lo hi ⊆ Function.support f ∩ Set.Ioc a b := by
      intro r hr
      simp only [lo, hi, Set.mem_Ioo, max_lt_iff, lt_min_iff] at hr
      refine ⟨(hball ?_).ne', hr.1.1, hr.2.1.le⟩
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith
    refine lt_of_lt_of_le ?_ (measure_mono hsub)
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (by linarith)
  · rw [Set.uIoc_of_le hab.le]
    exact (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall hnn)

/-- Annulus inequality: `R² ∫_R^{R'} ρ² r^{d-2} < ∫_R^{R'} ρ² rᵈ`, and the right side is
positive. -/
lemma annulus_integral_ineq {ρ : ℝ → ℝ} {R R' d : ℝ} (hR : 0 < R) (hRR : R < R')
    (hρ : ContinuousOn ρ (Set.Icc R R')) (hρ0 : ∀ r ∈ Set.Ioo R R', ρ r ≠ 0) :
    0 < ∫ r in R..R', ρ r ^ 2 * r ^ d ∧
      R ^ 2 * (∫ r in R..R', ρ r ^ 2 * r ^ (d - 2)) < ∫ r in R..R', ρ r ^ 2 * r ^ d := by
  have hpow : ∀ e : ℝ, ContinuousOn (fun r : ℝ => r ^ e) (Set.Icc R R') := fun e =>
    fun r hr => (Real.continuousAt_rpow_const r e (Or.inl (by linarith [hr.1]))).continuousWithinAt
  have hi1 : IntervalIntegrable (fun r => ρ r ^ 2 * r ^ d) volume R R' :=
    ((hρ.pow 2).mul (hpow d)).intervalIntegrable_of_Icc hRR.le
  have hi2 : IntervalIntegrable (fun r => ρ r ^ 2 * r ^ (d - 2)) volume R R' :=
    ((hρ.pow 2).mul (hpow (d - 2))).intervalIntegrable_of_Icc hRR.le
  constructor
  · refine intervalIntegral.intervalIntegral_pos_of_pos_on hi1 (fun r hr => ?_) hRR
    have := hρ0 r hr
    have : 0 < r := by linarith [hr.1]
    positivity
  · have key : 0 < ∫ r in R..R', (ρ r ^ 2 * r ^ d - R ^ 2 * (ρ r ^ 2 * r ^ (d - 2))) := by
      refine intervalIntegral.intervalIntegral_pos_of_pos_on (hi1.sub (hi2.const_mul _))
        (fun r hr => ?_) hRR
      have hr0 : 0 < r := by linarith [hr.1]
      have h1 : r ^ d = r ^ (d - 2) * r ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_add hr0]; norm_num
      have hρr := hρ0 r hr
      have h2 : 0 < r ^ (d - 2) := Real.rpow_pos_of_pos hr0 _
      have h3 : R ^ 2 < r ^ 2 := by nlinarith [hr.1]
      rw [h1]
      have : 0 < ρ r ^ 2 := by positivity
      nlinarith [mul_pos this h2]
    rw [intervalIntegral.integral_sub hi1 (hi2.const_mul _),
      intervalIntegral.integral_const_mul] at key
    linarith

end FourthRatio

end
