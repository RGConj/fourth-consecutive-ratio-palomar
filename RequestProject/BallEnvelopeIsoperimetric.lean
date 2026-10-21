module

public import RequestProject.BallEnvelope
public import RequestProject.Isoperimetric
public import Mathlib.Topology.Algebra.Support

/-!
# The sharp level-volume bound for upper ball envelopes

This applies the verified thickening isoperimetric inequality to actual
positive superlevels of a compactly supported Lipschitz function.
-/

@[expose] public section

open Set Metric MeasureTheory
open scoped NNReal ENNReal Pointwise

noncomputable section

namespace FourthRatio

lemma upperBallEnvelope_level_isoperimetric_nonempty {d : ℕ}
    {f : EuclideanSpace ℝ (Fin (d + 1)) → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hc : HasCompactSupport f) {r t : ℝ}
    (hr : 0 < r) (ht : 0 < t) (hne : ({x | t < f x} : Set _).Nonempty) :
    (d + 1) * volume {x | t < f x} ^ (1 - ((d : ℝ) + 1)⁻¹) *
      volume (ball (0 : EuclideanSpace ℝ (Fin (d + 1))) 1) ^ ((d : ℝ) + 1)⁻¹ ≤
        (volume {x | t < upperBallEnvelope f r x} - volume {x | t < f x}) /
          ENNReal.ofReal r := by
  have hm : MeasurableSet {x | t < f x} := measurableSet_lt measurable_const hf.continuous.measurable
  have hs : {x | t < f x} ⊆ tsupport f := by
    intro x hx
    have hfx : t < f x := hx
    exact subset_tsupport f (ne_of_gt (ht.trans hfx))
  have hfin : volume {x | t < f x} ≠ ⊤ :=
    ne_top_of_le_ne_top hc.isCompact.measure_ne_top (measure_mono hs)
  have hi := isoperimetric_inequality hr hne hm hfin
  apply hi.trans
  have hv : volume ({x | t < f x} + ball 0 r) ≤
      volume {x | t < upperBallEnvelope f r x} :=
    measure_mono (superlevel_add_ball_subset_upperBallEnvelope hf r t)
  gcongr

/-- In dimension at least two the level-volume inequality also covers empty
positive superlevels, with their zero contribution. -/
theorem upperBallEnvelope_level_isoperimetric {N : ℕ} (hN : 2 ≤ N)
    {f : EuclideanSpace ℝ (Fin N) → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hc : HasCompactSupport f) {r t : ℝ}
    (hr : 0 < r) (ht : 0 < t) :
    (N : ℝ≥0∞) * volume {x | t < f x} ^ (1 - (N : ℝ)⁻¹) *
      volume (ball (0 : EuclideanSpace ℝ (Fin N)) 1) ^ (N : ℝ)⁻¹ ≤
        (volume {x | t < upperBallEnvelope f r x} - volume {x | t < f x}) /
          ENNReal.ofReal r := by
  by_cases hne : ({x | t < f x} : Set _).Nonempty
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
    simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using
      upperBallEnvelope_level_isoperimetric_nonempty hf hc hr ht hne
  · have he : ({x | t < f x} : Set _) = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have hp : 0 < 1 - (N : ℝ)⁻¹ := by
      have hi : (1 : ℝ) / N < 1 := (div_lt_one (by linarith : 0 < (N : ℝ))).mpr (by linarith)
      simpa only [one_div] using sub_pos.mpr hi
    rw [he, measure_empty, ENNReal.zero_rpow_of_pos hp, mul_zero, zero_mul]
    exact bot_le

end FourthRatio

end
