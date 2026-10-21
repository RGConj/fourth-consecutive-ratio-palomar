module

public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Tactic

/-!
# The upper envelope over a translating ball

This is the finite, continuous envelope used to differentiate the
Brunn--Minkowski thickening inequality for smooth test functions.
-/

@[expose] public section

open Set Metric
open scoped Pointwise NNReal

noncomputable section

namespace FourthRatio

variable {E : Type*} [NormedAddCommGroup E]

/-- The supremum of f over the closed radius-r ball translated to x. -/
def upperBallEnvelope (f : E → ℝ) (r : ℝ) (x : E) : ℝ :=
  sSup ((fun h => f (x + h)) '' closedBall 0 r)

lemma translate_value_le_of_lipschitz {f : E → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (x : E) {h : E} {r : ℝ} (hh : h ∈ closedBall 0 r) :
    f (x + h) ≤ f x + (K : ℝ) * r := by
  have hn : ‖h‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hh
  have hd : |f (x + h) - f x| ≤ (K : ℝ) * ‖h‖ := by
    simpa only [Real.dist_eq, dist_eq_norm, add_sub_cancel_left, Real.norm_eq_abs] using hf.dist_le_mul (x + h) x
  have hb := hd.trans (mul_le_mul_of_nonneg_left hn K.coe_nonneg)
  linarith [le_abs_self (f (x + h) - f x)]

lemma upperBallValues_bddAbove {f : E → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (x : E) (r : ℝ) : BddAbove ((fun h => f (x + h)) '' closedBall 0 r) := by
  refine ⟨f x + (K : ℝ) * r, ?_⟩
  rintro y ⟨h, hh, rfl⟩
  exact translate_value_le_of_lipschitz hf x hh

lemma upperBallValues_nonempty (f : E → ℝ) (x : E) {r : ℝ} (hr : 0 ≤ r) :
    ((fun h => f (x + h)) '' closedBall 0 r).Nonempty := by
  exact (nonempty_closedBall.mpr hr).image _

lemma le_upperBallEnvelope {f : E → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (x : E) {h : E} {r : ℝ} (hh : h ∈ closedBall 0 r) :
    f (x + h) ≤ upperBallEnvelope f r x :=
  le_csSup (upperBallValues_bddAbove hf x r) ⟨h, hh, rfl⟩

lemma self_le_upperBallEnvelope {f : E → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (x : E) {r : ℝ} (hr : 0 ≤ r) : f x ≤ upperBallEnvelope f r x := by
  simpa only [add_zero] using le_upperBallEnvelope hf x (mem_closedBall_self hr)

lemma upperBallEnvelope_le {f : E → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (x : E) {r : ℝ} (hr : 0 ≤ r) : upperBallEnvelope f r x ≤ f x + (K : ℝ) * r := by
  apply csSup_le (upperBallValues_nonempty f x hr)
  rintro y ⟨h, hh, rfl⟩
  exact translate_value_le_of_lipschitz hf x hh

lemma upperBallEnvelope_le_add_dist {f : E → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {r : ℝ} (hr : 0 ≤ r) (x y : E) :
    upperBallEnvelope f r x ≤ upperBallEnvelope f r y + (K : ℝ) * dist x y := by
  apply csSup_le (upperBallValues_nonempty f x hr)
  rintro z ⟨h, hh, rfl⟩
  have hd : |f (x + h) - f (y + h)| ≤ (K : ℝ) * dist x y := by
    simpa only [Real.dist_eq, dist_add_right] using hf.dist_le_mul (x + h) (y + h)
  have hy := le_upperBallEnvelope hf y hh
  linarith [le_abs_self (f (x + h) - f (y + h))]

/-- Taking an upper ball envelope preserves the Lipschitz constant. -/
theorem upperBallEnvelope_lipschitz {f : E → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {r : ℝ} (hr : 0 ≤ r) : LipschitzWith K (upperBallEnvelope f r) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, abs_le]
  have hxy := upperBallEnvelope_le_add_dist hf hr x y
  have hyx := upperBallEnvelope_le_add_dist hf hr y x
  rw [dist_comm y x] at hyx
  constructor <;> linarith

/-- Thickening a positive superlevel set is contained in the corresponding
superlevel set of the upper envelope. -/
theorem superlevel_add_ball_subset_upperBallEnvelope {f : E → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (r t : ℝ) :
    {x | t < f x} + ball 0 r ⊆ {x | t < upperBallEnvelope f r x} := by
  rintro z ⟨a, ha, b, hb, rfl⟩
  have hbn : ‖b‖ < r := by simpa only [mem_ball, dist_zero_right] using hb
  have hnb : -b ∈ closedBall (0 : E) r := by
    simpa only [mem_closedBall, dist_zero_right, norm_neg] using hbn.le
  have hv := le_upperBallEnvelope hf (a + b) hnb
  simp only [add_neg_cancel_right] at hv
  exact ha.trans_le hv

end FourthRatio

end
