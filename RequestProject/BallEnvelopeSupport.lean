module

public import RequestProject.BallEnvelope
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Algebra.Group.Pointwise

/-! # Compact support and uniform bounds for the ball envelope -/

@[expose] public section

open Set Metric
open scoped Pointwise NNReal

noncomputable section

namespace FourthRatio

variable {E : Type*} [NormedAddCommGroup E]

lemma upperBallEnvelope_eq_zero_of_notMem_add_support {f : E → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R) {x : E}
    (hx : x ∉ tsupport f + closedBall (0 : E) R) : upperBallEnvelope f r x = 0 := by
  have hval : ∀ h ∈ closedBall (0 : E) r, f (x + h) = 0 := by
    intro h hh
    by_contra hne
    apply hx
    have hn : ‖h‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hh
    refine ⟨x + h, subset_tsupport f hne, -h, ?_, ?_⟩
    · simpa only [mem_closedBall, dist_zero_right, norm_neg] using hn.trans hrR
    · simp
  apply le_antisymm
  · apply csSup_le (upperBallValues_nonempty f x hr)
    rintro y ⟨h, hh, rfl⟩
    change f (x + h) ≤ 0
    rw [hval h hh]
  · have h0 : f x = 0 := by
      simpa only [add_zero] using hval 0 (mem_closedBall_self hr)
    simpa only [h0] using self_le_upperBallEnvelope hf x hr

/-- A ball envelope of a compactly supported Lipschitz function remains
compactly supported in a proper normed group. -/
theorem upperBallEnvelope_hasCompactSupport [ProperSpace E] {f : E → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hc : HasCompactSupport f) {r : ℝ} (hr : 0 ≤ r) :
    HasCompactSupport (upperBallEnvelope f r) := by
  have hK : IsCompact (tsupport f + closedBall (0 : E) r) :=
    hc.isCompact.add (isCompact_closedBall (0 : E) r)
  apply HasCompactSupport.intro' hK hK.isClosed
  intro x hx
  exact upperBallEnvelope_eq_zero_of_notMem_add_support hf hr le_rfl hx

/-- The positive-radius difference quotients are bounded by the original
Lipschitz constant. -/
theorem upperBallEnvelope_difference_quotient_norm_le {f : E → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (x : E) {r : ℝ} (hr : 0 < r) :
    ‖(upperBallEnvelope f r x - f x) / r‖ ≤ (K : ℝ) := by
  have hl := self_le_upperBallEnvelope hf x hr.le
  have hu := upperBallEnvelope_le hf x hr.le
  have hq0 : 0 ≤ (upperBallEnvelope f r x - f x) / r :=
    div_nonneg (sub_nonneg.mpr hl) hr.le
  have hqK : (upperBallEnvelope f r x - f x) / r ≤ (K : ℝ) :=
    (div_le_iff₀ hr).mpr (by linarith)
  simpa only [Real.norm_eq_abs, abs_of_nonneg hq0] using hqK

end FourthRatio

end
