module

public import RequestProject.BallEnvelopeDerivative
public import RequestProject.BallEnvelopeSupport
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! # Integral first variation of the upper ball envelope -/

@[expose] public section

open Set Metric Filter Topology MeasureTheory
open scoped NNReal RealInnerProductSpace Pointwise

noncomputable section

namespace FourthRatio

/-- For a compactly supported C¹ function, the integral of the positive-radius
upper-envelope difference quotient tends to the integral of the gradient norm. -/
theorem tendsto_integral_upperBallEnvelope_difference_quotient {N : ℕ}
    {f : EuclideanSpace ℝ (Fin N) → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    Tendsto (fun r : ℝ => ∫ x, (upperBallEnvelope f r x - f x) / r)
      (𝓝[>] 0) (𝓝 (∫ x, ‖gradient f x‖)) := by
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hf one_ne_zero
  let A : Set (EuclideanSpace ℝ (Fin N)) := tsupport f + closedBall 0 1
  have hAc : IsCompact A := hc.isCompact.add (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin N)) 1)
  have hAm : MeasurableSet A := hAc.isClosed.measurableSet
  let bound : EuclideanSpace ℝ (Fin N) → ℝ := A.indicator (fun _ => (K : ℝ))
  have hbi : Integrable bound :=
    (integrableOn_const (μ := volume) (s := A) (C := (K : ℝ)) hAc.measure_ne_top).integrable_indicator hAm
  have hm : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      AEStronglyMeasurable (fun x => (upperBallEnvelope f r x - f x) / r) volume := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr0 : 0 < r := hr
    exact (((upperBallEnvelope_lipschitz hK hr0.le).continuous.sub hK.continuous).div_const r).aestronglyMeasurable
  have hb : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ∀ᵐ x ∂volume, ‖(upperBallEnvelope f r x - f x) / r‖ ≤ bound x := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with r hr
    apply Filter.Eventually.of_forall
    intro x
    by_cases hx : x ∈ A
    · change ‖(upperBallEnvelope f r x - f x) / r‖ ≤ A.indicator (fun _ => (K : ℝ)) x
      rw [indicator_of_mem hx]
      exact upperBallEnvelope_difference_quotient_norm_le hK x hr.1
    · have hz := upperBallEnvelope_eq_zero_of_notMem_add_support hK hr.1.le hr.2.le hx
      have hnot : x ∉ tsupport f := by
        intro hxf
        apply hx
        exact ⟨x, hxf, 0, mem_closedBall_self (by norm_num), by simp⟩
      have hfz : f x = 0 := image_eq_zero_of_notMem_tsupport hnot
      change ‖(upperBallEnvelope f r x - f x) / r‖ ≤ A.indicator (fun _ => (K : ℝ)) x
      rw [indicator_of_notMem hx, hz, hfz, sub_self, zero_div, norm_zero]
  have hl : ∀ᵐ x ∂volume, Tendsto (fun r : ℝ => (upperBallEnvelope f r x - f x) / r)
      (𝓝[>] 0) (𝓝 ‖gradient f x‖) := by
    apply Filter.Eventually.of_forall
    intro x
    have hg : HasGradientAt f (gradient f x) x :=
      ((hf.differentiable one_ne_zero x).hasFDerivAt).hasGradientAt
    exact tendsto_upperBallEnvelope_difference_quotient hK hg
  exact tendsto_integral_filter_of_dominated_convergence bound hm hb hbi hl

end FourthRatio

end
