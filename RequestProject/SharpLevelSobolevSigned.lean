module

public import RequestProject.BallEnvelopeIntegral
public import RequestProject.BallEnvelopeIsoperimetric
public import RequestProject.LayercakeSigned

/-!
# The sharp level-volume Sobolev bound

The proof differentiates Brunn--Minkowski through upper ball envelopes and
layer cake. No perimeter or rearrangement-energy theorem is assumed.
-/

@[expose] public section

open Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace FourthRatio

/-- The sharp L¹ gradient bound by the integrated powers of the positive
superlevel volumes, for an arbitrary compactly supported C¹ function. -/
theorem sharp_level_volume_gradient_bound_signed {N : ℕ} (hN : 2 ≤ N)
    {f : EuclideanSpace ℝ (Fin N) → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) :
    (∫⁻ t in Ioi (0 : ℝ),
      (N : ℝ≥0∞) * volume {x | t < f x} ^ (1 - (N : ℝ)⁻¹) *
        volume (ball (0 : EuclideanSpace ℝ (Fin N)) 1) ^ (N : ℝ)⁻¹) ≤
      ENNReal.ofReal (∫ x, ‖gradient f x‖) := by
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hf one_ne_zero
  have hfi : Integrable f := hf.continuous.integrable_of_hasCompactSupport hc
  let lhs : ℝ≥0∞ := ∫⁻ t in Ioi (0 : ℝ),
    (N : ℝ≥0∞) * volume {x | t < f x} ^ (1 - (N : ℝ)⁻¹) *
      volume (ball (0 : EuclideanSpace ℝ (Fin N)) 1) ^ (N : ℝ)⁻¹
  change lhs ≤ ENNReal.ofReal (∫ x, ‖gradient f x‖)
  have hb : ∀ r > 0, lhs ≤ ENNReal.ofReal (∫ x, (upperBallEnvelope f r x - f x) / r) := by
    intro r hr
    have hgi : Integrable (upperBallEnvelope f r) :=
      (upperBallEnvelope_lipschitz hK hr.le).continuous.integrable_of_hasCompactSupport
        (upperBallEnvelope_hasCompactSupport hK hc hr.le)
    have hfg : ∀ x, f x ≤ upperBallEnvelope f r x := fun x => self_le_upperBallEnvelope hK x hr.le
    calc
      lhs ≤ ∫⁻ t in Ioi (0 : ℝ),
          (volume {x | t < upperBallEnvelope f r x} - volume {x | t < f x}) /
            ENNReal.ofReal r := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        change (N : ℝ≥0∞) * volume {x | t < f x} ^ (1 - (N : ℝ)⁻¹) *
          volume (ball (0 : EuclideanSpace ℝ (Fin N)) 1) ^ (N : ℝ)⁻¹ ≤
          (volume {x | t < upperBallEnvelope f r x} - volume {x | t < f x}) /
            ENNReal.ofReal r
        exact upperBallEnvelope_level_isoperimetric hN hK hc hr ht
      _ ≤ _ := superlevel_difference_div_lintegral_le hfi hgi hfg hr
  have hi := tendsto_integral_upperBallEnvelope_difference_quotient hf hc
  have he := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hi
  apply le_of_tendsto_of_tendsto tendsto_const_nhds he
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact hb r hr

end FourthRatio

end
