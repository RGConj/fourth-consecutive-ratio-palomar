module

public import RequestProject.RearrangementMass
public import Mathlib.MeasureTheory.Integral.Lebesgue.Sub

/-! # Layer-cake identities for ordered integrable differences -/

@[expose] public section

open Set MeasureTheory Filter
open scoped ENNReal

namespace FourthRatio

/-- The integrated excess of the superlevel volumes equals the mass of the
difference of two ordered nonnegative integrable functions. -/
theorem superlevel_difference_lintegral {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f g : α → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) (hfg : ∀ x, f x ≤ g x) :
    (∫⁻ t in Ioi (0 : ℝ), μ {x | t < g x} - μ {x | t < f x}) =
      ENNReal.ofReal (∫ x, g x - f x ∂μ) := by
  have hfm : Measurable (fun t : ℝ => μ {x | t < f x}) := by
    apply Antitone.measurable
    intro s t hst
    apply measure_mono
    intro x hx
    have hxt : t < f x := hx
    exact lt_of_le_of_lt hst hxt
  have hfl := lintegral_eq_lintegral_meas_lt μ (Eventually.of_forall hf0) hf.aemeasurable
  have hgl := lintegral_eq_lintegral_meas_lt μ (Eventually.of_forall hg0) hg.aemeasurable
  have hfin : (∫⁻ t in Ioi (0 : ℝ), μ {x | t < f x}) ≠ ⊤ := by
    rw [← hfl]
    exact hf.lintegral_lt_top.ne
  have hle : (fun t => μ {x | t < f x}) ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun t => μ {x | t < g x}) := by
    apply Eventually.of_forall
    intro t
    apply measure_mono
    intro x hx
    have hxt : t < f x := hx
    exact hxt.trans_le (hfg x)
  rw [lintegral_sub hfm hfin hle, ← hgl, ← hfl,
    ← ofReal_integral_eq_lintegral_ofReal hg (Eventually.of_forall hg0),
    ← ofReal_integral_eq_lintegral_ofReal hf (Eventually.of_forall hf0)]
  calc
    ENNReal.ofReal (∫ x, g x ∂μ) - ENNReal.ofReal (∫ x, f x ∂μ) =
        ENNReal.ofReal ((∫ x, g x ∂μ) - ∫ x, f x ∂μ) :=
      (ENNReal.ofReal_sub _ (integral_nonneg hf0)).symm
    _ = _ := congrArg ENNReal.ofReal (integral_sub hg hf).symm

/-- The same identity with a positive difference-quotient parameter. -/
theorem superlevel_difference_div_lintegral {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f g : α → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) (hfg : ∀ x, f x ≤ g x)
    {r : ℝ} (hr : 0 < r) :
    (∫⁻ t in Ioi (0 : ℝ), (μ {x | t < g x} - μ {x | t < f x}) / ENNReal.ofReal r) =
      ENNReal.ofReal (∫ x, (g x - f x) / r ∂μ) := by
  calc
    _ = (∫⁻ t in Ioi (0 : ℝ), μ {x | t < g x} - μ {x | t < f x}) / ENNReal.ofReal r := by
      simp only [div_eq_mul_inv]
      exact lintegral_mul_const' _ _
        (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr hr))
    _ = ENNReal.ofReal (∫ x, g x - f x ∂μ) / ENNReal.ofReal r := by
      rw [superlevel_difference_lintegral hf hg hf0 hg0 hfg]
    _ = ENNReal.ofReal ((∫ x, g x - f x ∂μ) / r) := (ENNReal.ofReal_div_of_pos hr).symm
    _ = _ := congrArg ENNReal.ofReal (integral_div r (fun x => g x - f x)).symm

end FourthRatio
