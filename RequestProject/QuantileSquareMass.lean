module

public import RequestProject.QuantileProfile
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Preservation of square mass for the actual decreasing profile -/

@[expose] public section
open Set MeasureTheory Filter
open scoped ENNReal
noncomputable section
namespace FourthRatio

/-- Layer cake and the exact positive superlevels give preservation of L² mass.
The integrals may be infinite, so no hidden L²-integrability premise is needed. -/
theorem decreasingProfile_sq_lintegral_eq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : Integrable f μ) (hf0 : ∀ x, 0 ≤ f x) :
    (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (decreasingProfile μ f s ^ 2)) =
      ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μ := by
  rw [lintegral_eq_lintegral_meas_lt (volume.restrict (Ioi (0 : ℝ)))
      (Eventually.of_forall (fun s => sq_nonneg (decreasingProfile μ f s)))
      ((decreasingProfile_measurable μ f).pow_const 2).aemeasurable,
    lintegral_eq_lintegral_meas_lt μ (Eventually.of_forall (fun x => sq_nonneg (f x)))
      (hf.aemeasurable.pow_const 2)]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have hsqrt : ∀ a : ℝ, 0 ≤ a → (t < a ^ 2 ↔ Real.sqrt t < a) := by
    intro a ha
    have hsq := Real.sq_sqrt ht.le
    have hsnon := Real.sqrt_nonneg t
    constructor <;> intro h <;> nlinarith
  have hfset : {x | t < f x ^ 2} = {x | Real.sqrt t < f x} := by
    ext x
    exact hsqrt (f x) (hf0 x)
  have hgset : {s | t < decreasingProfile μ f s ^ 2} =
      {s | Real.sqrt t < decreasingProfile μ f s} := by
    ext s
    exact hsqrt (decreasingProfile μ f s) (decreasingProfile_nonneg μ f s)
  dsimp only
  rw [hfset, hgset]
  exact decreasingProfile_superlevel_measure hf (Real.sqrt_nonneg t)

end FourthRatio
end
