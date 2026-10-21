module

public import RequestProject.QuantileSquareAE

/-! # Real square-mass integrability and identities for the actual profile -/

@[expose] public section
open Set MeasureTheory Filter
open scoped ENNReal
noncomputable section
namespace FourthRatio

theorem decreasingProfile_sq_integrable_ae {α : Type*} [MeasurableSpace α]
    {mu : Measure α} {f : α → ℝ} (hf : Integrable f mu)
    (hf0 : ∀ᵐ x ∂mu, 0 ≤ f x) (hfsq : Integrable (fun x => f x ^ 2) mu) :
    IntegrableOn (fun s => decreasingProfile mu f s ^ 2) (Ioi (0 : ℝ)) := by
  refine ⟨((decreasingProfile_measurable mu f).pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun s => sq_nonneg (decreasingProfile mu f s))),
    decreasingProfile_sq_lintegral_eq_ae hf hf0]
  exact hfsq.lintegral_lt_top

theorem integral_sq_decreasingProfile_eq_ae {α : Type*} [MeasurableSpace α]
    {mu : Measure α} {f : α → ℝ} (hf : Integrable f mu)
    (hf0 : ∀ᵐ x ∂mu, 0 ≤ f x) (hfsq : Integrable (fun x => f x ^ 2) mu) :
    (∫ s in Ioi (0 : ℝ), decreasingProfile mu f s ^ 2) = ∫ x, f x ^ 2 ∂mu := by
  have hp := decreasingProfile_sq_integrable_ae hf hf0 hfsq
  have he := decreasingProfile_sq_lintegral_eq_ae hf hf0
  rw [← ofReal_integral_eq_lintegral_ofReal hp
      (Eventually.of_forall (fun s => sq_nonneg (decreasingProfile mu f s))),
    ← ofReal_integral_eq_lintegral_ofReal hfsq (Eventually.of_forall (fun x => sq_nonneg (f x)))] at he
  have hr := congrArg ENNReal.toReal he
  simpa only [ENNReal.toReal_ofReal (integral_nonneg (fun s => sq_nonneg (decreasingProfile mu f s))),
    ENNReal.toReal_ofReal (integral_nonneg (fun x => sq_nonneg (f x)))] using hr

theorem setIntegral_sq_le_profile_initial_ae {α : Type*} [MeasurableSpace α]
    {mu : Measure α} {f : α → ℝ} (hf : Integrable f mu) (hfm : Measurable f)
    (hf0 : ∀ᵐ x ∂mu, 0 ≤ f x) (hfsq : Integrable (fun x => f x ^ 2) mu)
    {A : Set α} (hA : MeasurableSet A) {m : ℝ} (hAm : mu A ≤ ENNReal.ofReal m) :
    (∫ x in A, f x ^ 2 ∂mu) ≤ ∫ s in Ioo (0 : ℝ) m, decreasingProfile mu f s ^ 2 := by
  have hp := (decreasingProfile_sq_integrable_ae hf hf0 hfsq).mono_set
    (show Ioo (0 : ℝ) m ⊆ Ioi 0 from fun s hs => hs.1)
  have he := setLIntegral_sq_le_profile_initial_ae hf hfm hf0 hA hAm
  rw [← ofReal_integral_eq_lintegral_ofReal hfsq.integrableOn
      (Eventually.of_forall (fun x => sq_nonneg (f x))),
    ← ofReal_integral_eq_lintegral_ofReal hp
      (Eventually.of_forall (fun s => sq_nonneg (decreasingProfile mu f s)))] at he
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top he
  simpa only [ENNReal.toReal_ofReal (integral_nonneg (fun x => sq_nonneg (f x))),
    ENNReal.toReal_ofReal (integral_nonneg (fun s => sq_nonneg (decreasingProfile mu f s)))] using hr

end FourthRatio
end
