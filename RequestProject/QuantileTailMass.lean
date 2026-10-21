module

public import RequestProject.QuantileMass
public import RequestProject.QuantileThresholds

/-! # Integrability and initial-coordinate mass bounds for the actual profile -/

@[expose] public section
open Set MeasureTheory Filter
open scoped ENNReal
noncomputable section
namespace FourthRatio

/-- The real decreasing profile is integrable on its positive volume axis. -/
theorem decreasingProfile_integrableOn {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : Integrable f μ) (hf0 : ∀ x, 0 ≤ f x) :
    IntegrableOn (decreasingProfile μ f) (Ioi (0 : ℝ)) := by
  refine ⟨(decreasingProfile_measurable μ f).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall (decreasingProfile_nonneg μ f))]
  rw [decreasingProfile_lintegral_eq hf hf0]
  exact hf.lintegral_lt_top

theorem rearrangedDensity_integrable {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : Integrable f μ) (hf0 : ∀ x, 0 ≤ f x) :
    Integrable (rearrangedDensity μ f) :=
  (decreasingProfile_integrableOn hf hf0).integrable_indicator measurableSet_Ioi

/-- A measurable set of volume at most s carries no more mass than the first
s units of the constructed profile, in extended integral form. -/
theorem setLIntegral_le_profile_initial {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : Integrable f μ) (hf0 : ∀ x, 0 ≤ f x)
    {A : Set α} (hA : MeasurableSet A) {s : ℝ} (hAs : μ A ≤ ENNReal.ofReal s) :
    (∫⁻ x in A, ENNReal.ofReal (f x) ∂μ) ≤
      ∫⁻ t in Ioo (0 : ℝ) s, ENNReal.ofReal (decreasingProfile μ f t) := by
  apply (setLIntegral_le_decreasingProfile hf hf0 hA).trans
  apply lintegral_mono_set
  intro t ht
  exact ⟨ht.1, (ENNReal.ofReal_lt_ofReal_iff'.mp (ht.2.trans_le hAs)).1⟩

/-- Real mass bound, using proved integrability rather than a finiteness premise. -/
theorem setIntegral_le_profile_initial {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : Integrable f μ) (hf0 : ∀ x, 0 ≤ f x)
    {A : Set α} (hA : MeasurableSet A) {s : ℝ} (hAs : μ A ≤ ENNReal.ofReal s) :
    (∫ x in A, f x ∂μ) ≤ ∫ t in Ioo (0 : ℝ) s, decreasingProfile μ f t := by
  have hprof := (decreasingProfile_integrableOn hf hf0).mono_set
    (show Ioo (0 : ℝ) s ⊆ Ioi 0 from fun t ht => ht.1)
  have hle := setLIntegral_le_profile_initial hf hf0 hA hAs
  rw [← ofReal_integral_eq_lintegral_ofReal hf.integrableOn (Eventually.of_forall hf0),
    ← ofReal_integral_eq_lintegral_ofReal hprof
      (Eventually.of_forall (decreasingProfile_nonneg μ f))] at hle
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
  simpa only [ENNReal.toReal_ofReal (integral_nonneg hf0),
    ENNReal.toReal_ofReal (integral_nonneg (decreasingProfile_nonneg μ f))] using hreal

/-- In particular the upper quantile tail obeys the initial-coordinate mass bound. -/
theorem quantile_tail_mass_le {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : Integrable f μ) (hfm : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) {s : ℝ} (hs : 0 < s) :
    (∫ x in {x | decreasingProfile μ f s < f x}, f x ∂μ) ≤
      ∫ t in Ioo (0 : ℝ) s, decreasingProfile μ f t :=
  setIntegral_le_profile_initial hf hf0 (measurableSet_lt measurable_const hfm)
    (decreasingProfile_strict_tail_le hf hs)

end FourthRatio
end
