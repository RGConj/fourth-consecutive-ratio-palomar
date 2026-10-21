module

public import RequestProject.QuantileDistribution
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-! # A finite real decreasing rearrangement and preservation of mass -/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace FourthRatio

/-- Markov's inequality gives an explicit bound for the constructed quantile. -/
theorem decreasingQuantile_le_integral_div {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : AEMeasurable f μ) {s : ℝ} (hs : 0 < s) :
    decreasingQuantile μ f s ≤ (∫⁻ x, ENNReal.ofReal (f x) ∂μ) / ENNReal.ofReal s := by
  unfold decreasingQuantile
  apply iSup_le
  intro q
  by_cases hq : ENNReal.ofReal s < μ {x | (q : ℝ) < f x}
  · rw [if_pos hq]
    apply (ENNReal.le_div_iff_mul_le
      (Or.inl (ENNReal.ofReal_ne_zero_iff.mpr hs)) (Or.inl ENNReal.ofReal_ne_top)).mpr
    calc
      ENNReal.ofReal (q : ℝ) * ENNReal.ofReal s ≤
          ENNReal.ofReal (q : ℝ) * μ {x | (q : ℝ) < f x} := mul_le_mul_right hq.le _
      _ ≤ ENNReal.ofReal (q : ℝ) *
          μ {x | ENNReal.ofReal (q : ℝ) ≤ ENNReal.ofReal (f x)} := by
        apply mul_le_mul_right
        apply measure_mono
        intro x hx
        exact ENNReal.ofReal_le_ofReal (le_of_lt hx)
      _ ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ :=
        mul_meas_ge_le_lintegral₀ (ENNReal.measurable_ofReal.comp_aemeasurable hf) _
  · rw [if_neg hq]
    exact bot_le

theorem decreasingQuantile_lt_top {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : Integrable f μ) {s : ℝ} (hs : 0 < s) :
    decreasingQuantile μ f s < ⊤ :=
  (decreasingQuantile_le_integral_div hf.aemeasurable hs).trans_lt
    (ENNReal.div_lt_top hf.lintegral_lt_top.ne (ENNReal.ofReal_ne_zero_iff.mpr hs))

/-- The finite real profile associated to the ENNReal quantile. -/
def decreasingProfile {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) (s : ℝ) : ℝ := (decreasingQuantile μ f s).toReal

lemma decreasingProfile_nonneg {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) (s : ℝ) : 0 ≤ decreasingProfile μ f s :=
  ENNReal.toReal_nonneg

theorem decreasingProfile_measurable {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) : Measurable (decreasingProfile μ f) :=
  ENNReal.measurable_toReal.comp (decreasingQuantile_measurable μ f)

theorem decreasingProfile_antitoneOn {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : Integrable f μ) :
    AntitoneOn (decreasingProfile μ f) (Ioi 0) := by
  intro s hs t ht hst
  exact ENNReal.toReal_mono (decreasingQuantile_lt_top hf hs).ne
    (decreasingQuantile_antitone μ f hst)

theorem decreasingProfile_superlevel_iff {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : Integrable f μ) {t s : ℝ}
    (ht : 0 ≤ t) (hs : 0 < s) :
    t < decreasingProfile μ f s ↔ ENNReal.ofReal s < μ {x | t < f x} := by
  exact (ENNReal.ofReal_lt_iff_lt_toReal ht (decreasingQuantile_lt_top hf hs).ne).symm.trans
    (decreasingQuantile_superlevel_iff μ f ht)

/-- Exact equidistribution for the finite real profile. -/
theorem decreasingProfile_superlevel_measure {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : Integrable f μ) {t : ℝ} (ht : 0 ≤ t) :
    (volume.restrict (Ioi (0 : ℝ))) {s | t < decreasingProfile μ f s} =
      μ {x | t < f x} := by
  have hset : {s | t < decreasingProfile μ f s} ∩ Ioi 0 =
      {s : ℝ | 0 < s ∧ ENNReal.ofReal t < decreasingQuantile μ f s} := by
    ext s
    change (t < decreasingProfile μ f s ∧ 0 < s) ↔
      (0 < s ∧ ENNReal.ofReal t < decreasingQuantile μ f s)
    constructor
    · rintro ⟨h, hs⟩
      exact ⟨hs, (ENNReal.ofReal_lt_iff_lt_toReal ht
        (decreasingQuantile_lt_top hf hs).ne).mpr h⟩
    · rintro ⟨hs, h⟩
      exact ⟨(ENNReal.ofReal_lt_iff_lt_toReal ht
        (decreasingQuantile_lt_top hf hs).ne).mp h, hs⟩
  rw [Measure.restrict_apply
    (measurableSet_lt measurable_const (decreasingProfile_measurable μ f)), hset]
  exact decreasingQuantile_superlevel_volume μ f ht

/-- The constructed real rearrangement preserves the mass of a nonnegative
integrable density. -/
theorem decreasingProfile_lintegral_eq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : Integrable f μ) (hf0 : ∀ x, 0 ≤ f x) :
    (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (decreasingProfile μ f s)) =
      ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  rw [lintegral_eq_lintegral_meas_lt (volume.restrict (Ioi (0 : ℝ)))
      (Filter.Eventually.of_forall (decreasingProfile_nonneg μ f))
      (decreasingProfile_measurable μ f).aemeasurable,
    lintegral_eq_lintegral_meas_lt μ (Filter.Eventually.of_forall hf0) hf.aemeasurable]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t ht
  change (volume.restrict (Ioi (0 : ℝ))) {s | t < decreasingProfile μ f s} =
    μ {x | t < f x}
  exact decreasingProfile_superlevel_measure hf ht.le

end FourthRatio

end
