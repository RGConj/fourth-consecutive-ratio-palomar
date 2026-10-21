module

public import RequestProject.QuantileProfile

/-! # Hardy--Littlewood mass comparison for the constructed rearrangement -/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace FourthRatio

/-- The layer-cake mass bound only needs almost-everywhere measurability. -/
theorem setLIntegral_le_superlevel_min_ae {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : AEMeasurable f μ) (hf0 : ∀ x, 0 ≤ f x)
    {A : Set α} (hA : MeasurableSet A) :
    (∫⁻ x in A, ENNReal.ofReal (f x) ∂μ) ≤
      ∫⁻ t in Ioi (0 : ℝ), min (μ A) (μ {x | t < f x}) := by
  rw [lintegral_eq_lintegral_meas_lt (μ.restrict A)
    (Filter.Eventually.of_forall hf0) hf.restrict]
  apply lintegral_mono
  intro t
  change (μ.restrict A) {x | t < f x} ≤ min (μ A) (μ {x | t < f x})
  apply le_min
  · calc
      _ ≤ (μ.restrict A) univ := measure_mono (subset_univ _)
      _ = μ A := by simp
  · exact Measure.restrict_apply_le _ _

/-- The real decreasing density, zero-extended outside the volume half-line. -/
def rearrangedDensity {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) : ℝ → ℝ := (Ioi 0).indicator (decreasingProfile μ f)

lemma rearrangedDensity_measurable {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) : Measurable (rearrangedDensity μ f) :=
  (decreasingProfile_measurable μ f).indicator measurableSet_Ioi

lemma rearrangedDensity_nonneg {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) (s : ℝ) : 0 ≤ rearrangedDensity μ f s := by
  exact indicator_nonneg (fun s _ => decreasingProfile_nonneg μ f s) s

/-- Exact superlevels of the zero-extended real rearrangement. -/
theorem rearrangedDensity_superlevel {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : Integrable f μ) {t : ℝ} (ht : 0 < t) :
    {s | t < rearrangedDensity μ f s} =
      {s : ℝ | 0 < s ∧ ENNReal.ofReal s < μ {x | t < f x}} := by
  ext s
  change (t < (Ioi 0).indicator (decreasingProfile μ f) s) ↔
    (0 < s ∧ ENNReal.ofReal s < μ {x | t < f x})
  by_cases hs : 0 < s
  · rw [indicator_of_mem hs]
    simp only [hs, true_and]
    exact decreasingProfile_superlevel_iff hf ht.le hs
  · rw [indicator_of_notMem hs]
    simp only [hs, false_and, not_lt_of_ge ht.le]

/-- A set of volume m carries at most the first m units of the constructed
rearranged density. This applies to every nonnegative integrable density;
no rearrangement-existence or equidistribution premise is assumed. -/
theorem setLIntegral_le_decreasingProfile {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : Integrable f μ) (hf0 : ∀ x, 0 ≤ f x)
    {A : Set α} (hA : MeasurableSet A) :
    (∫⁻ x in A, ENNReal.ofReal (f x) ∂μ) ≤
      ∫⁻ s in {s : ℝ | 0 < s ∧ ENNReal.ofReal s < μ A},
        ENNReal.ofReal (decreasingProfile μ f s) := by
  let B : Set ℝ := {s | 0 < s ∧ ENNReal.ofReal s < μ A}
  have hBm : MeasurableSet B :=
    measurableSet_Ioi.inter (measurableSet_lt ENNReal.measurable_ofReal measurable_const)
  have hBvol : volume B = μ A := volume_positive_ofReal_lt _
  have hequi : ∀ t > 0, μ {x | t < f x} = volume {s | t < rearrangedDensity μ f s} := by
    intro t ht
    rw [rearrangedDensity_superlevel hf ht]
    exact (volume_positive_ofReal_lt _).symm
  have hnested : ∀ t > 0,
      {s | t < rearrangedDensity μ f s} ⊆ B ∨ B ⊆ {s | t < rearrangedDensity μ f s} := by
    intro t ht
    rw [rearrangedDensity_superlevel hf ht]
    rcases le_total (μ {x | t < f x}) (μ A) with h | h
    · left
      intro s hs
      exact ⟨hs.1, hs.2.trans_le h⟩
    · right
      intro s hs
      exact ⟨hs.1, hs.2.trans_le h⟩
  calc
    _ ≤ ∫⁻ t in Ioi (0 : ℝ), min (μ A) (μ {x | t < f x}) :=
      setLIntegral_le_superlevel_min_ae hf.aemeasurable hf0 hA
    _ = ∫⁻ t in Ioi (0 : ℝ), min (volume B) (volume {s | t < rearrangedDensity μ f s}) := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro t ht
      change min (μ A) (μ {x | t < f x}) =
        min (volume B) (volume {s | t < rearrangedDensity μ f s})
      rw [hBvol, hequi t ht]
    _ = ∫⁻ s in B, ENNReal.ofReal (rearrangedDensity μ f s) :=
      (setLIntegral_eq_superlevel_min (rearrangedDensity_measurable μ f)
        (rearrangedDensity_nonneg μ f) hBm hnested).symm
    _ = _ := by
      apply setLIntegral_congr_fun hBm
      intro s hs
      change ENNReal.ofReal (rearrangedDensity μ f s) =
        ENNReal.ofReal (decreasingProfile μ f s)
      rw [rearrangedDensity, indicator_of_mem hs.1]

end FourthRatio

end
