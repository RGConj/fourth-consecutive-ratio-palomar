module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! # Lower semicontinuity of integrated superlevel-volume powers -/

@[expose] public section

open Set Filter MeasureTheory Topology
open scoped ENNReal

noncomputable section
namespace FourthRatio

/-- Fatou's lemma applied to open superlevel indicators. -/
theorem superlevel_measure_le_liminf {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} {u : ℕ → α → ℝ}
    (hf : AEMeasurable f μ) (hu : ∀ n, AEMeasurable (u n) μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => u n x) atTop (𝓝 (f x))) (t : ℝ) :
    μ {x | t < f x} ≤ liminf (fun n => μ {x | t < u n x}) atTop := by
  let F : ℕ → α → ℝ≥0∞ := fun n => {x | t < u n x}.indicator 1
  have hm : ∀ n, AEMeasurable (F n) μ := fun n =>
    aemeasurable_const.indicator₀ (nullMeasurableSet_lt aemeasurable_const (hu n))
  calc
    μ {x | t < f x} = ∫⁻ x, {x | t < f x}.indicator (1 : α → ℝ≥0∞) x ∂μ :=
      (lintegral_indicator_one₀ (nullMeasurableSet_lt aemeasurable_const hf)).symm
    _ ≤ ∫⁻ x, liminf (fun n => F n x) atTop ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hlim] with x hx
      by_cases ht : t < f x
      · rw [indicator_of_mem ht]
        refine le_liminf_of_le (by isBoundedDefault) ?_
        filter_upwards [hx.eventually (Ioi_mem_nhds ht)] with n hn
        simp [F, hn]
      · rw [indicator_of_notMem ht]
        exact bot_le
    _ ≤ liminf (fun n => ∫⁻ x, F n x ∂μ) atTop := lintegral_liminf_le' hm
    _ = _ := by
      congr 1
      funext n
      exact lintegral_indicator_one₀ (nullMeasurableSet_lt aemeasurable_const (hu n))

/-- Integrated powers of superlevel volume are lower semicontinuous for a.e.
convergence. Constants may be any finite extended nonnegative reals. -/
theorem level_volume_lintegral_le_liminf {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} {u : ℕ → α → ℝ}
    (hf : AEMeasurable f μ) (hu : ∀ n, AEMeasurable (u n) μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => u n x) atTop (𝓝 (f x)))
    {p : ℝ} (hp : 0 < p) {C D : ℝ≥0∞} (hC : C ≠ ∞) (hD : D ≠ ∞) :
    (∫⁻ t in Ioi (0 : ℝ), C * μ {x | t < f x} ^ p * D) ≤
      liminf (fun n => ∫⁻ t in Ioi (0 : ℝ), C * μ {x | t < u n x} ^ p * D) atTop := by
  let g : ℝ≥0∞ → ℝ≥0∞ := fun a => C * a ^ p * D
  have hgm : Monotone g := fun a b hab =>
    mul_le_mul_left (mul_le_mul_right ((ENNReal.rpow_le_rpow_iff hp).mpr hab) C) D
  have hgc : Continuous g :=
    (ENNReal.continuous_mul_const hD).comp
      ((ENNReal.continuous_const_mul hC).comp ENNReal.continuous_rpow_const)
  calc
    _ ≤ ∫⁻ t in Ioi (0 : ℝ), liminf (fun n => g (μ {x | t < u n x})) atTop := by
      apply lintegral_mono
      intro t
      calc
        g (μ {x | t < f x}) ≤ g (liminf (fun n => μ {x | t < u n x}) atTop) :=
          hgm (superlevel_measure_le_liminf hf hu hlim t)
        _ = _ := hgm.map_liminf_of_continuousAt _ hgc.continuousAt
    _ ≤ _ := by
      apply lintegral_liminf_le
      intro n
      have ha : Antitone (fun t : ℝ => μ {x | t < u n x}) := fun s t hst =>
        measure_mono fun x hx => lt_of_le_of_lt hst hx
      exact hgc.measurable.comp ha.measurable

end FourthRatio
end
