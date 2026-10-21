module

public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Tactic

/-!
# Superlevel-set control of mass on a measurable set

The layer-cake bound used in the Hardy--Littlewood part of Chiti comparison.
This file does not assert the existence or the energy inequality of a Schwarz
rearrangement of a weak eigenfunction.
-/

@[expose] public section

open MeasureTheory Set

namespace FourthRatio

/-- The mass carried by a set is bounded by the integrated minimum of its volume
and the superlevel volumes of the density. -/
theorem setLIntegral_le_superlevel_min {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : Measurable f) (hnn : ∀ x, 0 ≤ f x)
    {A : Set α} (hA : MeasurableSet A) :
    (∫⁻ x in A, ENNReal.ofReal (f x) ∂μ) ≤
      ∫⁻ t in Ioi (0 : ℝ), min (μ A) (μ {x | t < f x}) := by
  rw [lintegral_eq_lintegral_meas_lt (μ.restrict A)
    (Filter.Eventually.of_forall hnn) hf.aemeasurable]
  apply lintegral_mono
  intro t
  have hs : MeasurableSet {x | t < f x} := measurableSet_lt measurable_const hf
  change (μ.restrict A) {x | t < f x} ≤ min (μ A) (μ {x | t < f x})
  rw [Measure.restrict_apply hs]
  exact le_min (measure_mono inter_subset_right) (measure_mono inter_subset_left)

/-- A set nested with each positive superlevel set attains the layer-cake mass
bound. This is a measure-theoretic statement, independent of dimension. -/
theorem setLIntegral_eq_superlevel_min {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : Measurable f) (hnn : ∀ x, 0 ≤ f x)
    {A : Set α} (hA : MeasurableSet A)
    (hnested : ∀ t > 0, {x | t < f x} ⊆ A ∨ A ⊆ {x | t < f x}) :
    (∫⁻ x in A, ENNReal.ofReal (f x) ∂μ) =
      ∫⁻ t in Ioi (0 : ℝ), min (μ A) (μ {x | t < f x}) := by
  rw [lintegral_eq_lintegral_meas_lt (μ.restrict A)
    (Filter.Eventually.of_forall hnn) hf.aemeasurable]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have hs : MeasurableSet {x | t < f x} := measurableSet_lt measurable_const hf
  change (μ.restrict A) {x | t < f x} = min (μ A) (μ {x | t < f x})
  rw [Measure.restrict_apply hs]
  rcases hnested t ht with hsmall | hlarge
  · rw [inter_eq_left.mpr hsmall, min_eq_right (measure_mono hsmall)]
  · rw [inter_eq_right.mpr hlarge, min_eq_left (measure_mono hlarge)]

/-- The Hardy--Littlewood mass comparison for an equimeasurable profile whose
positive superlevel sets are nested with the comparison set. -/
theorem setLIntegral_le_of_equidistributed_nested {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
    {f : α → ℝ} {g : β → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    {A : Set α} {B : Set β} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hvol : μ A = ν B)
    (hequi : ∀ t > 0, μ {x | t < f x} = ν {x | t < g x})
    (hnested : ∀ t > 0, {x | t < g x} ⊆ B ∨ B ⊆ {x | t < g x}) :
    (∫⁻ x in A, ENNReal.ofReal (f x) ∂μ) ≤
      ∫⁻ x in B, ENNReal.ofReal (g x) ∂ν := by
  calc
    _ ≤ ∫⁻ t in Ioi (0 : ℝ), min (μ A) (μ {x | t < f x}) :=
      setLIntegral_le_superlevel_min hf hf0 hA
    _ = ∫⁻ t in Ioi (0 : ℝ), min (ν B) (ν {x | t < g x}) := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro t ht
      change min (μ A) (μ {x | t < f x}) = min (ν B) (ν {x | t < g x})
      rw [hvol, hequi t ht]
    _ = _ := (setLIntegral_eq_superlevel_min hg hg0 hB hnested).symm

end FourthRatio
