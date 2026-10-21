module

public import RequestProject.DecreasingQuantile
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Exact distribution of the constructed decreasing quantile -/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal

namespace FourthRatio

lemma volume_positive_ofReal_lt (a : ℝ≥0∞) :
    volume {s : ℝ | 0 < s ∧ ENNReal.ofReal s < a} = a := by
  by_cases ha : a = ⊤
  · subst a
    have hs : {s : ℝ | 0 < s ∧ ENNReal.ofReal s < ⊤} = Ioi 0 := by
      ext s
      simp only [ENNReal.ofReal_lt_top, and_true, mem_Ioi, Set.mem_ofPred_eq]
    rw [hs, Real.volume_Ioi]
  · have heq : ENNReal.ofReal a.toReal = a := ENNReal.ofReal_toReal ha
    have hs : {s : ℝ | 0 < s ∧ ENNReal.ofReal s < a} = Ioo 0 a.toReal := by
      ext s
      change (0 < s ∧ ENNReal.ofReal s < a) ↔ (0 < s ∧ s < a.toReal)
      constructor
      · rintro ⟨hs, hsa⟩
        have hsa' : ENNReal.ofReal s < ENNReal.ofReal a.toReal := by rwa [heq]
        exact ⟨hs, (ENNReal.ofReal_lt_ofReal_iff'.mp hsa').1⟩
      · rintro ⟨hs, hsa⟩
        have hsa' : ENNReal.ofReal s < ENNReal.ofReal a.toReal :=
          ENNReal.ofReal_lt_ofReal_iff'.mpr ⟨hsa, lt_trans hs hsa⟩
        exact ⟨hs, by rwa [heq] at hsa'⟩
    rw [hs, Real.volume_Ioo, sub_zero, heq]

/-- The quantile is equidistributed with the original density, when its volume
coordinate is equipped with Lebesgue measure on the positive half-line. -/
theorem decreasingQuantile_superlevel_volume {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    volume {s : ℝ | 0 < s ∧ ENNReal.ofReal t < decreasingQuantile μ f s} =
      μ {x | t < f x} := by
  have hs : {s : ℝ | 0 < s ∧ ENNReal.ofReal t < decreasingQuantile μ f s} =
      {s : ℝ | 0 < s ∧ ENNReal.ofReal s < μ {x | t < f x}} := by
    ext s
    change (0 < s ∧ ENNReal.ofReal t < decreasingQuantile μ f s) ↔
      (0 < s ∧ ENNReal.ofReal s < μ {x | t < f x})
    rw [decreasingQuantile_superlevel_iff μ f ht]
  rw [hs]
  exact volume_positive_ofReal_lt _

end FourthRatio
