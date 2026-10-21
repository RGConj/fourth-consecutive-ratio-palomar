module

public import RequestProject.QuantileThresholds

/-! # Exact volume-coordinate control of strict quantile slabs -/

@[expose] public section
open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace FourthRatio

/-- A strict slab between two distinct quantiles has volume at most the
coordinate difference, including distributions with atoms at either endpoint. -/
theorem quantile_slab_volume_le {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : Integrable f μ)
    {s₁ s₂ : ℝ} (hs₁ : 0 < s₁) (hs₂ : 0 < s₂)
    (hq : decreasingProfile μ f s₂ < decreasingProfile μ f s₁) :
    μ {x | decreasingProfile μ f s₂ < f x ∧ f x < decreasingProfile μ f s₁} ≤
      ENNReal.ofReal (s₂ - s₁) := by
  let a := decreasingProfile μ f s₂
  let b := decreasingProfile μ f s₁
  let A := {x | a < f x}
  let B := {x | b ≤ f x}
  have hBA : B ⊆ A := fun x hx => hq.trans_le hx
  have hA : μ A ≤ ENNReal.ofReal s₂ := decreasingProfile_strict_tail_le hf hs₂
  have hB : ENNReal.ofReal s₁ ≤ μ B :=
    decreasingProfile_closed_tail_ge hf hs₁
      ((decreasingProfile_nonneg μ f s₂).trans_lt hq)
  have hAfin : μ A ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hA
  have hBfin : μ B ≠ ∞ := ne_top_of_le_ne_top hAfin (measure_mono hBA)
  have hBnull : NullMeasurableSet B μ := nullMeasurableSet_le aemeasurable_const hf.aemeasurable
  have hset : {x | a < f x ∧ f x < b} = A \ B := by
    ext x
    simp only [mem_setOf_eq, mem_diff, A, B, not_le]
  change μ {x | a < f x ∧ f x < b} ≤ _
  rw [hset, measure_sdiff hBA hBnull hBfin, ENNReal.ofReal_sub _ hs₁.le]
  exact tsub_le_tsub hA hB

end FourthRatio
end
