module

public import RequestProject.LayercakeDifference

/-! # A positive-superlevel difference bound for signed functions -/

@[expose] public section
open Set MeasureTheory Filter
open scoped ENNReal
namespace FourthRatio

theorem superlevel_difference_div_lintegral_le {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f g : α → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : ∀ x, f x ≤ g x) {r : ℝ} (hr : 0 < r) :
    (∫⁻ t in Ioi (0 : ℝ), (μ {x | t < g x} - μ {x | t < f x}) / ENNReal.ofReal r) ≤
      ENNReal.ofReal (∫ x, (g x - f x) / r ∂μ) := by
  have heq : (∫⁻ t in Ioi (0 : ℝ),
      (μ {x | t < g x} - μ {x | t < f x}) / ENNReal.ofReal r) =
      ∫⁻ t in Ioi (0 : ℝ),
      (μ {x | t < max (g x) 0} - μ {x | t < max (f x) 0}) / ENNReal.ofReal r := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have hpos : ∀ (h : α → ℝ), {x | t < max (h x) 0} = {x | t < h x} := by
      intro h
      ext x
      simp only [mem_setOf_eq, lt_max_iff, not_lt_of_ge ht.le, or_false]
    dsimp only
    rw [hpos, hpos]
  rw [heq, superlevel_difference_div_lintegral hf.pos_part hg.pos_part
    (fun _ => le_max_right _ _) (fun _ => le_max_right _ _)
    (fun x => max_le_max (hfg x) le_rfl) hr]
  apply ENNReal.ofReal_le_ofReal
  apply integral_mono ((hg.pos_part.sub hf.pos_part).div_const r) ((hg.sub hf).div_const r)
  intro x
  apply div_le_div_of_nonneg_right _ hr.le
  change max (g x) 0 - max (f x) 0 ≤ g x - f x
  rcases le_or_gt (f x) 0 with hf0 | hf0
  · rw [max_eq_right hf0]
    rcases le_or_gt (g x) 0 with hg0 | hg0
    · rw [max_eq_right hg0]
      linarith [hfg x]
    · rw [max_eq_left hg0.le]
      linarith
  · rw [max_eq_left hf0.le, max_eq_left (hf0.le.trans (hfg x))]

end FourthRatio
