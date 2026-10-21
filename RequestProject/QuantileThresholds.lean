module

public import RequestProject.QuantileProfile
public import Mathlib.MeasureTheory.Measure.Continuity

/-! # Threshold volume bounds for the constructed decreasing profile -/

@[expose] public section
open Set MeasureTheory Filter Topology
open scoped ENNReal
noncomputable section
namespace FourthRatio

/-- The strict superlevel at the quantile has volume at most its coordinate. -/
theorem decreasingProfile_strict_tail_le {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : Integrable f μ) {s : ℝ} (hs : 0 < s) :
    μ {x | decreasingProfile μ f s < f x} ≤ ENNReal.ofReal s := by
  apply not_lt.mp
  intro h
  have ht := (decreasingProfile_superlevel_iff hf (decreasingProfile_nonneg μ f s) hs).mpr h
  exact lt_irrefl _ ht

/-- Conversely the closed superlevel at a positive quantile carries at least
its coordinate. This includes possible atoms in the distribution. -/
theorem decreasingProfile_closed_tail_ge {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : Integrable f μ) {s : ℝ} (hs : 0 < s)
    (hq : 0 < decreasingProfile μ f s) :
    ENNReal.ofReal s ≤ μ {x | decreasingProfile μ f s ≤ f x} := by
  let a := decreasingProfile μ f s
  have ha : 0 < a := hq
  let t : ℕ → ℝ := fun n => a - a * (1 / ((n : ℝ) + 1))
  have htnonneg : ∀ n, 0 ≤ t n := by
    intro n
    have hd : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    dsimp only [t]
    nlinarith
  have htlt : ∀ n, t n < a := by
    intro n
    dsimp only [t]
    have : 0 < a * (1 / ((n : ℝ) + 1)) := by positivity
    linarith
  have htm : Monotone t := by
    intro n m hnm
    have hd : (1 : ℝ) / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 1)
    dsimp only [t]
    nlinarith
  have htlim : Tendsto t atTop (𝓝 a) := by
    have hconst : Tendsto (fun _ : ℕ => a) atTop (𝓝 a) := tendsto_const_nhds
    have h := hconst.sub (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul a)
    simpa only [mul_zero, sub_zero] using h
  let A : ℕ → Set α := fun n => {x | t n < f x}
  have hAm : Antitone A := fun n m hnm x hx => (htm hnm).trans_lt hx
  have hAnull : ∀ n, NullMeasurableSet (A n) μ := fun n =>
    nullMeasurableSet_lt aemeasurable_const hf.aemeasurable
  have hAone : μ (A 1) ≠ ∞ := by
    apply (hf.measure_gt_lt_top (ε := t 1) ?_).ne
    dsimp [t]
    nlinarith
  have hAeq : (⋂ n, A n) = {x | a ≤ f x} := by
    ext x
    simp only [mem_iInter, A, mem_setOf_eq]
    constructor
    · intro hx
      exact le_of_tendsto' htlim (fun n => (hx n).le)
    · intro hx n
      exact (htlt n).trans_le hx
  rw [← hAeq, hAm.measure_iInter hAnull ⟨1, hAone⟩]
  apply le_iInf
  intro n
  exact ((decreasingProfile_superlevel_iff hf (htnonneg n) hs).mp (htlt n)).le

end FourthRatio
end
