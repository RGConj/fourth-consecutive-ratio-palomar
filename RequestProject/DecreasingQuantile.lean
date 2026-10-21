module

public import RequestProject.RearrangementMass
public import Mathlib.MeasureTheory.Measure.Continuity
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# A concrete decreasing rearrangement in volume coordinates

The quantile is defined by a countable supremum of rational superlevels.
Measurability, antitonicity and its exact superlevel characterization are
proved from that definition, not included as assumed rearrangement properties.
-/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace FourthRatio

/-- The decreasing quantile of a real density, in the volume coordinate s.
Only its values at positive s are used for Schwarz rearrangement. -/
def decreasingQuantile {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) (s : ℝ) : ℝ≥0∞ :=
  ⨆ q : ℚ, if ENNReal.ofReal s < μ {x | (q : ℝ) < f x}
    then ENNReal.ofReal (q : ℝ) else 0

theorem decreasingQuantile_antitone {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) : Antitone (decreasingQuantile μ f) := by
  intro s t hst
  unfold decreasingQuantile
  apply iSup_le
  intro q
  by_cases hqt : ENNReal.ofReal t < μ {x | (q : ℝ) < f x}
  · rw [if_pos hqt]
    have hqs : ENNReal.ofReal s < μ {x | (q : ℝ) < f x} :=
      (ENNReal.ofReal_le_ofReal hst).trans_lt hqt
    exact le_iSup_of_le q (by rw [if_pos hqs])
  · rw [if_neg hqt]
    exact bot_le

theorem decreasingQuantile_measurable {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) : Measurable (decreasingQuantile μ f) := by
  unfold decreasingQuantile
  apply Measurable.iSup
  intro q
  exact Measurable.ite
    (measurableSet_lt ENNReal.measurable_ofReal measurable_const)
    measurable_const measurable_const

lemma superlevel_measure_eq_iSup_rat {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) (t : ℝ) :
    μ {x | t < f x} = ⨆ q : ℚ, ⨆ (_ : t < (q : ℝ)), μ {x | (q : ℝ) < f x} := by
  let S : Set ℚ := {q | t < (q : ℝ)}
  have hu : {x | t < f x} = ⋃ q ∈ S, {x | (q : ℝ) < f x} := by
    ext x
    simp only [mem_iUnion, S, Set.mem_ofPred_eq, exists_prop]
    constructor
    · intro hx
      obtain ⟨q, htq, hqf⟩ := exists_rat_btwn hx
      exact ⟨q, htq, hqf⟩
    · rintro ⟨q, htq, hqf⟩
      exact htq.trans hqf
  have hd : DirectedOn (fun a b : ℚ => {x | (a : ℝ) < f x} ⊆ {x | (b : ℝ) < f x}) S := by
    intro a ha b hb
    rcases le_total a b with hab | hba
    · refine ⟨a, ha, subset_rfl, ?_⟩
      intro x hx
      change (b : ℝ) < f x at hx
      have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
      exact hab'.trans_lt hx
    · refine ⟨b, hb, ?_, subset_rfl⟩
      intro x hx
      change (a : ℝ) < f x at hx
      have hba' : (b : ℝ) ≤ (a : ℝ) := by exact_mod_cast hba
      exact hba'.trans_lt hx
  rw [hu]
  exact measure_biUnion_eq_iSup (Set.to_countable S) hd

/-- The exact superlevels of the constructed quantile recover the original
superlevel volumes. No rearrangement axioms are assumed. -/
theorem decreasingQuantile_superlevel_iff {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) {t s : ℝ} (ht : 0 ≤ t) :
    ENNReal.ofReal t < decreasingQuantile μ f s ↔
      ENNReal.ofReal s < μ {x | t < f x} := by
  unfold decreasingQuantile
  rw [lt_iSup_iff]
  constructor
  · rintro ⟨q, hq⟩
    by_cases hcond : ENNReal.ofReal s < μ {x | (q : ℝ) < f x}
    · rw [if_pos hcond] at hq
      have htq : t < (q : ℝ) := (ENNReal.ofReal_lt_ofReal_iff'.mp hq).1
      exact hcond.trans_le (measure_mono (fun x hx => htq.trans hx))
    · simp only [if_neg hcond, not_lt_zero] at hq
  · intro hs
    rw [superlevel_measure_eq_iSup_rat μ f t, lt_iSup_iff] at hs
    obtain ⟨q, hq⟩ := hs
    obtain ⟨htq, hqs⟩ := lt_iSup_iff.mp hq
    refine ⟨q, ?_⟩
    rw [if_pos hqs]
    exact ENNReal.ofReal_lt_ofReal_iff'.mpr ⟨htq, ht.trans_lt htq⟩

end FourthRatio

end
