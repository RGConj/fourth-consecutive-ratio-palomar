module

public import RequestProject.QuantileTailMass

/-! # Almost-everywhere invariance of the actual rearrangement -/

@[expose] public section
open Set MeasureTheory Filter
open scoped ENNReal
noncomputable section
namespace FourthRatio

/-- Null-set changes of the original representative do not change the quantile. -/
theorem decreasingQuantile_congr_ae {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f g : α → ℝ} (hfg : f =ᵐ[μ] g) :
    decreasingQuantile μ f = decreasingQuantile μ g := by
  funext s
  unfold decreasingQuantile
  apply iSup_congr
  intro q
  have hm : μ {x | (q : ℝ) < f x} = μ {x | (q : ℝ) < g x} := by
    apply measure_congr
    exact hfg.mono fun x hx => by simp only [Set.mem_setOf_eq, hx]
  rw [hm]

theorem decreasingProfile_congr_ae {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f g : α → ℝ} (hfg : f =ᵐ[μ] g) :
    decreasingProfile μ f = decreasingProfile μ g := by
  funext s
  unfold decreasingProfile
  rw [decreasingQuantile_congr_ae hfg]

/-- L¹ profile integrability only needs a.e. nonnegativity of the original. -/
theorem decreasingProfile_integrableOn_ae {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : Integrable f μ) (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x) :
    IntegrableOn (decreasingProfile μ f) (Ioi (0 : ℝ)) := by
  have heq : (fun x => max (f x) 0) =ᵐ[μ] f := hf0.mono fun x hx => max_eq_left hx
  rw [← decreasingProfile_congr_ae heq]
  exact decreasingProfile_integrableOn hf.pos_part (fun _ => le_max_right _ _)

/-- The real initial-coordinate mass bound is independent of the choice of a
nonnegative representative. -/
theorem setIntegral_le_profile_initial_ae {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : Integrable f μ) (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x)
    {A : Set α} (hA : MeasurableSet A) {s : ℝ} (hAs : μ A ≤ ENNReal.ofReal s) :
    (∫ x in A, f x ∂μ) ≤ ∫ t in Ioo (0 : ℝ) s, decreasingProfile μ f t := by
  have heq : (fun x => max (f x) 0) =ᵐ[μ] f := hf0.mono fun x hx => max_eq_left hx
  have h := setIntegral_le_profile_initial hf.pos_part (fun _ => le_max_right _ _) hA hAs
  rw [integral_congr_ae (ae_restrict_of_ae heq), decreasingProfile_congr_ae heq] at h
  exact h

theorem quantile_tail_mass_le_ae {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : Integrable f μ) (hfm : Measurable f)
    (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x) {s : ℝ} (hs : 0 < s) :
    (∫ x in {x | decreasingProfile μ f s < f x}, f x ∂μ) ≤
      ∫ t in Ioo (0 : ℝ) s, decreasingProfile μ f t :=
  setIntegral_le_profile_initial_ae hf hf0 (measurableSet_lt measurable_const hfm)
    (decreasingProfile_strict_tail_le hf hs)

end FourthRatio
end
