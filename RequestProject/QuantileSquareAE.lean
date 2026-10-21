module

public import RequestProject.QuantileAE
public import RequestProject.QuantileSquareMass

/-! # Square-mass rearrangement for actual a.e. nonnegative representatives -/

@[expose] public section
open Set MeasureTheory Filter
open scoped ENNReal
noncomputable section
namespace FourthRatio

theorem decreasingProfile_sq_lintegral_eq_ae {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : Integrable f μ) (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x) :
    (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (decreasingProfile μ f s ^ 2)) =
      ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μ := by
  have heq : (fun x => max (f x) 0) =ᵐ[μ] f := hf0.mono fun x hx => max_eq_left hx
  have h := decreasingProfile_sq_lintegral_eq hf.pos_part (fun _ => le_max_right _ _)
  rw [decreasingProfile_congr_ae heq] at h
  exact h.trans (lintegral_congr_ae (heq.mono fun x hx =>
    congrArg (fun t : ℝ => ENNReal.ofReal (t ^ 2)) hx))

/-- Hardy–Littlewood square-mass control by the actual decreasing profile.
Null-set sign changes of the chosen L² representative do not affect the result. -/
theorem setLIntegral_sq_le_profile_initial_ae {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : Integrable f μ) (hfm : Measurable f)
    (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x) {A : Set α} (hA : MeasurableSet A)
    {m : ℝ} (hAm : μ A ≤ ENNReal.ofReal m) :
    (∫⁻ x in A, ENNReal.ofReal (f x ^ 2) ∂μ) ≤
      ∫⁻ s in Ioo (0 : ℝ) m, ENNReal.ofReal (decreasingProfile μ f s ^ 2) := by
  let g := rearrangedDensity μ f
  let B : Set ℝ := {s | 0 < s ∧ ENNReal.ofReal s < μ A}
  have hBm : MeasurableSet B := measurableSet_Ioi.inter
    (measurableSet_lt ENNReal.measurable_ofReal measurable_const)
  have hBvol : volume B = μ A := volume_positive_ofReal_lt _
  have hsqrt : ∀ t > 0, ∀ a : ℝ, 0 ≤ a → (t < a ^ 2 ↔ Real.sqrt t < a) := by
    intro t ht a ha
    have hsq := Real.sq_sqrt ht.le
    have hsnon := Real.sqrt_nonneg t
    constructor <;> intro h <;> nlinarith
  have hgset : ∀ t > 0, {s | t < g s ^ 2} =
      {s : ℝ | 0 < s ∧ ENNReal.ofReal s < μ {x | Real.sqrt t < f x}} := by
    intro t ht
    have he : {s | t < g s ^ 2} = {s | Real.sqrt t < g s} := by
      ext s
      exact hsqrt t ht (g s) (rearrangedDensity_nonneg μ f s)
    rw [he]
    exact rearrangedDensity_superlevel hf (Real.sqrt_pos.mpr ht)
  have hequi : ∀ t > 0, μ {x | t < f x ^ 2} = volume {s | t < g s ^ 2} := by
    intro t ht
    have hset : {x | t < f x ^ 2} =ᵐ[μ] {x | Real.sqrt t < f x} := by
      filter_upwards [hf0] with x hx
      change (t < f x ^ 2) = (Real.sqrt t < f x)
      exact propext (hsqrt t ht (f x) hx)
    rw [measure_congr hset, hgset t ht, volume_positive_ofReal_lt]
  have hnested : ∀ t > 0, {s | t < g s ^ 2} ⊆ B ∨ B ⊆ {s | t < g s ^ 2} := by
    intro t ht
    rw [hgset t ht]
    rcases le_total (μ {x | Real.sqrt t < f x}) (μ A) with h | h
    · exact Or.inl (fun s hs => ⟨hs.1, hs.2.trans_le h⟩)
    · exact Or.inr (fun s hs => ⟨hs.1, hs.2.trans_le h⟩)
  have hbound := setLIntegral_le_of_equidistributed_nested (hfm.pow_const 2)
    ((rearrangedDensity_measurable μ f).pow_const 2) (fun x => sq_nonneg (f x))
    (fun s => sq_nonneg (g s)) hA hBm hBvol.symm hequi hnested
  calc
    _ ≤ ∫⁻ s in B, ENNReal.ofReal (g s ^ 2) := hbound
    _ = ∫⁻ s in B, ENNReal.ofReal (decreasingProfile μ f s ^ 2) := by
      apply setLIntegral_congr_fun hBm
      intro s hs
      dsimp only [g, rearrangedDensity]
      rw [indicator_of_mem hs.1]
    _ ≤ _ := by
      have hsub : B ⊆ Ioo (0 : ℝ) m := fun s hs =>
        ⟨hs.1, (ENNReal.ofReal_lt_ofReal_iff'.mp (hs.2.trans_le hAm)).1⟩
      exact lintegral_mono_set hsub

end FourthRatio
end
