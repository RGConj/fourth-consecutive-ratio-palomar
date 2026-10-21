module

public import RequestProject.L2FiniteMass
public import RequestProject.Basic

/-! # Actual L¹ integrability of finite-support L² functions -/

@[expose] public section
open Set MeasureTheory Filter Topology
open scoped RealInnerProductSpace ENNReal
noncomputable section
namespace FourthRatio

/-- The norm of an L² function, restricted to a finite measurable set, is
integrable. The proof realizes it as an actual L² scalar product. -/
theorem integrable_indicator_norm_L2 {α E : Type*} [MeasurableSpace α]
    {μ : Measure α} [NormedAddCommGroup E] {A : Set α}
    (hA : MeasurableSet A) (hfin : μ A ≠ ∞) (f : Lp E 2 μ) :
    Integrable (A.indicator (fun x => ‖(f : α → E) x‖)) μ := by
  have hi := L2.integrable_inner (𝕜 := ℝ) (normL2 f) (indicatorConstLp 2 hA hfin (1 : ℝ))
  apply hi.congr
  filter_upwards [normL2_ae f, indicatorConstLp_coeFn (p := 2) (hs := hA) (hμs := hfin) (c := (1 : ℝ))]
    with x hx hy
  rw [hx, hy]
  by_cases ha : x ∈ A <;> simp [ha, RCLike.inner_apply, conj_trivial]

/-- A finite-support L² representative is a genuinely integrable function. -/
theorem integrable_L2_of_support {α E : Type*} [MeasurableSpace α]
    {μ : Measure α} [NormedAddCommGroup E] {A : Set α}
    (hA : MeasurableSet A) (hfin : μ A ≠ ∞) (f : Lp E 2 μ)
    (hf : ∀ᵐ x ∂μ, x ∉ A → (f : α → E) x = 0) : Integrable (f : α → E) μ := by
  apply (integrable_norm_iff (Lp.aestronglyMeasurable f)).mp
  apply (integrable_indicator_norm_L2 hA hfin f).congr
  filter_upwards [hf] with x hx
  by_cases ha : x ∈ A
  · simp [ha]
  · simp [ha, hx ha]

/-- Both components of an H₀¹ pair are integrable on a finite measurable domain. -/
theorem integrable_components_of_mem_H {N : ℕ} {D : Set (RN N)}
    (hD : MeasurableSet D) (hfin : volume D ≠ ∞) {p : Amb N} (hp : p ∈ H D) :
    Integrable (p.1 : RN N → ℝ) volume ∧ Integrable (p.2 : RN N → RN N) volume := by
  obtain ⟨hf, hg⟩ := mem_vanishOn.mp (H_le_vanishOn D hp)
  rw [EventuallyEq, ae_restrict_iff' hD.compl] at hf hg
  exact ⟨integrable_L2_of_support hD hfin p.1 hf, integrable_L2_of_support hD hfin p.2 hg⟩

end FourthRatio
end
