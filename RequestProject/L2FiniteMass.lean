module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Continuity of L¹ mass on finite sets for L² functions -/

@[expose] public section
open Set Filter MeasureTheory Topology
open scoped RealInnerProductSpace ENNReal
noncomputable section
namespace FourthRatio

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]

/-- Taking the pointwise norm is a continuous operation on L². -/
def normL2 (f : Lp E 2 μ) : Lp ℝ 2 μ :=
  lipschitzWith_one_norm.compLp (by simp) f

lemma normL2_ae (f : Lp E 2 μ) :
    (normL2 f : α → ℝ) =ᵐ[μ] fun x => ‖(f : α → E) x‖ :=
  lipschitzWith_one_norm.coeFn_compLp (by simp) f

lemma continuous_normL2 : Continuous (normL2 : Lp E 2 μ → Lp ℝ 2 μ) :=
  lipschitzWith_one_norm.continuous_compLp (by simp)

lemma setIntegral_norm_eq_inner_normL2 {A : Set α} (hA : MeasurableSet A) (hfin : μ A ≠ ∞)
    (f : Lp E 2 μ) :
    (∫ x in A, ‖(f : α → E) x‖ ∂μ) =
      ⟪normL2 f, indicatorConstLp 2 hA hfin (1 : ℝ)⟫ := by
  rw [L2.inner_def, ← integral_indicator hA]
  apply integral_congr_ae
  filter_upwards [normL2_ae f, indicatorConstLp_coeFn (p := 2) (hs := hA) (hμs := hfin) (c := (1 : ℝ))]
    with x hx hy
  rw [hx, hy]
  by_cases ha : x ∈ A <;> simp [ha, RCLike.inner_apply, conj_trivial]

/-- Integrating the pointwise norm on a finite measurable set is continuous in L². -/
theorem continuous_setIntegral_norm_L2 {A : Set α} (hA : MeasurableSet A) (hfin : μ A ≠ ∞) :
    Continuous (fun f : Lp E 2 μ => ∫ x in A, ‖(f : α → E) x‖ ∂μ) := by
  have h : Continuous (fun f : Lp E 2 μ =>
      ⟪normL2 f, indicatorConstLp 2 hA hfin (1 : ℝ)⟫) :=
    continuous_normL2.inner continuous_const
  simpa only [← setIntegral_norm_eq_inner_normL2 hA hfin] using h

/-- If all functions vanish outside the same finite set, the total norm integral
is continuous along L² convergence. -/
theorem tendsto_integral_norm_L2_of_support {A : Set α} (hA : MeasurableSet A) (hfin : μ A ≠ ∞)
    {u : ℕ → Lp E 2 μ} {f : Lp E 2 μ} (hlim : Tendsto u atTop (𝓝 f))
    (hu : ∀ n, ∀ᵐ x ∂μ, x ∉ A → (u n : α → E) x = 0)
    (hf : ∀ᵐ x ∂μ, x ∉ A → (f : α → E) x = 0) :
    Tendsto (fun n => ∫ x, ‖(u n : α → E) x‖ ∂μ) atTop
      (𝓝 (∫ x, ‖(f : α → E) x‖ ∂μ)) := by
  have heq : ∀ (g : Lp E 2 μ), (∀ᵐ x ∂μ, x ∉ A → (g : α → E) x = 0) →
      (∫ x in A, ‖(g : α → E) x‖ ∂μ) = ∫ x, ‖(g : α → E) x‖ ∂μ := by
    intro g hg
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [hg] with x hx hxa
    rw [hx hxa, norm_zero]
  have h := (continuous_setIntegral_norm_L2 hA hfin).tendsto f |>.comp hlim
  simpa only [Function.comp_def, heq f hf, fun n => heq (u n) (hu n)] using h

end FourthRatio
end
