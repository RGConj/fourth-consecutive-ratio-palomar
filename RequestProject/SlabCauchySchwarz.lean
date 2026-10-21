module

public import RequestProject.L2FiniteMass
public import RequestProject.SobolevTools

/-! # Cauchy--Schwarz on a finite measurable level slab -/

@[expose] public section
open Set MeasureTheory Filter Topology
open scoped RealInnerProductSpace ENNReal
noncomputable section
namespace FourthRatio
variable {N : ℕ}

/-- The L¹ gradient mass squared is at most volume times L² energy, on every
finite measurable set. -/
theorem setIntegral_norm_sq_le_measure_mul {A : Set (RN N)} (hA : MeasurableSet A)
    (hfin : volume A ≠ ∞) (f : L2v N) :
    (∫ x in A, ‖(f : RN N → RN N) x‖) ^ 2 ≤
      volume.real A * ∫ x in A, ‖(f : RN N → RN N) x‖ ^ 2 := by
  let g := indL2v A hA f
  let q := normL2 g
  let χ : L2 N := indicatorConstLp 2 hA hfin (1 : ℝ)
  have hq : ‖q‖ ^ 2 = ∫ x in A, ‖(f : RN N → RN N) x‖ ^ 2 := by
    rw [Lp2_norm_sq_eq, ← integral_indicator hA]
    apply integral_congr_ae
    filter_upwards [normL2_ae g, indL2v_ae A hA f] with x hx hy
    change ‖(q : RN N → ℝ) x‖ ^ 2 = A.indicator (fun x => ‖(f : RN N → RN N) x‖ ^ 2) x
    rw [hx, hy]
    by_cases hxa : x ∈ A <;> simp [hxa]
  have hχ : ‖χ‖ ^ 2 = volume.real A := by
    rw [Lp2_norm_sq_eq]
    have heq : (fun x => ‖(χ : RN N → ℝ) x‖ ^ 2) =ᵐ[volume] A.indicator (fun _ => (1 : ℝ)) := by
      filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hA) (hμs := hfin) (c := (1 : ℝ))] with x hx
      rw [hx]
      by_cases hxa : x ∈ A <;> simp [hxa]
    rw [integral_congr_ae heq, integral_indicator hA]
    simp
  have hmass : ⟪q, χ⟫ = ∫ x in A, ‖(f : RN N → RN N) x‖ := by
    rw [← setIntegral_norm_eq_inner_normL2 hA hfin g]
    apply setIntegral_congr_ae hA
    filter_upwards [indL2v_ae A hA f] with x hx hxa
    rw [hx, indicator_of_mem hxa]
  have hc := abs_real_inner_le_norm q χ
  have hsq : ⟪q, χ⟫ ^ 2 ≤ (‖q‖ * ‖χ‖) ^ 2 := by
    nlinarith [abs_nonneg ⟪q, χ⟫, sq_abs ⟪q, χ⟫, norm_nonneg q, norm_nonneg χ]
  rw [hmass, mul_pow, hq, hχ] at hsq
  exact hsq.trans_eq (mul_comm _ _)

end FourthRatio
end
