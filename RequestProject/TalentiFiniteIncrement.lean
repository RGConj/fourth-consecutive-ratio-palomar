module

public import RequestProject.QuantileSlabGradient
public import RequestProject.SlabCauchySchwarz
public import RequestProject.QuantileSlabVolume
public import RequestProject.QuantileAE

/-! # Finite-increment Talenti comparison for the actual weak eigenfunction

The proof combines the actual H₀¹ clip test, sharp level-volume Sobolev,
Cauchy–Schwarz and the constructed decreasing quantile.
-/

@[expose] public section
open Set MeasureTheory Filter Topology Metric
open scoped ENNReal RealInnerProductSpace
noncomputable section
namespace FourthRatio
variable {N : ℕ}

theorem talenti_finite_increment (hN : 2 ≤ N)
    {D : Set (RN N)} (hD : MeasurableSet D) (hfin : volume D ≠ ∞)
    {p : Amb N} {lam : ℝ} (hp : IsEigenfunction D p lam) (hlam : 0 ≤ lam)
    (hp0 : ∀ᵐ x, 0 ≤ (p.1 : RN N → ℝ) x)
    {s₁ s₂ : ℝ} (hs₁ : 0 < s₁) (hs₁₂ : s₁ < s₂)
    (hq : decreasingProfile volume (p.1 : RN N → ℝ) s₂ <
      decreasingProfile volume (p.1 : RN N → ℝ) s₁) :
    decreasingProfile volume (p.1 : RN N → ℝ) s₁ -
      decreasingProfile volume (p.1 : RN N → ℝ) s₂ ≤
      lam * (s₂ - s₁) * (∫ t in Ioo (0 : ℝ) s₂, decreasingProfile volume (p.1 : RN N → ℝ) t) /
        ((N : ℝ) * s₁ ^ (1 - (N : ℝ)⁻¹) *
          volume.real (ball (0 : RN N) 1) ^ (N : ℝ)⁻¹) ^ 2 := by
  let a := decreasingProfile volume (p.1 : RN N → ℝ) s₂
  let b := decreasingProfile volume (p.1 : RN N → ℝ) s₁
  let h := b - a
  let δ := s₂ - s₁
  let K := (N : ℝ) * s₁ ^ (1 - (N : ℝ)⁻¹) * volume.real (ball (0 : RN N) 1) ^ (N : ℝ)⁻¹
  let U := ∫ t in Ioo (0 : ℝ) s₂, decreasingProfile volume (p.1 : RN N → ℝ) t
  let A := eigenSlab p a b
  let L := ∫ x in A, ‖(p.2 : RN N → RN N) x‖
  let E := ∫ x in A, ‖(p.2 : RN N → RN N) x‖ ^ 2
  have hs₂ : 0 < s₂ := hs₁.trans hs₁₂
  have ha : 0 ≤ a := decreasingProfile_nonneg _ _ _
  have hb : 0 ≤ b := decreasingProfile_nonneg _ _ _
  have hh : 0 < h := sub_pos.mpr hq
  have hδ : 0 < δ := sub_pos.mpr hs₁₂
  have hpi := (integrable_components_of_mem_H hD hfin hp.1).1
  have hAm : MeasurableSet A := measurableSet_eigenSlab p a b
  have hvol : volume A ≤ ENNReal.ofReal δ := quantile_slab_volume_le hpi hs₁ hs₂ hq
  have hAfin : volume A ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hvol
  have hvreal : volume.real A ≤ δ := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hvol
    simpa only [ENNReal.toReal_ofReal hδ.le, ← measureReal_def] using h
  have hL : 0 ≤ L := integral_nonneg (fun x => norm_nonneg ((p.2 : RN N → RN N) x))
  have hE : 0 ≤ E := integral_nonneg (fun x => sq_nonneg ‖(p.2 : RN N → RN N) x‖)
  have hU : 0 ≤ U := integral_nonneg (decreasingProfile_nonneg _ _)
  haveI : Nontrivial (Fin N) := Fin.nontrivial_iff_two_le.mpr hN
  have hω : 0 < volume.real (ball (0 : RN N) 1) :=
    ENNReal.toReal_pos (measure_ball_pos volume (0 : RN N) (by norm_num)).ne' measure_ball_ne_top
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hK : 0 < K := mul_pos (mul_pos hNpos (Real.rpow_pos_of_pos hs₁ _)) (Real.rpow_pos_of_pos hω _)
  have hgrad : h * K ≤ L := quantile_slab_gradient_bound hN hD hfin hp.1 hs₁ hs₂ hq
  have hgradSq : (h * K) ^ 2 ≤ L ^ 2 :=
    (sq_le_sq₀ (mul_nonneg hh.le hK.le) hL).mpr hgrad
  have hCS : L ^ 2 ≤ volume.real A * E := setIntegral_norm_sq_le_measure_mul hAm hAfin p.2
  have htail := quantile_tail_mass_le_ae hpi (Lp.stronglyMeasurable p.1).measurable hp0 hs₂
  have henergy : E ≤ lam * (h * U) := by
    apply (eigen_slab_energy_le hp hlam hpi hp0 a b ha hb hq.le).trans
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htail hh.le) hlam
  have hchain : (h * K) ^ 2 ≤ δ * (lam * (h * U)) := calc
    _ ≤ L ^ 2 := hgradSq
    _ ≤ volume.real A * E := hCS
    _ ≤ δ * E := mul_le_mul_of_nonneg_right hvreal hE
    _ ≤ _ := mul_le_mul_of_nonneg_left henergy hδ.le
  have hcancel : h * K ^ 2 ≤ lam * δ * U := by
    apply (mul_le_mul_iff_right₀ hh).mp
    convert hchain using 1 <;> ring
  change h ≤ lam * δ * U / K ^ 2
  exact (le_div_iff₀ (sq_pos_of_pos hK)).mpr hcancel

end FourthRatio
end
