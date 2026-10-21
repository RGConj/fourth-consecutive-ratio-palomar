module

public import RequestProject.TalentiFiniteIncrement
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

/-! # Local Lipschitz regularity of the actual eigenfunction rearrangement -/

@[expose] public section
open Set MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace FourthRatio
variable {N : ℕ}

/-- The finite-increment estimate makes the constructed profile Lipschitz on
every half-line bounded away from the zero-volume endpoint. -/
theorem eigen_profile_lipschitzOn_from (hN : 2 ≤ N)
    {D : Set (RN N)} (hD : MeasurableSet D) (hfin : volume D ≠ ∞)
    {p : Amb N} {lam : ℝ} (hp : IsEigenfunction D p lam) (hlam : 0 ≤ lam)
    (hp0 : ∀ᵐ x, 0 ≤ (p.1 : RN N → ℝ) x) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ≥0, LipschitzOnWith C (decreasingProfile volume (p.1 : RN N → ℝ)) (Ici ε) := by
  let f := decreasingProfile volume (p.1 : RN N → ℝ)
  have hpi := (integrable_components_of_mem_H hD hfin hp.1).1
  have hfi : IntegrableOn f (Ioi (0 : ℝ)) := decreasingProfile_integrableOn_ae hpi hp0
  let M := ∫ s in Ioi (0 : ℝ), f s
  have hM : 0 ≤ M := integral_nonneg (decreasingProfile_nonneg _ _)
  haveI : Nontrivial (Fin N) := Fin.nontrivial_iff_two_le.mpr hN
  have hω : 0 < volume.real (ball (0 : RN N) 1) :=
    ENNReal.toReal_pos (measure_ball_pos volume (0 : RN N) (by norm_num)).ne' measure_ball_ne_top
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hN1 : 1 < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have he : 0 ≤ 1 - (N : ℝ)⁻¹ := by
    have := (inv_lt_one₀ hNpos).mpr hN1
    linarith
  let K : ℝ → ℝ := fun s => (N : ℝ) * s ^ (1 - (N : ℝ)⁻¹) *
    volume.real (ball (0 : RN N) 1) ^ (N : ℝ)⁻¹
  have hKε : 0 < K ε := mul_pos (mul_pos hNpos (Real.rpow_pos_of_pos hε _)) (Real.rpow_pos_of_pos hω _)
  have hKm : ∀ x, ε ≤ x → K ε ≤ K x := by
    intro x hx
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hε.le hx he) hNpos.le)
      (Real.rpow_pos_of_pos hω _).le
  let C := lam * M / K ε ^ 2
  have hC : 0 ≤ C := div_nonneg (mul_nonneg hlam hM) (sq_nonneg _)
  have hanti : AntitoneOn f (Ioi 0) := decreasingProfile_antitoneOn hpi
  have hordered : ∀ x ∈ Ici ε, ∀ y ∈ Ici ε, x ≤ y → f x - f y ≤ C * (y - x) := by
    intro x hx y hy hxy
    have hxpos : 0 < x := hε.trans_le hx
    have hypos : 0 < y := hε.trans_le hy
    have hfyx : f y ≤ f x := hanti hxpos hypos hxy
    by_cases heq : f x = f y
    · rw [heq, sub_self]
      exact mul_nonneg hC (sub_nonneg.mpr hxy)
    have hgt : f y < f x := lt_of_le_of_ne hfyx (Ne.symm heq)
    have hxylt : x < y := lt_of_le_of_ne hxy (by intro h; subst y; exact heq rfl)
    have htal := talenti_finite_increment hN hD hfin hp hlam hp0 hxpos hxylt hgt
    have hU : (∫ t in Ioo (0 : ℝ) y, f t) ≤ M :=
      setIntegral_mono_set hfi (Eventually.of_forall (decreasingProfile_nonneg _ _))
        (Eventually.of_forall fun t ht => ht.1)
    have hden : K ε ^ 2 ≤ K x ^ 2 :=
      (sq_le_sq₀ hKε.le (hKε.le.trans (hKm x hx))).mpr (hKm x hx)
    calc
      _ ≤ lam * (y - x) * (∫ t in Ioo (0 : ℝ) y, f t) / K x ^ 2 := htal
      _ ≤ lam * (y - x) * M / K ε ^ 2 :=
        div_le_div₀ (mul_nonneg (mul_nonneg hlam (sub_nonneg.mpr hxy)) hM)
          (mul_le_mul_of_nonneg_left hU (mul_nonneg hlam (sub_nonneg.mpr hxy)))
          (sq_pos_of_pos hKε) hden
      _ = C * (y - x) := by dsimp only [C]; ring
  refine ⟨⟨C, hC⟩, LipschitzOnWith.of_dist_le_mul ?_⟩
  intro x hx y hy
  change dist (f x) (f y) ≤ C * dist x y
  rcases le_total x y with hxy | hyx
  · have hq : 0 ≤ f x - f y := sub_nonneg.mpr (hanti (hε.trans_le hx) (hε.trans_le hy) hxy)
    rw [Real.dist_eq, abs_of_nonneg hq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxy), neg_sub]
    exact hordered x hx y hy hxy
  · rw [dist_comm (f x) (f y), dist_comm x y]
    have hq : 0 ≤ f y - f x := sub_nonneg.mpr (hanti (hε.trans_le hy) (hε.trans_le hx) hyx)
    rw [Real.dist_eq, abs_of_nonneg hq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hyx), neg_sub]
    exact hordered y hy x hx hyx

/-- Actual local absolute continuity, required by the proved Volterra criterion. -/
theorem eigen_profile_locally_absolutelyContinuous (hN : 2 ≤ N)
    {D : Set (RN N)} (hD : MeasurableSet D) (hfin : volume D ≠ ∞)
    {p : Amb N} {lam : ℝ} (hp : IsEigenfunction D p lam) (hlam : 0 ≤ lam)
    (hp0 : ∀ᵐ x, 0 ≤ (p.1 : RN N → ℝ) x)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    AbsolutelyContinuousOnInterval (decreasingProfile volume (p.1 : RN N → ℝ)) a b := by
  obtain ⟨C, hC⟩ := eigen_profile_lipschitzOn_from hN hD hfin hp hlam hp0 (lt_min ha hb)
  apply LipschitzOnWith.absolutelyContinuousOnInterval (K := C)
  exact hC.mono fun s hs => hs.1

end FourthRatio
end
