module

public import RequestProject.Defs

/-!
# Symmetry of radial integrals on `ℝ^N`

For a radial weight `g(|z|)`:
* `∫ g(|z|) ⟨c, z⟩ dz = 0` (invariance under `z ↦ -z`);
* `∫ g(|z|) ⟨c, z⟩² dz = |c|²/N ∫ g(|z|) |z|² dz` (invariance under reflections, and
  `∑ᵢ zᵢ² = |z|²`).

These are the "spherical-harmonic orthogonality" facts used in the separation-of-variables
computation on the annulus.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Function
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

variable {N : ℕ}

/-- Odd moments of a radial weight vanish. -/
lemma integral_radial_mul_inner_eq_zero (g : ℝ → ℝ) (c : RN N) :
    ∫ z : RN N, g ‖z‖ * ⟪c, z⟫ = 0 := by
  have h := integral_neg_eq_self (fun z : RN N => g ‖z‖ * ⟪c, z⟫) volume
  simp only [norm_neg, inner_neg_right, mul_neg, integral_neg] at h
  linarith

/-- The second moment in a unit direction does not depend on the direction. -/
lemma integral_radial_inner_sq_unit (g : ℝ → ℝ) {u w : RN N} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) :
    ∫ z : RN N, g ‖z‖ * ⟪u, z⟫ ^ 2 = ∫ z : RN N, g ‖z‖ * ⟪w, z⟫ ^ 2 := by
  set K : Submodule ℝ (RN N) := (ℝ ∙ (u - w))ᗮ
  have hKu : K.reflection u = w := Submodule.reflection_sub (hu.trans hw.symm)
  have h := MeasureTheory.integral_comp K.reflection (fun z : RN N => g ‖z‖ * ⟪u, z⟫ ^ 2)
  rw [← h]
  congr 1; funext z
  simp only [LinearIsometryEquiv.norm_map]
  congr 2
  rw [← K.reflection.inner_map_map u, Submodule.reflection_reflection, hKu]

lemma integrable_radial_inner_sq {g : ℝ → ℝ}
    (hg : Integrable (fun z : RN N => g ‖z‖ * ‖z‖ ^ 2))
    (hgm : AEStronglyMeasurable (fun z : RN N => g ‖z‖) volume) {u : RN N} (hu : ‖u‖ = 1) :
    Integrable (fun z : RN N => g ‖z‖ * ⟪u, z⟫ ^ 2) := by
  refine hg.mono (hgm.mul (by fun_prop : Continuous fun z : RN N => ⟪u, z⟫ ^ 2).aestronglyMeasurable)
    (Eventually.of_forall fun z => ?_)
  simp only [norm_mul, Real.norm_eq_abs, abs_pow, sq_abs]
  have := abs_real_inner_le_norm u z
  rw [hu, one_mul] at this
  have h2 : ⟪u, z⟫ ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
  exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)

/-- **Second moments of a radial weight.** -/
lemma integral_radial_inner_sq (hN : 1 ≤ N) {g : ℝ → ℝ}
    (hg : Integrable (fun z : RN N => g ‖z‖ * ‖z‖ ^ 2))
    (hgm : AEStronglyMeasurable (fun z : RN N => g ‖z‖) volume) (c : RN N) :
    ∫ z : RN N, g ‖z‖ * ⟪c, z⟫ ^ 2 = ‖c‖ ^ 2 / N * ∫ z : RN N, g ‖z‖ * ‖z‖ ^ 2 := by
  set e : Fin N → RN N := fun i => EuclideanSpace.single i 1
  have he : ∀ i, ‖e i‖ = 1 := fun i => by simp [e]
  have hez : ∀ i (z : RN N), ⟪e i, z⟫ = z i := fun i z => by
    simp [e, EuclideanSpace.inner_single_left]
  have i0 : Fin N := ⟨0, hN⟩
  set Q := ∫ z : RN N, g ‖z‖ * ⟪e i0, z⟫ ^ 2
  have hQ : ∀ i, ∫ z : RN N, g ‖z‖ * ⟪e i, z⟫ ^ 2 = Q := fun i =>
    integral_radial_inner_sq_unit g (he i) (he i0)
  have hsum : (N : ℝ) * Q = ∫ z : RN N, g ‖z‖ * ‖z‖ ^ 2 := by
    have h1 : ∫ z : RN N, ∑ i, g ‖z‖ * ⟪e i, z⟫ ^ 2 = ∑ i, ∫ z : RN N, g ‖z‖ * ⟪e i, z⟫ ^ 2 :=
      integral_finsetSum _ fun i _ => integrable_radial_inner_sq hg hgm (he i)
    simp only [hQ, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
    rw [← h1]
    congr 1; funext z
    rw [← Finset.mul_sum, EuclideanSpace.norm_sq_eq]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hez, Real.norm_eq_abs, sq_abs]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  by_cases hc : c = 0
  · subst hc; simp
  have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hc
  set u : RN N := ‖c‖⁻¹ • c
  have hu : ‖u‖ = 1 := by simp [u, norm_smul, hcn.ne']
  have hcu : ∀ z : RN N, ⟪c, z⟫ = ‖c‖ * ⟪u, z⟫ := fun z => by
    simp [u, inner_smul_left, hcn.ne']
  calc ∫ z : RN N, g ‖z‖ * ⟪c, z⟫ ^ 2 = ∫ z : RN N, ‖c‖ ^ 2 * (g ‖z‖ * ⟪u, z⟫ ^ 2) := by
        congr 1; funext z; rw [hcu]; ring
    _ = ‖c‖ ^ 2 * Q := by
        rw [integral_const_mul, integral_radial_inner_sq_unit g hu (he i0)]
    _ = _ := by rw [← hsum]; field_simp

end FourthRatio

end
