module

public import RequestProject.ChitiCumulative
public import RequestProject.RadialVolumeIntegrals

/-! # Actual ball-mass concentration for nonnegative weak eigenfunctions -/

@[expose] public section
open Set MeasureTheory Filter Topology Metric
open scoped ENNReal RealInnerProductSpace
noncomputable section
namespace FourthRatio
variable {N : ℕ}

theorem eigenfunction_ball_mass_nonnegative (hN : 2 ≤ N)
    {D : Set (RN N)} (hD : MeasurableSet D) (hfin : volume D ≠ ∞)
    {p : Amb N} {lam : ℝ} (hp : IsEigenfunction D p lam) (hlam : 0 < lam)
    (hp0 : ∀ᵐ x, 0 ≤ (p.1 : RN N → ℝ) x) (center : RN N) (r : ℝ) :
    (∫ x in ball center r, (p.1 : RN N → ℝ) x ^ 2) *
        (∫ x in ball (0 : RN N) (besselZero ((N : ℝ) / 2 - 1) 1 / Real.sqrt lam),
          besselEntire N lam x ^ 2) ≤
      (∫ x in ball (0 : RN N) r ∩ ball 0 (besselZero ((N : ℝ) / 2 - 1) 1 / Real.sqrt lam),
        besselEntire N lam x ^ 2) * ∫ x, (p.1 : RN N → ℝ) x ^ 2 := by
  rcases le_or_gt r 0 with hr | hr
  · have hb : ball center r = ∅ := ball_eq_empty.mpr hr
    have hb0 : ball (0 : RN N) r = ∅ := ball_eq_empty.mpr hr
    simp [hb, hb0]
  let omega := radialUnitVolume N
  let R := besselZero ((N : ℝ) / 2 - 1) 1 / Real.sqrt lam
  let c := (Real.sqrt lam / 2) ^ ((N : ℝ) / 2 - 1)
  let m := omega * r ^ N
  let S := ballVolumeLimit N lam omega
  let g := eigenBallVolumeModel N lam c
  let u := decreasingProfile volume (p.1 : RN N → ℝ)
  let mu := volume.restrict (Ioi (0 : ℝ))
  have homega : 0 < omega := radialUnitVolume_pos hN
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hnu : 0 ≤ (N : ℝ) / 2 - 1 := by linarith
  have hR : 0 < R := div_pos (besselZero_props hnu).1 (Real.sqrt_pos.mpr hlam)
  have hc : 0 < c := Real.rpow_pos_of_pos (div_pos (Real.sqrt_pos.mpr hlam) (by norm_num)) _
  have hpi := (integrable_components_of_mem_H hD hfin hp.1).1
  have hpsq : Integrable (fun x => (p.1 : RN N → ℝ) x ^ 2) volume := (Lp.memLp p.1).integrable_sq
  have hHL := setIntegral_sq_le_profile_initial_ae hpi (Lp.stronglyMeasurable p.1).measurable hp0 hpsq
    (A := ball center r) measurableSet_ball
    (m := m) (by rw [volume_ball_eq_ofReal_radialVolume hN center hr.le])
  have hcoord : (∫ s in Iio m, u s ^ 2 ∂mu) = ∫ s in Ioo (0 : ℝ) m, u s ^ 2 := by
    change (∫ s, u s ^ 2 ∂((volume.restrict (Ioi (0 : ℝ))).restrict (Iio m))) = _
    rw [Measure.restrict_restrict measurableSet_Iio, positive_Iio_inter]
  have hGtotal : (∫ s, g s ^ 2 ∂mu) = ∫ x in ball (0 : RN N) R, besselEntire N lam x ^ 2 := by
    change (∫ s, ballVolumeCut N lam omega c S s ^ 2 ∂mu) = _
    rw [integral_sq_ballVolumeCut hN lam omega c S]
    exact (besselEntire_ball_integral_volume hN lam hR).symm
  have hGpartial : (∫ s in Iio m, g s ^ 2 ∂mu) =
      ∫ x in ball (0 : RN N) r ∩ ball 0 R, besselEntire N lam x ^ 2 := by
    exact (besselEntire_ball_inter_integral_volume hN lam hr hR).symm
  have hcmp := eigen_profile_cumulative_homogeneous hN hD hfin hp hlam hp0 hc m
  rw [hGtotal, hGpartial] at hcmp
  have hGnonneg : 0 ≤ ∫ x in ball (0 : RN N) R, besselEntire N lam x ^ 2 :=
    integral_nonneg (fun x => sq_nonneg (besselEntire N lam x))
  have hHLP : (∫ x in ball center r, (p.1 : RN N → ℝ) x ^ 2) ≤ ∫ s in Iio m, u s ^ 2 ∂mu := by
    rw [hcoord]
    exact hHL
  exact (mul_le_mul_of_nonneg_right hHLP hGnonneg).trans hcmp

end FourthRatio
end
