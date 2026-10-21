module

public import RequestProject.RadialVolumeMeasure
public import RequestProject.BallVolumeCut

/-! # Exact transport of actual Bessel square-mass integrals -/

@[expose] public section
open Set MeasureTheory Filter Topology Metric
open scoped ENNReal RealInnerProductSpace
noncomputable section
namespace FourthRatio
variable {N : ℕ}

lemma ballVolumeSquareRadius_radialVolume (hN : 2 ≤ N) (x : RN N) :
    ballVolumeSquareRadius N (radialUnitVolume N) (radialVolume N x) = ‖x‖ ^ 2 := by
  have homega := radialUnitVolume_pos hN
  have hNp : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hdiv : radialVolume N x / radialUnitVolume N = ‖x‖ ^ N := by
    dsimp only [radialVolume]
    field_simp [homega.ne']
  dsimp only [ballVolumeSquareRadius]
  rw [hdiv, ← Real.rpow_natCast_mul (norm_nonneg x) N (2 / (N : ℝ))]
  have he : (N : ℝ) * (2 / (N : ℝ)) = 2 := by field_simp [hNp]
  rw [he, Real.rpow_two]

lemma radialVolume_preimage_Iio (hN : 2 ≤ N) {R : ℝ} (hR : 0 < R) :
    (radialVolume N) ⁻¹' Iio (radialUnitVolume N * R ^ N) = ball (0 : RN N) R := by
  have homega := radialUnitVolume_pos hN
  ext x
  change radialUnitVolume N * ‖x‖ ^ N < radialUnitVolume N * R ^ N ↔ dist x 0 < R
  rw [dist_zero_right]
  constructor
  · intro hx
    apply (pow_lt_pow_iff_left₀ (norm_nonneg x) hR.le (show N ≠ 0 by omega)).mp
    exact (mul_lt_mul_iff_right₀ homega).mp (by simpa only [mul_comm] using hx)
  · intro hx
    exact mul_lt_mul_of_pos_left
      ((pow_lt_pow_iff_left₀ (norm_nonneg x) hR.le (show N ≠ 0 by omega)).mpr hx) homega

lemma volume_ball_eq_ofReal_radialVolume (hN : 2 ≤ N) (y : RN N) {R : ℝ} (hR : 0 ≤ R) :
    volume (ball y R) = ENNReal.ofReal (radialUnitVolume N * R ^ N) := by
  haveI : Nontrivial (Fin N) := Fin.nontrivial_iff_two_le.mpr hN
  rw [Measure.addHaar_ball volume y hR]
  simp only [finrank_euclideanSpace, Fintype.card_fin]
  rw [← ENNReal.ofReal_toReal (measure_ball_ne_top : volume (ball (0 : RN N) 1) ≠ ∞),
    ← ENNReal.ofReal_mul (pow_nonneg hR N)]
  congr 1
  change R ^ N * radialUnitVolume N = radialUnitVolume N * R ^ N
  ring

theorem integral_radialVolume_comp (hN : 2 ≤ N) {F : ℝ → ℝ} (hF : Measurable F) :
    (∫ x : RN N, F (radialVolume N x)) = ∫ s in Ioi (0 : ℝ), F s := by
  have h := integral_map_of_stronglyMeasurable (μ := (volume : Measure (RN N)))
    (continuous_radialVolume N).measurable hF.stronglyMeasurable
  rw [map_radialVolume hN] at h
  exact h.symm

/-- Actual Bessel square mass over any measurable radial-volume set. -/
theorem besselEntire_integral_radialVolume (hN : 2 ≤ N) (a : ℝ)
    {A : Set ℝ} (hA : MeasurableSet A) :
    (∫ x in (radialVolume N) ⁻¹' A, besselEntire N a x ^ 2) =
      ∫ s in A ∩ Ioi (0 : ℝ),
        ballVolumeBessel N a (radialUnitVolume N) ((Real.sqrt a / 2) ^ ((N : ℝ) / 2 - 1)) s ^ 2 := by
  let F := fun s => ballVolumeBessel N a (radialUnitVolume N)
    ((Real.sqrt a / 2) ^ ((N : ℝ) / 2 - 1)) s ^ 2
  have hFm : Measurable F := (continuous_ballVolumeBessel hN a (radialUnitVolume N) _).measurable.pow_const 2
  have hpoint : ∀ x : RN N, F (radialVolume N x) = besselEntire N a x ^ 2 := by
    intro x
    exact congrArg (fun t : ℝ => t ^ 2)
      (ballVolumeBessel_eq_besselEntire (ballVolumeSquareRadius_radialVolume hN x).symm)
  rw [← integral_indicator (hA.preimage (continuous_radialVolume N).measurable)]
  have heq : ((radialVolume N) ⁻¹' A).indicator (fun x => besselEntire N a x ^ 2) =
      fun x => (A.indicator F) (radialVolume N x) := by
    funext x
    by_cases hx : radialVolume N x ∈ A
    · have hxpre : x ∈ (radialVolume N) ⁻¹' A := hx
      rw [indicator_of_mem hxpre, indicator_of_mem hx]
      exact (hpoint x).symm
    · have hxpre : x ∉ (radialVolume N) ⁻¹' A := hx
      rw [indicator_of_notMem hxpre, indicator_of_notMem hx]
  rw [heq, integral_radialVolume_comp hN (hFm.indicator hA), integral_indicator hA,
    Measure.restrict_restrict hA]

theorem besselEntire_ball_integral_volume (hN : 2 ≤ N) (a : ℝ) {R : ℝ} (hR : 0 < R) :
    (∫ x in ball (0 : RN N) R, besselEntire N a x ^ 2) =
      ∫ s in Ioo (0 : ℝ) (radialUnitVolume N * R ^ N),
        ballVolumeBessel N a (radialUnitVolume N) ((Real.sqrt a / 2) ^ ((N : ℝ) / 2 - 1)) s ^ 2 := by
  rw [← radialVolume_preimage_Iio hN hR, besselEntire_integral_radialVolume hN a measurableSet_Iio,
    positive_Iio_inter]

/-- Partial ball mass is the cumulative mass of the actual zero-extended model. -/
theorem besselEntire_ball_inter_integral_volume (hN : 2 ≤ N) (a : ℝ)
    {r R : ℝ} (hr : 0 < r) (hR : 0 < R) :
    (∫ x in ball (0 : RN N) r ∩ ball 0 R, besselEntire N a x ^ 2) =
      ∫ s in Iio (radialUnitVolume N * r ^ N),
        ballVolumeCut N a (radialUnitVolume N) ((Real.sqrt a / 2) ^ ((N : ℝ) / 2 - 1))
          (radialUnitVolume N * R ^ N) s ^ 2 ∂volume.restrict (Ioi (0 : ℝ)) := by
  rw [← radialVolume_preimage_Iio hN hr, ← radialVolume_preimage_Iio hN hR,
    ← preimage_inter, besselEntire_integral_radialVolume hN a (measurableSet_Iio.inter measurableSet_Iio)]
  rw [ballVolumeCut_sq_eq, integral_indicator measurableSet_Iio,
    Measure.restrict_restrict measurableSet_Iio,
    Measure.restrict_restrict (measurableSet_Iio.inter measurableSet_Iio)]
  congr 1
  ext s
  simp [and_assoc, and_comm, and_left_comm, min_comm]

end FourthRatio
end
