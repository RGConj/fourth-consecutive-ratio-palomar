module

public import RequestProject.BallVolumePositive
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! # Integrability and nonzero mass of the actual truncated ball model -/

@[expose] public section
open Set MeasureTheory Filter Topology
open scoped ENNReal
noncomputable section
namespace FourthRatio

lemma continuous_ballVolumeBessel {N : ℕ} (hN : 2 ≤ N) (a omega c : ℝ) :
    Continuous (ballVolumeBessel N a omega c) := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hnu : 0 ≤ (N : ℝ) / 2 - 1 := by linarith
  have he : 0 ≤ 2 / (N : ℝ) := by positivity
  have hr : Continuous (ballVolumeSquareRadius N omega) :=
    (Real.continuous_rpow_const he).comp (continuous_id.div_const omega)
  have hF : Continuous (besselSeries ((N : ℝ) / 2 - 1) 1) :=
    continuous_iff_continuousAt.mpr fun s => (analyticAt_besselSeries hnu zero_le_one s).continuousAt
  change Continuous (fun s : ℝ => c * besselSeries ((N : ℝ) / 2 - 1) 1 (a * ballVolumeSquareRadius N omega s))
  exact continuous_const.mul (hF.comp (continuous_const.mul hr))

def ballVolumeCut (N : ℕ) (a omega c S : ℝ) : ℝ → ℝ :=
  (Iio S).indicator (ballVolumeBessel N a omega c)

lemma measurable_ballVolumeCut {N : ℕ} (hN : 2 ≤ N) (a omega c S : ℝ) :
    Measurable (ballVolumeCut N a omega c S) :=
  (continuous_ballVolumeBessel hN a omega c).measurable.indicator measurableSet_Iio

lemma ballVolumeCut_sq_eq (N : ℕ) (a omega c S : ℝ) :
    (fun s => ballVolumeCut N a omega c S s ^ 2) =
      (Iio S).indicator (fun s => ballVolumeBessel N a omega c s ^ 2) := by
  funext s
  by_cases hs : s < S <;> simp [ballVolumeCut, hs]

lemma positive_Iio_inter (S : ℝ) : Iio S ∩ Ioi (0 : ℝ) = Ioo 0 S := by
  ext s
  simp [and_comm]

theorem integrable_sq_ballVolumeCut {N : ℕ} (hN : 2 ≤ N) (a omega c S : ℝ) :
    Integrable (fun s => ballVolumeCut N a omega c S s ^ 2) (volume.restrict (Ioi (0 : ℝ))) := by
  rw [ballVolumeCut_sq_eq, integrable_indicator_iff measurableSet_Iio]
  change Integrable (fun s => ballVolumeBessel N a omega c s ^ 2)
    ((volume.restrict (Ioi (0 : ℝ))).restrict (Iio S))
  rw [Measure.restrict_restrict measurableSet_Iio, positive_Iio_inter]
  exact ((continuous_ballVolumeBessel hN a omega c).pow 2).continuousOn.integrableOn_compact
    (isCompact_Icc (a := (0 : ℝ)) (b := S)) |>.mono_set (fun s hs => ⟨hs.1.le, hs.2.le⟩)

theorem integral_sq_ballVolumeCut {N : ℕ} (hN : 2 ≤ N) (a omega c S : ℝ) :
    (∫ s, ballVolumeCut N a omega c S s ^ 2 ∂volume.restrict (Ioi (0 : ℝ))) =
      ∫ s in Ioo (0 : ℝ) S, ballVolumeBessel N a omega c s ^ 2 := by
  rw [ballVolumeCut_sq_eq, integral_indicator measurableSet_Iio,
    Measure.restrict_restrict measurableSet_Iio, positive_Iio_inter]

lemma ballVolumeLimit_pos {N : ℕ} (hN : 2 ≤ N) {a omega : ℝ}
    (ha : 0 < a) (homega : 0 < omega) : 0 < ballVolumeLimit N a omega := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hnu : 0 ≤ (N : ℝ) / 2 - 1 := by linarith
  exact mul_pos homega (pow_pos (div_pos (besselZero_props hnu).1 (Real.sqrt_pos.mpr ha)) _)

theorem integral_sq_ballVolumeCut_pos {N : ℕ} (hN : 2 ≤ N) {a omega c : ℝ}
    (ha : 0 < a) (homega : 0 < omega) (hc : 0 < c) :
    0 < ∫ s, ballVolumeCut N a omega c (ballVolumeLimit N a omega) s ^ 2
      ∂volume.restrict (Ioi (0 : ℝ)) := by
  let S := ballVolumeLimit N a omega
  apply (integral_pos_iff_support_of_nonneg (fun s => sq_nonneg _) (integrable_sq_ballVolumeCut hN a omega c S)).mpr
  have hsub : Ioo (0 : ℝ) S ⊆ Function.support (fun s => ballVolumeCut N a omega c S s ^ 2) := by
    intro s hs
    have hpos : 0 < ballVolumeCut N a omega c S s ^ 2 := by
      rw [ballVolumeCut, indicator_of_mem hs.2]
      exact pow_pos (ballVolumeBessel_pos hN ha homega hc hs.1 hs.2) 2
    exact hpos.ne'
  have hvol : 0 < (volume.restrict (Ioi (0 : ℝ))) (Ioo (0 : ℝ) S) := by
    rw [Measure.restrict_apply measurableSet_Ioo, inter_eq_left.mpr (show Ioo (0 : ℝ) S ⊆ Ioi 0 from fun s hs => hs.1),
      Real.volume_Ioo, sub_zero, ENNReal.ofReal_pos]
    exact ballVolumeLimit_pos hN ha homega
  exact lt_of_lt_of_le hvol (measure_mono hsub)

end FourthRatio
end
