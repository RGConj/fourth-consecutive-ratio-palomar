module

public import RequestProject.BesselRecurrence
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! # The actual normalized Bessel series in volume coordinates -/

@[expose] public section
open Set Filter Topology MeasureTheory
noncomputable section
namespace FourthRatio

/-- Moving the eigenvalue parameter into the entire-series argument is an
identity of the actual defining coefficients. -/
theorem besselSeries_parameter_scale (nu a t : ℝ) :
    besselSeries nu a t = besselSeries nu 1 (a * t) := by
  unfold besselSeries
  apply tsum_congr
  intro m
  simp only [besselCoef, mul_pow, div_pow, one_pow]
  ring

lemma hasDerivAt_normalizedSeries {nu : ℝ} (hnu : 0 ≤ nu) (t : ℝ) :
    HasDerivAt (besselSeries nu 1) (besselSeries1 nu t) t := by
  simpa only [besselSeries1] using hasDerivAt_besselSeries hnu zero_le_one t

/-- Squared radius corresponding to volume s for ball-volume constant omega. -/
def ballVolumeSquareRadius (N : ℕ) (omega s : ℝ) : ℝ := (s / omega) ^ (2 / (N : ℝ))

lemma ballVolumeSquareRadius_pos {N : ℕ} {omega s : ℝ} (homega : 0 < omega) (hs : 0 < s) :
    0 < ballVolumeSquareRadius N omega s := Real.rpow_pos_of_pos (div_pos hs homega) _

/-- The true derivative of squared radius in volume coordinates. -/
theorem hasDerivAt_ballVolumeSquareRadius {N : ℕ} {omega s : ℝ}
    (homega : 0 < omega) (hs : 0 < s) :
    HasDerivAt (ballVolumeSquareRadius N omega)
      ((2 / (N : ℝ)) * ballVolumeSquareRadius N omega s / s) s := by
  have hd : HasDerivAt (ballVolumeSquareRadius N omega)
      ((1 / omega) * (2 / (N : ℝ)) * (s / omega) ^ (2 / (N : ℝ) - 1)) s := by
    change HasDerivAt (fun t : ℝ => (t / omega) ^ (2 / (N : ℝ)))
      ((1 / omega) * (2 / (N : ℝ)) * (s / omega) ^ (2 / (N : ℝ) - 1)) s
    simpa only [id_eq] using
      ((hasDerivAt_id s).div_const omega).rpow_const (Or.inl (div_pos hs homega).ne')
  apply hd.congr_deriv
  dsimp only [ballVolumeSquareRadius]
  rw [Real.rpow_sub_one (div_pos hs homega).ne']
  field_simp [hs.ne', homega.ne']

/-- The volume-coordinate square radius is genuinely continuous at zero. -/
theorem tendsto_ballVolumeSquareRadius_zero {N : ℕ} (hN : 0 < N)
    {omega : ℝ} (homega : 0 < omega) :
    Tendsto (ballVolumeSquareRadius N omega) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hNp : 0 < (N : ℝ) := by exact_mod_cast hN
  have he : 0 < 2 / (N : ℝ) := by positivity
  have hc : Continuous (ballVolumeSquareRadius N omega) :=
    (Real.continuous_rpow_const he.le).comp (continuous_id.div_const omega)
  have hz : ballVolumeSquareRadius N omega 0 = 0 := by
    simp only [ballVolumeSquareRadius, zero_div, Real.zero_rpow he.ne']
  have ht := (hc.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  rwa [hz] at ht

end FourthRatio
end
