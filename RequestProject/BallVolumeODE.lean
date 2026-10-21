module

public import RequestProject.BallVolumeBasic

/-! # Actual ball Bessel density and flux in volume coordinates -/

@[expose] public section
open Set Filter Topology MeasureTheory
noncomputable section
namespace FourthRatio

def ballVolumeBessel (N : ℕ) (a omega c s : ℝ) : ℝ :=
  c * besselSeries ((N : ℝ) / 2 - 1) 1 (a * ballVolumeSquareRadius N omega s)

def ballVolumeBesselFlux (N : ℕ) (a omega c s : ℝ) : ℝ :=
  ((N : ℝ) / 2) * c * s *
    besselSeries (((N : ℝ) / 2 - 1) + 1) 1 (a * ballVolumeSquareRadius N omega s)

def ballVolumeKernel (N : ℕ) (a omega s : ℝ) : ℝ :=
  a * ballVolumeSquareRadius N omega s / ((N : ℝ) ^ 2 * s ^ 2)

/-- This volume profile is the actual besselEntire profile, evaluated at the
corresponding squared radius. -/
theorem ballVolumeBessel_eq_besselEntire {N : ℕ} {a omega s : ℝ} {x : RN N}
    (hx : ‖x‖ ^ 2 = ballVolumeSquareRadius N omega s) :
    ballVolumeBessel N a omega ((Real.sqrt a / 2) ^ ((N : ℝ) / 2 - 1)) s = besselEntire N a x := by
  dsimp only [ballVolumeBessel, besselEntire]
  rw [besselSeries_parameter_scale ((N : ℝ) / 2 - 1) a (‖x‖ ^ 2), hx]

/-- The ball density solves the same Volterra differential relation as the
Talenti comparison, with an explicit flux. -/
theorem hasDerivAt_ballVolumeBessel {N : ℕ} (hN : 2 ≤ N)
    {a omega c s : ℝ} (homega : 0 < omega) (hs : 0 < s) :
    HasDerivAt (ballVolumeBessel N a omega c)
      (-(ballVolumeKernel N a omega s * ballVolumeBesselFlux N a omega c s)) s := by
  have hNreal : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hnu : 0 ≤ (N : ℝ) / 2 - 1 := by linarith
  have hNp : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  let r := ballVolumeSquareRadius N omega s
  have hd : HasDerivAt (ballVolumeBessel N a omega c)
      (c * (besselSeries1 ((N : ℝ) / 2 - 1) (a * r) *
        (a * ((2 / (N : ℝ)) * r / s)))) s := by
    change HasDerivAt (fun t : ℝ => c * besselSeries ((N : ℝ) / 2 - 1) 1
      (a * ballVolumeSquareRadius N omega t)) _ s
    simpa only [Function.comp_def, r] using
      ((hasDerivAt_normalizedSeries hnu (a * r)).comp s
        ((hasDerivAt_ballVolumeSquareRadius homega hs).const_mul a)).const_mul c
  apply hd.congr_deriv
  rw [besselSeries1_succ hnu]
  dsimp only [ballVolumeKernel, ballVolumeBesselFlux, r]
  field_simp [hNp, hs.ne']
  <;> ring

/-- The explicit flux differentiates to the actual ball density. -/
theorem hasDerivAt_ballVolumeBesselFlux {N : ℕ} (hN : 2 ≤ N)
    {a omega c s : ℝ} (homega : 0 < omega) (hs : 0 < s) :
    HasDerivAt (ballVolumeBesselFlux N a omega c) (ballVolumeBessel N a omega c s) s := by
  have hNreal : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hnu : 0 ≤ (N : ℝ) / 2 - 1 := by linarith
  have hnu1 : 0 ≤ ((N : ℝ) / 2 - 1) + 1 := by linarith
  have hNp : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  let r := ballVolumeSquareRadius N omega s
  have hlin : HasDerivAt (fun t : ℝ => (((N : ℝ) / 2) * c) * t) (((N : ℝ) / 2) * c) s := by
    simpa only [mul_one, id_eq] using (hasDerivAt_id s).const_mul (((N : ℝ) / 2) * c)
  have hser := (hasDerivAt_normalizedSeries hnu1 (a * r)).comp s
    ((hasDerivAt_ballVolumeSquareRadius homega hs).const_mul a)
  have hd : HasDerivAt (ballVolumeBesselFlux N a omega c)
      ((((N : ℝ) / 2) * c) * besselSeries (((N : ℝ) / 2 - 1) + 1) 1 (a * r) +
        ((((N : ℝ) / 2) * c) * s) * (besselSeries1 (((N : ℝ) / 2 - 1) + 1) (a * r) *
          (a * ((2 / (N : ℝ)) * r / s)))) s := by
    change HasDerivAt (fun t : ℝ => ((N : ℝ) / 2) * c * t *
      besselSeries (((N : ℝ) / 2 - 1) + 1) 1 (a * ballVolumeSquareRadius N omega t)) _ s
    simpa only [Function.comp_def, Pi.mul_apply, r] using hlin.fun_mul hser
  apply hd.congr_deriv
  dsimp only [ballVolumeBessel]
  rw [← besselSeries_succ_rel hnu (a * r)]
  dsimp only [r]
  field_simp [hNp, hs.ne']
  <;> ring

/-- The flux has its genuine zero limit at the volume endpoint. -/
theorem tendsto_ballVolumeBesselFlux_zero {N : ℕ} (hN : 2 ≤ N)
    {a omega c : ℝ} (homega : 0 < omega) :
    Tendsto (ballVolumeBesselFlux N a omega c) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hNreal : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hnu1 : 0 ≤ ((N : ℝ) / 2 - 1) + 1 := by linarith
  have hr := tendsto_ballVolumeSquareRadius_zero (show 0 < N by omega) homega
  have harg : Tendsto (fun s => a * ballVolumeSquareRadius N omega s) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [mul_zero] using hr.const_mul a
  have hF := (hasDerivAt_normalizedSeries hnu1 0).continuousAt.tendsto.comp harg
  have hs : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hprod := (hs.mul hF).const_mul (((N : ℝ) / 2) * c)
  change Tendsto (fun s : ℝ => ((N : ℝ) / 2) * c * s *
    besselSeries (((N : ℝ) / 2 - 1) + 1) 1 (a * ballVolumeSquareRadius N omega s)) (𝓝[>] 0) (𝓝 0)
  simpa only [Function.comp_def, zero_mul, mul_zero, mul_assoc] using hprod

end FourthRatio
end
