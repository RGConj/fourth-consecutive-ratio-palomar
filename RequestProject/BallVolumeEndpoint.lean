module

public import RequestProject.BallVolumeODE
public import RequestProject.ProfileEndpoint

/-! # Genuine endpoint matching of the actual rearrangement and ball model -/

@[expose] public section
open Set MeasureTheory Filter Topology
noncomputable section
namespace FourthRatio

theorem tendsto_ballVolumeBessel_zero {N : ℕ} (hN : 2 ≤ N)
    {a omega c : ℝ} (homega : 0 < omega) :
    Tendsto (ballVolumeBessel N a omega c) (𝓝[>] (0 : ℝ))
      (𝓝 (c * (Real.Gamma (((N : ℝ) / 2 - 1) + 1))⁻¹)) := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hnu : 0 ≤ (N : ℝ) / 2 - 1 := by linarith
  have hr := tendsto_ballVolumeSquareRadius_zero (show 0 < N by omega) homega
  have harg : Tendsto (fun s => a * ballVolumeSquareRadius N omega s) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [mul_zero] using hr.const_mul a
  have hF := (hasDerivAt_normalizedSeries hnu 0).continuousAt.tendsto.comp harg
  change Tendsto (fun s : ℝ => c * besselSeries ((N : ℝ) / 2 - 1) 1
    (a * ballVolumeSquareRadius N omega s)) (𝓝[>] 0) _
  simpa only [Function.comp_def, besselSeries_zero] using hF.const_mul c

theorem tendsto_ballVolumeBesselFlux_div_zero {N : ℕ} (hN : 2 ≤ N)
    {a omega c : ℝ} (homega : 0 < omega) :
    Tendsto (fun s => ballVolumeBesselFlux N a omega c s / s) (𝓝[>] (0 : ℝ))
      (𝓝 ((((N : ℝ) / 2) * c) * (Real.Gamma ((((N : ℝ) / 2 - 1) + 1) + 1))⁻¹)) := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hnu : 0 ≤ ((N : ℝ) / 2 - 1) + 1 := by linarith
  have hr := tendsto_ballVolumeSquareRadius_zero (show 0 < N by omega) homega
  have harg : Tendsto (fun s => a * ballVolumeSquareRadius N omega s) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [mul_zero] using hr.const_mul a
  have hF := (hasDerivAt_normalizedSeries hnu 0).continuousAt.tendsto.comp harg
  have hlim : Tendsto (fun s => (((N : ℝ) / 2) * c) *
      besselSeries (((N : ℝ) / 2 - 1) + 1) 1 (a * ballVolumeSquareRadius N omega s))
      (𝓝[>] (0 : ℝ))
      (𝓝 ((((N : ℝ) / 2) * c) * (Real.Gamma ((((N : ℝ) / 2 - 1) + 1) + 1))⁻¹)) := by
    simpa only [Function.comp_def, besselSeries_zero] using hF.const_mul (((N : ℝ) / 2) * c)
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  dsimp only [ballVolumeBesselFlux]
  field_simp [hs.ne']

/-- The actual model Wronskian tends to zero without imposing a finite value
on the potentially singular decreasing eigenfunction profile at zero. -/
theorem decreasingProfile_ball_wronskian_zero {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : Integrable f μ) (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x)
    {N : ℕ} (hN : 2 ≤ N) {a omega c : ℝ} (homega : 0 < omega) :
    Tendsto (fun s => decreasingProfile μ f s * ballVolumeBesselFlux N a omega c s -
      initialMass (decreasingProfile μ f) s * ballVolumeBessel N a omega c s)
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  tendsto_wronskian_zero (decreasingProfile_integrableOn_ae hf hf0)
    (fun s _ => decreasingProfile_nonneg μ f s) (decreasingProfile_antitoneOn hf)
    (tendsto_ballVolumeBessel_zero hN homega) (tendsto_ballVolumeBesselFlux_div_zero hN homega)

end FourthRatio
end
