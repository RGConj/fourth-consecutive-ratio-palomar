module

public import RequestProject.InitialMass
public import RequestProject.QuantileAE

/-! # Genuine zero-volume endpoint limits for the actual rearrangement -/

@[expose] public section
open Set MeasureTheory Filter Topology
noncomputable section
namespace FourthRatio

theorem tendsto_initialMass_zero {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi (0 : ℝ))) :
    Tendsto (initialMass f) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hg := hf.integrable_indicator measurableSet_Ioi
  have ht : Tendsto (fun s => ∫ t in (0 : ℝ)..s, (Ioi (0 : ℝ)).indicator f t)
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [intervalIntegral.integral_same] using
      ((hg.continuous_primitive 0).tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (initialMass_eq_primitive f hs.le).symm

/-- An antitone density cannot carry more than its initial-interval average. -/
theorem mul_le_initialMass_of_antitone {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi (0 : ℝ)))
    (hanti : AntitoneOn f (Ioi 0)) {s : ℝ} (hs : 0 < s) :
    s * f s ≤ initialMass f s := by
  have hconst : IntegrableOn (fun _ : ℝ => f s) (Ioo (0 : ℝ) s) :=
    integrableOn_const (by simp)
  have hfi := hf.mono_set (show Ioo (0 : ℝ) s ⊆ Ioi 0 from fun t ht => ht.1)
  have hle : (∫ t in Ioo (0 : ℝ) s, f s) ≤ ∫ t in Ioo (0 : ℝ) s, f t := by
    apply integral_mono_ae hconst hfi
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact hanti ht.1 hs ht.2.le
  have hleft : (∫ t in Ioo (0 : ℝ) s, f s) = s * f s := by
    simp [measureReal_def, Real.volume_Ioo, hs.le]
  rwa [hleft] at hle

/-- The potentially unbounded density has the true s*f(s) -> 0 endpoint limit. -/
theorem tendsto_mul_density_zero {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi (0 : ℝ)))
    (hf0 : ∀ s > 0, 0 ≤ f s) (hanti : AntitoneOn f (Ioi 0)) :
    Tendsto (fun s : ℝ => s * f s) (𝓝[>] 0) (𝓝 0) := by
  have hlo : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 ≤ s * f s := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact mul_nonneg hs.le (hf0 s hs)
  have hhi : ∀ᶠ s in 𝓝[>] (0 : ℝ), s * f s ≤ initialMass f s := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact mul_le_initialMass_of_antitone hf hanti hs
  exact squeeze_zero' hlo hhi (tendsto_initialMass_zero hf)

/-- This endpoint limit applies to the actual decreasing profile, without an
assumed boundedness or a finite pointwise value at zero. -/
theorem decreasingProfile_mul_tendsto_zero {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : Integrable f μ) (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x) :
    Tendsto (fun s : ℝ => s * decreasingProfile μ f s) (𝓝[>] 0) (𝓝 0) :=
  tendsto_mul_density_zero (decreasingProfile_integrableOn_ae hf hf0)
    (fun s _ => decreasingProfile_nonneg μ f s) (decreasingProfile_antitoneOn hf)

/-- The Volterra Wronskian has a true zero limit when the model density is
bounded at zero and its model flux has a finite first-order limit. -/
theorem tendsto_wronskian_zero {u z Z : ℝ → ℝ} {z₀ Z₁ : ℝ}
    (hu : IntegrableOn u (Ioi (0 : ℝ))) (hu0 : ∀ s > 0, 0 ≤ u s)
    (hum : AntitoneOn u (Ioi 0)) (hz : Tendsto z (𝓝[>] (0 : ℝ)) (𝓝 z₀))
    (hZ : Tendsto (fun s => Z s / s) (𝓝[>] (0 : ℝ)) (𝓝 Z₁)) :
    Tendsto (fun s => u s * Z s - initialMass u s * z s) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hfirst := (tendsto_mul_density_zero hu hu0 hum).mul hZ
  have hsecond := (tendsto_initialMass_zero hu).mul hz
  have hlim : Tendsto (fun s => (s * u s) * (Z s / s) - initialMass u s * z s)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [zero_mul, sub_zero] using hfirst.sub hsecond
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  field_simp [hs.ne']

end FourthRatio
end
