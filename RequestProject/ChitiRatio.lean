module

public import RequestProject.ACVolterraComparison
public import RequestProject.TalentiDerivative
public import RequestProject.TalentiLocalLipschitz
public import RequestProject.InitialMassAC
public import RequestProject.BallVolumeKernel
public import RequestProject.BallVolumeEndpoint
public import RequestProject.BallVolumePositive
public import RequestProject.BallVolumeRegular

/-! # Actual eigenfunction/ball ratio monotonicity

Every comparison hypothesis is derived for the actual weak eigenfunction,
constructed decreasing quantile, and actual Bessel ball model.
-/

@[expose] public section
open Set MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace FourthRatio
variable {N : ℕ}

theorem eigen_profile_ball_ratio_monotone (hN : 2 ≤ N)
    {D : Set (RN N)} (hD : MeasurableSet D) (hfin : volume D ≠ ∞)
    {p : Amb N} {lam c : ℝ} (hp : IsEigenfunction D p lam) (hlam : 0 < lam)
    (hp0 : ∀ᵐ x, 0 ≤ (p.1 : RN N → ℝ) x) (hc : 0 < c) :
    MonotoneOn (fun s => decreasingProfile volume (p.1 : RN N → ℝ) s /
      ballVolumeBessel N lam (volume.real (ball (0 : RN N) 1)) c s)
      (Ioo 0 (ballVolumeLimit N lam (volume.real (ball (0 : RN N) 1)))) := by
  let omega := volume.real (ball (0 : RN N) 1)
  let u := decreasingProfile volume (p.1 : RN N → ℝ)
  let z := ballVolumeBessel N lam omega c
  let Z := ballVolumeBesselFlux N lam omega c
  let k := ballVolumeKernel N lam omega
  let S := ballVolumeLimit N lam omega
  haveI : Nontrivial (Fin N) := Fin.nontrivial_iff_two_le.mpr hN
  have homega : 0 < omega :=
    ENNReal.toReal_pos (measure_ball_pos volume (0 : RN N) (by norm_num)).ne' measure_ball_ne_top
  have hpi := (integrable_components_of_mem_H hD hfin hp.1).1
  have hfi : IntegrableOn u (Ioi (0 : ℝ)) := decreasingProfile_integrableOn_ae hpi hp0
  have hfc : ∀ s > 0, ContinuousAt u s := by
    intro s hs
    obtain ⟨C, hLip⟩ := eigen_profile_lipschitzOn_from hN hD hfin hp hlam.le hp0 (half_pos hs)
    exact hLip.continuousOn.continuousAt (Ici_mem_nhds (half_lt_self hs))
  have hTal := talenti_derivative_bound_ae hN hD hfin hp hlam.le hp0
  change MonotoneOn (fun s => u s / z s) (Ioo 0 S)
  refine ac_volterra_quotient_monotone (u := u) (z := z) (U := initialMass u) (Z := Z)
    (u1 := deriv u) (z1 := fun s => -(k s * Z s)) (k := k)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · filter_upwards [hTal] with s ht hs
    exact (ht hs.1).1
  · exact Eventually.of_forall fun s hs => hasDerivAt_ballVolumeBessel hN homega hs.1
  · exact Eventually.of_forall fun s hs => initialMass_hasDerivAt hfi
      (decreasingProfile_measurable volume (p.1 : RN N → ℝ)) hs.1 (hfc s hs.1)
  · exact Eventually.of_forall fun s hs => hasDerivAt_ballVolumeBesselFlux hN homega hs.1
  · intro x hx y hy
    have hu := eigen_profile_locally_absolutelyContinuous hN hD hfin hp hlam.le hp0 hx.1 hy.1
    have hZ := ballVolumeBesselFlux_absolutelyContinuous hN (a := lam) (c := c) homega hx.1 hy.1
    have hU := initialMass_absolutelyContinuous hfi hx.1.le hy.1.le
    have hz := ballVolumeBessel_absolutelyContinuous hN (a := lam) (c := c) homega hx.1 hy.1
    exact AbsolutelyContinuousOnInterval.fun_sub
      (AbsolutelyContinuousOnInterval.fun_mul hu hZ) (AbsolutelyContinuousOnInterval.fun_mul hU hz)
  · intro x hx y hy
    have hzInv : ∀ s ∈ uIcc x y, z s ≠ 0 := by
      intro s hs
      have hs0 : 0 < s := (lt_min hx.1 hy.1).trans_le hs.1
      have hsS : s < S := hs.2.trans_lt (max_lt hx.2 hy.2)
      exact (ballVolumeBessel_pos hN hlam homega hc hs0 hsS).ne'
    have hi := ballVolumeBessel_inv_absolutelyContinuous hN (a := lam) (c := c) homega hx.1 hy.1 hzInv
    have hu := eigen_profile_locally_absolutelyContinuous hN hD hfin hp hlam.le hp0 hx.1 hy.1
    simpa only [one_div, div_eq_mul_inv, one_mul] using AbsolutelyContinuousOnInterval.fun_mul hu hi
  · exact decreasingProfile_ball_wronskian_zero hpi hp0 hN homega
  · intro s hs
    change 0 ≤ lam * ballVolumeSquareRadius N omega s / ((N : ℝ) ^ 2 * s ^ 2)
    exact div_nonneg (mul_nonneg hlam.le (ballVolumeSquareRadius_pos homega hs.1).le) (by positivity)
  · intro s hs
    exact ballVolumeBesselFlux_nonneg hN hlam homega hc hs.1 hs.2
  · intro s hs
    exact ballVolumeBessel_pos hN hlam homega hc hs.1 hs.2
  · filter_upwards [hTal] with s ht hs
    have hb := (ht hs.1).2
    change -(ballVolumeKernel N lam omega s * initialMass u s) ≤ deriv u s
    rw [ballVolumeKernel_eq_talenti (show 0 < N by omega) homega hs.1]
    convert hb using 1 <;> ring
  · exact Eventually.of_forall fun _ _ => rfl

end FourthRatio
end
