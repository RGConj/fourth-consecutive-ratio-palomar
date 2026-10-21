module

public import RequestProject.ChitiRatio
public import RequestProject.BallVolumeCut
public import RequestProject.RadialVolumeMeasure
public import RequestProject.QuantileSquareReal
public import RequestProject.HomogeneousMass

/-! # Homogeneous actual eigenfunction/ball cumulative mass comparison -/

@[expose] public section
open Set MeasureTheory Filter Topology Metric
open scoped ENNReal RealInnerProductSpace
noncomputable section
namespace FourthRatio
variable {N : ℕ}

def eigenBallVolumeModel (N : ℕ) (lam c : ℝ) : ℝ → ℝ :=
  ballVolumeCut N lam (radialUnitVolume N) c (ballVolumeLimit N lam (radialUnitVolume N))

theorem eigen_profile_cumulative_homogeneous (hN : 2 ≤ N)
    {D : Set (RN N)} (hD : MeasurableSet D) (hfin : volume D ≠ ∞)
    {p : Amb N} {lam c : ℝ} (hp : IsEigenfunction D p lam) (hlam : 0 < lam)
    (hp0 : ∀ᵐ x, 0 ≤ (p.1 : RN N → ℝ) x) (hc : 0 < c) (m : ℝ) :
    (∫ s in Iio m, decreasingProfile volume (p.1 : RN N → ℝ) s ^ 2 ∂volume.restrict (Ioi (0 : ℝ))) *
        (∫ s, eigenBallVolumeModel N lam c s ^ 2 ∂volume.restrict (Ioi (0 : ℝ))) ≤
      (∫ s in Iio m, eigenBallVolumeModel N lam c s ^ 2 ∂volume.restrict (Ioi (0 : ℝ))) *
        ∫ x, (p.1 : RN N → ℝ) x ^ 2 := by
  let omega := radialUnitVolume N
  let S := ballVolumeLimit N lam omega
  let u := decreasingProfile volume (p.1 : RN N → ℝ)
  let g := eigenBallVolumeModel N lam c
  let mu := volume.restrict (Ioi (0 : ℝ))
  have homega : 0 < omega := radialUnitVolume_pos hN
  have hS : 0 < S := ballVolumeLimit_pos hN hlam homega
  have hpi := (integrable_components_of_mem_H hD hfin hp.1).1
  have hpsq : Integrable (fun x => (p.1 : RN N → ℝ) x ^ 2) volume := (Lp.memLp p.1).integrable_sq
  have hF : Integrable (fun s => u s ^ 2) mu := decreasingProfile_sq_integrable_ae hpi hp0 hpsq
  have hG : Integrable (fun s => g s ^ 2) mu := integrable_sq_ballVolumeCut hN lam omega c S
  have hGpos : 0 < ∫ s, g s ^ 2 ∂mu := integral_sq_ballVolumeCut_pos hN hlam homega hc
  have hgp : ∀ s ∈ Ioo 0 S, 0 < g s := by
    intro s hs
    change 0 < (Iio S).indicator (ballVolumeBessel N lam omega c) s
    rw [indicator_of_mem (show s ∈ Iio S from hs.2)]
    exact ballVolumeBessel_pos hN hlam homega hc hs.1 hs.2
  have hgz : ∀ s, S ≤ s → g s = 0 := by
    intro s hs
    change (Iio S).indicator (ballVolumeBessel N lam omega c) s = 0
    exact indicator_of_notMem (show s ∉ Iio S from not_lt_of_ge hs) _
  have hrraw := eigen_profile_ball_ratio_monotone hN hD hfin hp hlam hp0 hc
  have hratio : MonotoneOn (fun s => u s / g s) (Ioo 0 S) := by
    intro s hs t ht hst
    change u s / ((Iio S).indicator (ballVolumeBessel N lam omega c) s) ≤
      u t / ((Iio S).indicator (ballVolumeBessel N lam omega c) t)
    rw [indicator_of_mem (show s ∈ Iio S from hs.2), indicator_of_mem (show t ∈ Iio S from ht.2)]
    exact hrraw hs ht hst
  have hcmp := cumulative_sq_homogeneous_of_ratio_monotone hS
    (show ∀ᵐ s ∂mu, 0 < s from ae_restrict_mem measurableSet_Ioi)
    hF hG hGpos (fun s _ => decreasingProfile_nonneg _ _ s) hgp hgz hratio m
  have hmass : (∫ s, u s ^ 2 ∂mu) = ∫ x, (p.1 : RN N → ℝ) x ^ 2 :=
    integral_sq_decreasingProfile_eq_ae hpi hp0 hpsq
  rw [hmass] at hcmp
  exact hcmp

end FourthRatio
end
