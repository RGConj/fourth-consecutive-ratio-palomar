module

public import RequestProject.BallVolumeODE
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

/-! # Actual local regularity of the ball density and flux -/

@[expose] public section
open Set MeasureTheory Filter Topology
noncomputable section
namespace FourthRatio

lemma contDiffAt_ballVolumeSquareRadius {N : ℕ} {omega s : ℝ}
    (homega : 0 < omega) (hs : 0 < s) :
    ContDiffAt ℝ 1 (ballVolumeSquareRadius N omega) s := by
  change ContDiffAt ℝ 1 (fun t : ℝ => (t / omega) ^ (2 / (N : ℝ))) s
  simpa only [id_eq] using
    (contDiffAt_id.div_const omega).rpow_const_of_ne (div_pos hs homega).ne'

lemma contDiffAt_ballVolumeBessel {N : ℕ} (hN : 2 ≤ N)
    {a omega c s : ℝ} (homega : 0 < omega) (hs : 0 < s) :
    ContDiffAt ℝ 1 (ballVolumeBessel N a omega c) s := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hnu : 0 ≤ (N : ℝ) / 2 - 1 := by linarith
  have harg : ContDiffAt ℝ 1 (fun t : ℝ => a * ballVolumeSquareRadius N omega t) s :=
    ContDiffAt.mul contDiffAt_const (contDiffAt_ballVolumeSquareRadius homega hs)
  have hser : ContDiffAt ℝ 1 (fun t : ℝ =>
      besselSeries ((N : ℝ) / 2 - 1) 1 (a * ballVolumeSquareRadius N omega t)) s := by
    simpa only [Function.comp_def] using
      (analyticAt_besselSeries hnu zero_le_one (a * ballVolumeSquareRadius N omega s)).contDiffAt.comp s harg
  change ContDiffAt ℝ 1 (fun t : ℝ => c *
    besselSeries ((N : ℝ) / 2 - 1) 1 (a * ballVolumeSquareRadius N omega t)) s
  exact ContDiffAt.mul contDiffAt_const hser

lemma contDiffAt_ballVolumeBesselFlux {N : ℕ} (hN : 2 ≤ N)
    {a omega c s : ℝ} (homega : 0 < omega) (hs : 0 < s) :
    ContDiffAt ℝ 1 (ballVolumeBesselFlux N a omega c) s := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hnu : 0 ≤ ((N : ℝ) / 2 - 1) + 1 := by linarith
  have harg : ContDiffAt ℝ 1 (fun t : ℝ => a * ballVolumeSquareRadius N omega t) s :=
    ContDiffAt.mul contDiffAt_const (contDiffAt_ballVolumeSquareRadius homega hs)
  have hser : ContDiffAt ℝ 1 (fun t : ℝ =>
      besselSeries (((N : ℝ) / 2 - 1) + 1) 1 (a * ballVolumeSquareRadius N omega t)) s := by
    simpa only [Function.comp_def] using
      (analyticAt_besselSeries hnu zero_le_one (a * ballVolumeSquareRadius N omega s)).contDiffAt.comp s harg
  have hlin : ContDiffAt ℝ 1 (fun t : ℝ => ((N : ℝ) / 2) * c * t) s :=
    ContDiffAt.mul contDiffAt_const contDiffAt_id
  change ContDiffAt ℝ 1 (fun t : ℝ => ((N : ℝ) / 2) * c * t *
    besselSeries (((N : ℝ) / 2 - 1) + 1) 1 (a * ballVolumeSquareRadius N omega t)) s
  exact ContDiffAt.mul hlin hser

theorem ballVolumeBessel_absolutelyContinuous {N : ℕ} (hN : 2 ≤ N)
    {a omega c x y : ℝ} (homega : 0 < omega) (hx : 0 < x) (hy : 0 < y) :
    AbsolutelyContinuousOnInterval (ballVolumeBessel N a omega c) x y := by
  apply ContDiffOn.absolutelyContinuousOnInterval
  intro s hs
  have hs0 : 0 < s := (lt_min hx hy).trans_le hs.1
  exact (contDiffAt_ballVolumeBessel hN homega hs0).contDiffWithinAt

theorem ballVolumeBesselFlux_absolutelyContinuous {N : ℕ} (hN : 2 ≤ N)
    {a omega c x y : ℝ} (homega : 0 < omega) (hx : 0 < x) (hy : 0 < y) :
    AbsolutelyContinuousOnInterval (ballVolumeBesselFlux N a omega c) x y := by
  apply ContDiffOn.absolutelyContinuousOnInterval
  intro s hs
  have hs0 : 0 < s := (lt_min hx hy).trans_le hs.1
  exact (contDiffAt_ballVolumeBesselFlux hN homega hs0).contDiffWithinAt

theorem ballVolumeBessel_inv_absolutelyContinuous {N : ℕ} (hN : 2 ≤ N)
    {a omega c x y : ℝ} (homega : 0 < omega) (hx : 0 < x) (hy : 0 < y)
    (hz : ∀ s ∈ uIcc x y, ballVolumeBessel N a omega c s ≠ 0) :
    AbsolutelyContinuousOnInterval (fun s => 1 / ballVolumeBessel N a omega c s) x y := by
  apply ContDiffOn.absolutelyContinuousOnInterval
  intro s hs
  have hs0 : 0 < s := (lt_min hx hy).trans_le hs.1
  exact (ContDiffAt.fun_div contDiffAt_const (contDiffAt_ballVolumeBessel hN homega hs0) (hz s hs)).contDiffWithinAt

end FourthRatio
end
