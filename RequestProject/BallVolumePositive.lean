module

public import RequestProject.BallVolumeODE
public import RequestProject.ACMonotone

/-! # Positivity of the actual ball model on its first-eigenfunction interval -/

@[expose] public section
open Set MeasureTheory Filter Topology
noncomputable section
namespace FourthRatio

def ballVolumeLimit (N : ℕ) (a omega : ℝ) : ℝ :=
  omega * (besselZero ((N : ℝ) / 2 - 1) 1 / Real.sqrt a) ^ N

lemma ballVolumeSquareRadius_lt_radius_sq {N : ℕ} (hN : 0 < N)
    {omega R s : ℝ} (homega : 0 < omega) (hR : 0 < R) (hs : 0 < s)
    (hsR : s < omega * R ^ N) :
    ballVolumeSquareRadius N omega s < R ^ 2 := by
  have hNp : 0 < (N : ℝ) := by exact_mod_cast hN
  have hd : s / omega < R ^ N := (div_lt_iff₀ homega).mpr (by simpa only [mul_comm] using hsR)
  have hrpow := Real.rpow_lt_rpow (div_pos hs homega).le hd (show 0 < 2 / (N : ℝ) by positivity)
  have he : (R ^ N) ^ (2 / (N : ℝ)) = R ^ 2 := by
    rw [← Real.rpow_natCast_mul hR.le N (2 / (N : ℝ))]
    have hmul : (N : ℝ) * (2 / (N : ℝ)) = 2 := by field_simp [hNp.ne']
    rw [hmul, Real.rpow_two]
  exact hrpow.trans_eq he

theorem ballVolumeBessel_pos {N : ℕ} (hN : 2 ≤ N)
    {a omega c s : ℝ} (ha : 0 < a) (homega : 0 < omega) (hc : 0 < c)
    (hs : 0 < s) (hsR : s < ballVolumeLimit N a omega) :
    0 < ballVolumeBessel N a omega c s := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hnu : 0 ≤ (N : ℝ) / 2 - 1 := by linarith
  let j := besselZero ((N : ℝ) / 2 - 1) 1
  let R := j / Real.sqrt a
  have hj : 0 < j := (besselZero_props hnu).1
  have hR : 0 < R := div_pos hj (Real.sqrt_pos.mpr ha)
  have hrho : ballVolumeSquareRadius N omega s < R ^ 2 :=
    ballVolumeSquareRadius_lt_radius_sq (show 0 < N by omega) homega hR hs hsR
  have harg0 : 0 < a * ballVolumeSquareRadius N omega s :=
    mul_pos ha (ballVolumeSquareRadius_pos homega hs)
  have harg : a * ballVolumeSquareRadius N omega s < j ^ 2 := by
    calc
      _ < a * R ^ 2 := mul_lt_mul_of_pos_left hrho ha
      _ = j ^ 2 := by
        dsimp only [R]
        rw [div_pow, Real.sq_sqrt ha.le]
        field_simp [ha.ne']
  have hx : Real.sqrt (a * ballVolumeSquareRadius N omega s) < j := by
    have hsq := Real.sq_sqrt harg0.le
    have hn := Real.sqrt_nonneg (a * ballVolumeSquareRadius N omega s)
    nlinarith
  have hF := besselF_pos_before hnu (Real.sqrt_nonneg (a * ballVolumeSquareRadius N omega s)) hx
  have hser : 0 < besselSeries ((N : ℝ) / 2 - 1) 1 (a * ballVolumeSquareRadius N omega s) := by
    simpa only [besselF, Real.sq_sqrt harg0.le] using hF
  exact mul_pos hc hser

theorem ballVolumeBesselFlux_nonneg {N : ℕ} (hN : 2 ≤ N)
    {a omega c s : ℝ} (ha : 0 < a) (homega : 0 < omega) (hc : 0 < c)
    (hs : 0 < s) (hsR : s < ballVolumeLimit N a omega) :
    0 ≤ ballVolumeBesselFlux N a omega c s := by
  let S := ballVolumeLimit N a omega
  let Z := ballVolumeBesselFlux N a omega c
  have hZd : ∀ t > 0, HasDerivAt Z (ballVolumeBessel N a omega c t) t :=
    fun t ht => hasDerivAt_ballVolumeBesselFlux hN homega ht
  have hZc : ContinuousOn Z (Ioo 0 S) :=
    fun t ht => (hZd t ht.1).continuousAt.continuousWithinAt
  have hZdiff : DifferentiableOn ℝ Z (Ioo 0 S) :=
    fun t ht => (hZd t ht.1).differentiableAt.differentiableWithinAt
  have hZm : MonotoneOn Z (Ioo 0 S) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioo 0 S) hZc (hZdiff.mono interior_subset)
    intro t ht
    have ht' : t ∈ Ioo 0 S := interior_subset ht
    rw [(hZd t ht'.1).deriv]
    exact (ballVolumeBessel_pos hN ha homega hc ht'.1 ht'.2).le
  exact right_limit_le_of_monotoneOn hZm (tendsto_ballVolumeBesselFlux_zero hN homega) ⟨hs, hsR⟩

end FourthRatio
end
