module

public import RequestProject.BallVolumeODE

/-! # Equality of the actual ball and Talenti coefficients -/

@[expose] public section
open Set MeasureTheory Filter Topology
noncomputable section
namespace FourthRatio

/-- The ball's volume-coordinate ODE coefficient is exactly the sharp
coefficient obtained from the actual Sobolev/quantile estimate. -/
theorem ballVolumeKernel_eq_talenti {N : ℕ} (hN : 0 < N)
    {a omega s : ℝ} (homega : 0 < omega) (hs : 0 < s) :
    ballVolumeKernel N a omega s =
      a / ((N : ℝ) * s ^ (1 - (N : ℝ)⁻¹) * omega ^ (N : ℝ)⁻¹) ^ 2 := by
  have hNp : 0 < (N : ℝ) := by exact_mod_cast hN
  let B := (s / omega) ^ (N : ℝ)⁻¹
  let K := (N : ℝ) * s ^ (1 - (N : ℝ)⁻¹) * omega ^ (N : ℝ)⁻¹
  have hB : 0 < B := Real.rpow_pos_of_pos (div_pos hs homega) _
  have hK : 0 < K := mul_pos (mul_pos hNp (Real.rpow_pos_of_pos hs _)) (Real.rpow_pos_of_pos homega _)
  have hrho : ballVolumeSquareRadius N omega s = B ^ 2 := by
    dsimp only [ballVolumeSquareRadius, B]
    rw [← Real.rpow_mul_natCast (div_pos hs homega).le (N : ℝ)⁻¹ 2]
    congr 1
    norm_num <;> ring
  have hBK : B * K = (N : ℝ) * s := by
    dsimp only [B, K]
    rw [Real.div_rpow hs.le homega.le, Real.rpow_sub hs 1 (N : ℝ)⁻¹, Real.rpow_one]
    field_simp [(Real.rpow_pos_of_pos hs (N : ℝ)⁻¹).ne',
      (Real.rpow_pos_of_pos homega (N : ℝ)⁻¹).ne'] <;> ring
  have hprod : ballVolumeSquareRadius N omega s * K ^ 2 = (N : ℝ) ^ 2 * s ^ 2 := by
    rw [hrho, ← mul_pow, hBK, mul_pow]
  change a * ballVolumeSquareRadius N omega s / ((N : ℝ) ^ 2 * s ^ 2) = a / K ^ 2
  apply (div_eq_div_iff (mul_ne_zero (pow_ne_zero 2 hNp.ne') (pow_ne_zero 2 hs.ne'))
    (pow_ne_zero 2 hK.ne')).mpr
  calc
    a * ballVolumeSquareRadius N omega s * K ^ 2 =
        a * (ballVolumeSquareRadius N omega s * K ^ 2) := by ring
    _ = a * ((N : ℝ) ^ 2 * s ^ 2) := congrArg (a * ·) hprod

end FourthRatio
end
