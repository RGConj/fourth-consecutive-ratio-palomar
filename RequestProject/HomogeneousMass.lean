module

public import RequestProject.MassFromRatio
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Homogeneous square-mass comparison, with normalization proved explicitly -/

@[expose] public section
open Set MeasureTheory Filter
noncomputable section
namespace FourthRatio

theorem cumulative_sq_homogeneous_of_ratio_monotone {mu : Measure ℝ}
    {f g : ℝ → ℝ} {R : ℝ} (hR : 0 < R) (hmu : ∀ᵐ s ∂mu, 0 < s)
    (hf : Integrable (fun s => f s ^ 2) mu) (hg : Integrable (fun s => g s ^ 2) mu)
    (hgpos : 0 < ∫ s, g s ^ 2 ∂mu)
    (hf0 : ∀ s > 0, 0 ≤ f s) (hgp : ∀ s ∈ Ioo 0 R, 0 < g s)
    (hgz : ∀ s, R ≤ s → g s = 0)
    (hratio : MonotoneOn (fun s => f s / g s) (Ioo 0 R)) (r : ℝ) :
    (∫ s in Iio r, f s ^ 2 ∂mu) * (∫ s, g s ^ 2 ∂mu) ≤
      (∫ s in Iio r, g s ^ 2 ∂mu) * (∫ s, f s ^ 2 ∂mu) := by
  let F := ∫ s, f s ^ 2 ∂mu
  let G := ∫ s, g s ^ 2 ∂mu
  have hF : 0 ≤ F := integral_nonneg (fun s => sq_nonneg (f s))
  have hG : 0 < G := hgpos
  by_cases hFp : 0 < F
  · let q := Real.sqrt (F / G)
    have hq : 0 < q := Real.sqrt_pos.mpr (div_pos hFp hG)
    have hq2 : q ^ 2 * G = F := by
      rw [Real.sq_sqrt (div_nonneg hF hG.le), div_mul_cancel₀ _ hG.ne']
    let zg : ℝ → ℝ := fun s => q * g s
    have hint : Integrable (fun s => zg s ^ 2) mu := by
      apply (hg.const_mul (q ^ 2)).congr
      exact Eventually.of_forall fun s => by dsimp only [zg]; ring
    have heq : F = ∫ s, zg s ^ 2 ∂mu := by
      have he : (∫ s, zg s ^ 2 ∂mu) = q ^ 2 * G := by
        change (∫ s, (q * g s) ^ 2 ∂mu) = q ^ 2 * G
        simp only [mul_pow, integral_const_mul, G]
      rw [he, hq2]
    have hratioq : MonotoneOn (fun s => f s / zg s) (Ioo 0 R) := by
      intro s hs t ht hst
      have hm := mul_le_mul_of_nonneg_left (hratio hs ht hst) (inv_nonneg.mpr hq.le)
      have he : ∀ s ∈ Ioo 0 R, f s / zg s = q⁻¹ * (f s / g s) := by
        intro u hu
        dsimp only [zg]
        field_simp [hq.ne', (hgp u hu).ne']
      change f s / zg s ≤ f t / zg t
      rw [he s hs, he t ht]
      exact hm
    have hcmp := cumulative_sq_le_of_ratio_monotone hR hmu hf hint heq hf0
      (fun s hs => mul_pos hq (hgp s hs))
      (fun s hs => by dsimp only [zg]; rw [hgz s hs, mul_zero]) hratioq r
    have hpart : (∫ s in Iio r, zg s ^ 2 ∂mu) = q ^ 2 * ∫ s in Iio r, g s ^ 2 ∂mu := by
      change (∫ s in Iio r, (q * g s) ^ 2 ∂mu) = _
      simp only [mul_pow, integral_const_mul]
    rw [hpart] at hcmp
    have hscaled := mul_le_mul_of_nonneg_right hcmp hG.le
    change (∫ s in Iio r, f s ^ 2 ∂mu) * G ≤ (∫ s in Iio r, g s ^ 2 ∂mu) * F
    calc
      _ ≤ (q ^ 2 * ∫ s in Iio r, g s ^ 2 ∂mu) * G := hscaled
      _ = (∫ s in Iio r, g s ^ 2 ∂mu) * (q ^ 2 * G) := by ring
      _ = _ := by rw [hq2]
  · have hF0 : F = 0 := le_antisymm (not_lt.mp hFp) hF
    have hpart : (∫ s in Iio r, f s ^ 2 ∂mu) ≤ F :=
      setIntegral_le_integral hf (Eventually.of_forall (fun s => sq_nonneg (f s)))
    change (∫ s in Iio r, f s ^ 2 ∂mu) * G ≤ (∫ s in Iio r, g s ^ 2 ∂mu) * F
    rw [hF0, mul_zero]
    rw [hF0] at hpart
    exact mul_nonpos_of_nonpos_of_nonneg hpart hG.le

end FourthRatio
end
