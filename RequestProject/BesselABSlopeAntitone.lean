module

public import RequestProject.BesselABRiccati
public import RequestProject.LevelCrossing
public import Mathlib.Analysis.Convex.Mul

/-! # Decreasing logarithmic slope of the Ashbaugh--Benguria profile -/

@[expose] public section

open Set

noncomputable section

namespace FourthRatio

lemma abRiccati_convex {ν c : ℝ} (hν : 0 ≤ ν) (hc : c ∈ Icc 0 1) :
    ConvexOn ℝ (Ioo 0 1) (abRiccati ν c) := by
  let j := besselZero ν 1
  let k := besselZero (ν + 1) 1
  have hj : 0 < j := (besselZero_props hν).1
  let scale : ℝ → ℝ →ₗ[ℝ] ℝ := fun z =>
    { toFun := fun x => z * x
      map_add' := fun x y => mul_add z x y
      map_smul' := fun a x => by simp only [smul_eq_mul, RingHom.id_apply]; ring }
  have hs : Convex ℝ (Ioo (0 : ℝ) 1) := convex_Ioo _ _
  have hlin := (scale (j ^ 2 - k ^ 2)).convexOn hs
  have hinv : ConvexOn ℝ (Ioo 0 1) (fun t : ℝ => t⁻¹) := by
    simpa only [zpow_neg_one] using
      ((convexOn_zpow (-1 : ℤ) : ConvexOn ℝ (Ioi 0) (fun t : ℝ => t ^ (-1 : ℤ))).subset
        Ioo_subset_Ioi_self hs)
  have hpre := (besselOrderRatio_strictConvexOn hν).convexOn.comp_linearMap (scale j)
  have hY : ConvexOn ℝ (Ioo 0 1) (fun t => besselOrderRatio ν (j * t)) := by
    refine (hpre.subset ?_ hs).congr ?_
    · intro t ht
      change j * t ∈ Ico 0 j
      refine ⟨mul_nonneg hj.le ht.1.le, ?_⟩
      simpa only [mul_one] using mul_lt_mul_of_pos_left ht.2 hj
    · intro t _
      rfl
  have hcoef : 0 ≤ (1 - c) * (c + (2 * ν + 1)) :=
    mul_nonneg (sub_nonneg.mpr hc.2) (by linarith [hc.1])
  have hcoefY : 0 ≤ 2 * j * c := mul_nonneg (by positivity) hc.1
  refine ((hlin.add (hinv.smul hcoef)).add (hY.smul hcoefY)).congr ?_
  intro t _
  change (j ^ 2 - k ^ 2) * t + ((1 - c) * (c + (2 * ν + 1))) * t⁻¹ +
    (2 * j * c) * besselOrderRatio ν (j * t) = abRiccati ν c t
  dsimp only [abRiccati, j, k]
  rw [div_eq_mul_inv]

theorem abLogSlope_deriv_nonpos {ν : ℝ} (hν : 0 ≤ ν) {t : ℝ} (ht : t ∈ Ioo 0 1) :
    deriv (abLogSlope ν) t ≤ 0 := by
  exact nonpos_deriv_of_convex_ode (abLogSlope_continuous hν) (abLogSlope_zero ν)
    (abLogSlope_one hν)
    (fun s hs => (hasDerivAt_abLogSlope hν hs).differentiableAt.hasDerivAt)
    (fun s hs => abLogSlope_mem_Icc hν hs)
    (fun s hs => (hasDerivAt_abLogSlope hν hs).deriv)
    (fun c hc => abRiccati_convex hν hc) t ht

end FourthRatio

end
