module

public import RequestProject.WronskianSign
public import RequestProject.BesselGap

/-! # A decreasing quotient for radial equations of adjacent dimensions -/

@[expose] public section

open Set

noncomputable section

namespace FourthRatio

lemma radial_quotient_antitone {A A1 A2 C C1 C2 : ℝ → ℝ} {a b d : ℝ}
    (hd : 0 < d)
    (hA : ∀ t, HasDerivAt A (A1 t) t) (hA1 : ∀ t, HasDerivAt A1 (A2 t) t)
    (hC : ∀ t, HasDerivAt C (C1 t) t) (hC1 : ∀ t, HasDerivAt C1 (C2 t) t)
    (hodeA : ∀ t, t * A2 t + d * A1 t + a * t * A t = 0)
    (hodeC : ∀ t, t * C2 t + (d + 2) * C1 t + b * t * C t = 0)
    (hAz : A 1 = 0) (hCz : C 1 = 0)
    (hAp : ∀ t ∈ Ico 0 1, 0 < A t) (hCp : ∀ t ∈ Icc 0 1, 0 ≤ C t)
    (hK : MonotoneOn (fun t => -2 * A1 t / (t * A t) - (b - a)) (Ioo 0 1)) :
    AntitoneOn (fun t => C t / A t) (Ico 0 1) := by
  have hAc : Continuous A := continuous_iff_continuousAt.mpr fun t => (hA t).continuousAt
  have hA1c : Continuous A1 := continuous_iff_continuousAt.mpr fun t => (hA1 t).continuousAt
  have hCc : Continuous C := continuous_iff_continuousAt.mpr fun t => (hC t).continuousAt
  have hC1c : Continuous C1 := continuous_iff_continuousAt.mpr fun t => (hC1 t).continuousAt
  have hp : 0 < d + 2 := by linarith
  set K : ℝ → ℝ := fun t => -2 * A1 t / (t * A t) - (b - a)
  set W : ℝ → ℝ := fun t => t ^ (d + 2) * (A t * C1 t - A1 t * C t)
  set W1 : ℝ → ℝ := fun t => t ^ (d + 2) * A t * C t * K t
  have hWc : ContinuousOn W (Icc 0 1) := (continuousOn_rpow_d hp _).mul
    ((hAc.mul hC1c).sub (hA1c.mul hCc)).continuousOn
  have hW0 : W 0 = 0 := by simp [W, Real.zero_rpow hp.ne']
  have hW1 : W 1 = 0 := by simp [W, hAz, hCz]
  have hWd : ∀ t ∈ Ioo 0 1, HasDerivAt W (W1 t) t := by
    intro t ht
    have htne := ht.1.ne'
    have hAne := (hAp t ⟨ht.1.le, ht.2⟩).ne'
    have hraw := (hasDerivAt_rpow_d (d := d + 2) ht.1).mul
      (((hA t).mul (hC1 t)).sub ((hA1 t).mul (hC t)))
    have hA2 : A2 t = -(d * A1 t + a * t * A t) / t := by
      field_simp
      linarith [hodeA t]
    have hC2 : C2 t = -((d + 2) * C1 t + b * t * C t) / t := by
      field_simp
      linarith [hodeC t]
    convert hraw using 1 <;> (try rfl)
    dsimp only [W1, K, Pi.mul_apply, Pi.sub_apply]
    rw [hA2, hC2]
    field_simp [htne, hAne]
    ring
  have hWnonpos : ∀ t ∈ Icc 0 1, W t ≤ 0 := by
    apply nonpos_of_increasing_coefficient hWc hW0 hW1 hWd hK
    · intro t ht hKt
      exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (mul_nonneg
        (Real.rpow_nonneg ht.1.le _) (hAp t ⟨ht.1.le, ht.2⟩).le)
        (hCp t ⟨ht.1.le, ht.2.le⟩)) hKt
    · intro t ht hKt
      exact mul_nonneg (mul_nonneg (mul_nonneg
        (Real.rpow_nonneg ht.1.le _) (hAp t ⟨ht.1.le, ht.2⟩).le)
        (hCp t ⟨ht.1.le, ht.2.le⟩)) hKt
  refine antitoneOn_of_hasDerivWithinAt_nonpos
    (f' := fun t => (C1 t * A t - C t * A1 t) / A t ^ 2) (convex_Ico _ _)
    (hCc.continuousOn.div hAc.continuousOn (fun t ht => (hAp t ht).ne')) ?_ ?_
  · intro t ht
    rw [interior_Ico] at ht
    exact ((hC t).div (hA t) (hAp t ⟨ht.1.le, ht.2⟩).ne').hasDerivWithinAt
  · intro t ht
    rw [interior_Ico] at ht
    have hW := hWnonpos t ⟨ht.1.le, ht.2.le⟩
    have hn : A t * C1 t - A1 t * C t ≤ 0 :=
      nonpos_of_mul_nonpos_right hW (Real.rpow_pos_of_pos ht.1 (d + 2))
    exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) (sq_nonneg _)

end FourthRatio

end
