module

public import RequestProject.BesselRayleigh

/-!
# The normalized adjacent-zero comparison

This is the strict zero comparison used in the second Ashbaugh--Benguria
Bessel lemma. The proof combines Picone's inequality with the adjacent-order
recurrences, retaining a strictly positive remainder in the energy identity.
-/

@[expose] public section

open Set MeasureTheory Filter Topology

noncomputable section

namespace FourthRatio

/-- Lemma 2.2 of Ashbaugh--Benguria's second proof: the first zero squared,
divided by the order plus one, strictly increases with the order. -/
theorem besselZero_normalized_gap {ν : ℝ} (hν : 0 ≤ ν) :
    (ν + 2) * besselZero ν 1 ^ 2 < (ν + 1) * besselZero (ν + 1) 1 ^ 2 := by
  have hν1 : 0 ≤ ν + 1 := by linarith
  have hν2 : 0 ≤ ν + 2 := by linarith
  have hν3 : 0 ≤ ν + 3 := by linarith
  obtain ⟨hk, -, hFk, -⟩ := besselZero_props hν1
  set k := besselZero (ν + 1) 1
  set d := 2 * ν + 1
  set F := besselF (ν + 1)
  set F1 := besselF1 (ν + 1)
  set F2 := besselF2 (ν + 1)
  set H := besselF (ν + 3)
  have hd : 0 < d := by positivity
  have hF : ∀ r, HasDerivAt F (F1 r) r := hasDerivAt_besselF' hν1
  have hF1 : ∀ r, HasDerivAt F1 (F2 r) r := hasDerivAt_besselF1' hν1
  have hFc : Continuous F := continuous_iff_continuousAt.mpr fun r => (hF r).continuousAt
  have hF1c : Continuous F1 := continuous_iff_continuousAt.mpr fun r => (hF1 r).continuousAt
  have hHc : Continuous H := continuous_iff_continuousAt.mpr fun r =>
    (hasDerivAt_besselF' hν3 r).continuousAt
  have hpw := continuousOn_rpow_d hd (Icc 0 k)
  have hFk' : F k = 0 := hFk
  have hkH : k < besselZero (ν + 3) 1 := by
    have h1 := besselZero_lt_succ hν1
    have h2 := besselZero_lt_succ hν2
    rw [show ν + 1 + 1 = ν + 2 by ring] at h1
    rw [show ν + 2 + 1 = ν + 3 by ring] at h2
    exact h1.trans h2
  have hFp : ∀ r ∈ Ico 0 k, 0 < F r := fun r hr =>
    besselF_pos_before hν1 hr.1 hr.2
  have hFnn : ∀ r ∈ Icc 0 k, 0 ≤ F r := by
    intro r hr
    by_cases he : r = k
    · simp [he, hFk']
    · exact (hFp r ⟨hr.1, lt_of_le_of_ne hr.2 he⟩).le
  have hHp : ∀ r ∈ Icc 0 k, 0 < H r := fun r hr =>
    besselF_pos_before hν3 hr.1 (hr.2.trans_lt hkH)
  set A := ∫ r in (0 : ℝ)..k, r ^ d * F r ^ 2
  set B := ∫ r in (0 : ℝ)..k, r ^ d * F1 r ^ 2
  set K := ∫ r in (0 : ℝ)..k, r ^ d * r ^ 2 * F r * H r
  have hiA : IntervalIntegrable (fun r => r ^ d * F r ^ 2) volume 0 k :=
    (hpw.mul (hFc.pow 2).continuousOn).intervalIntegrable_of_Icc hk.le
  have hiB : IntervalIntegrable (fun r => r ^ d * F1 r ^ 2) volume 0 k :=
    (hpw.mul (hF1c.pow 2).continuousOn).intervalIntegrable_of_Icc hk.le
  have hiK : IntervalIntegrable (fun r => r ^ d * r ^ 2 * F r * H r) volume 0 k :=
    (((hpw.mul (continuous_pow 2).continuousOn).mul hFc.continuousOn).mul
      hHc.continuousOn).intervalIntegrable_of_Icc hk.le
  have hmid : k / 2 ∈ Ioo 0 k := ⟨by linarith, by linarith⟩
  have hApos : 0 < A := by
    refine integral_pos_of_nonneg_of_pos_near hiA (fun r hr => ?_) hmid ?_ ?_
    · exact mul_nonneg (Real.rpow_nonneg hr.1.le _) (sq_nonneg _)
    · exact ((continuousOn_rpow_d hd univ).continuousAt univ_mem).mul
        (hFc.pow 2).continuousAt
    · exact mul_pos (Real.rpow_pos_of_pos hmid.1 _) (sq_pos_of_pos
        (hFp _ ⟨hmid.1.le, hmid.2⟩))
  have hKpos : 0 < K := by
    refine integral_pos_of_nonneg_of_pos_near hiK (fun r hr => ?_) hmid ?_ ?_
    · exact mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hr.1.le _)
        (sq_nonneg _)) (hFnn r ⟨hr.1.le, hr.2⟩)) (hHp r ⟨hr.1.le, hr.2⟩).le
    · exact ((((continuousOn_rpow_d hd univ).continuousAt univ_mem).mul
        (continuous_pow 2).continuousAt).mul hFc.continuousAt).mul hHc.continuousAt
    · exact mul_pos (mul_pos (mul_pos (Real.rpow_pos_of_pos hmid.1 _)
        (sq_pos_of_pos hmid.1)) (hFp _ ⟨hmid.1.le, hmid.2⟩))
        (hHp _ ⟨hmid.1.le, hmid.2.le⟩)
  set E : ℝ → ℝ := fun r => 4 * (ν + 2) * (r ^ d * F r * F1 r)
  set Q : ℝ → ℝ := fun r => 4 * (ν + 2) * (r ^ d * F1 r ^ 2) -
    4 * (ν + 1) * (r ^ d * F r ^ 2) + r ^ d * r ^ 2 * F r * H r
  have hEc : ContinuousOn E (Icc 0 k) :=
    ((hpw.mul hFc.continuousOn).mul hF1c.continuousOn).const_mul _
  have hQint : IntervalIntegrable Q volume 0 k :=
    ((hiB.const_mul _).sub (hiA.const_mul _)).add hiK
  have hEd : ∀ r ∈ Ioo 0 k, HasDerivAt E (Q r) r := by
    intro r hr
    have hode : r * F2 r + (d + 2) * F1 r + r * F r = 0 := by
      have h := besselF_ode' hν1 r
      change r * besselF2 (ν + 1) r + (d + 2) * besselF1 (ν + 1) r +
        r * besselF (ν + 1) r = 0
      convert h using 1 <;> dsimp [d] <;> ring
    have hrec : 2 * (ν + 2) * F1 r + r * F r + r ^ 3 / 4 * H r = 0 := by
      have h := besselF_succ_rel hν1 r
      rw [show ν + 1 + 1 = ν + 2 by ring,
        show ν + 1 + 2 = ν + 3 by ring] at h
      dsimp [F1, F, H]
      rw [besselF1_succ hν1, show ν + 1 + 1 = ν + 2 by ring]
      linear_combination -r * h
    have h := (((hasDerivAt_rpow_d (d := d) hr.1).mul (hF r)).mul
      (hF1 r)).const_mul (4 * (ν + 2))
    convert h using 1
    dsimp only [Q, Pi.mul_apply]
    field_simp [hr.1.ne']
    dsimp only [d] at hode
    linear_combination -4 * (ν + 2) * r ^ d * F r * hode +
      4 * r ^ d * F r * hrec
  have hE : 4 * (ν + 2) * B - 4 * (ν + 1) * A + K = 0 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hk.le hEc hEd hQint
    have he : E k - E 0 = 0 := by simp [E, hFk', Real.zero_rpow hd.ne']
    rw [he] at h
    dsimp only [Q] at h
    rw [intervalIntegral.integral_add ((hiB.const_mul _).sub (hiA.const_mul _)) hiK,
      intervalIntegral.integral_sub (hiB.const_mul _) (hiA.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h
    exact h
  have hlow : (besselZero ν 1 / k) ^ 2 * A ≤ B :=
    bessel_rayleigh_lower hν hk hF hF1c hFk'
  have hstrict : (ν + 2) * B < (ν + 1) * A := by linarith
  have hscaled : ((ν + 2) * (besselZero ν 1 / k) ^ 2) * A < (ν + 1) * A := by
    have h := mul_le_mul_of_nonneg_left hlow (by linarith : 0 ≤ ν + 2)
    nlinarith
  have hratio : (ν + 2) * (besselZero ν 1 / k) ^ 2 < ν + 1 :=
    lt_of_mul_lt_mul_right hscaled hApos.le
  have h := mul_lt_mul_of_pos_right hratio (sq_pos_of_pos hk)
  field_simp [hk.ne'] at h
  simpa only [k, mul_comm] using h

end FourthRatio

end
