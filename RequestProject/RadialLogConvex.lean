module

public import RequestProject.BesselGap

/-!
# Convexity of a positive radial logarithmic derivative

Two weighted derivative identities underlie the same-argument Bessel quotient
convexity argument of Ashbaugh--Benguria. The weights are written without
negative powers at the origin, where the unweighted Riccati equation is singular.
-/

@[expose] public section

open Set

noncomputable section

namespace FourthRatio

private lemma positive_from_zero {f f1 : ℝ → ℝ} {k : ℝ}
    (hc : ContinuousOn f (Ico 0 k)) (hz : f 0 = 0)
    (hf : ∀ t ∈ Ioo 0 k, HasDerivAt f (f1 t) t)
    (hp : ∀ t ∈ Ioo 0 k, 0 < f1 t) :
    ∀ t ∈ Ioo 0 k, 0 < f t := by
  intro t ht
  have hm : StrictMonoOn f (Icc 0 t) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc _ _) (hc.mono ?_) ?_
    · intro x hx
      exact ⟨hx.1, hx.2.trans_lt ht.2⟩
    · intro x hx
      rw [interior_Icc] at hx
      have hx' : x ∈ Ioo 0 k := ⟨hx.1, hx.2.trans ht.2⟩
      rw [(hf x hx').deriv]
      exact hp x hx'
  simpa only [hz] using hm ⟨le_rfl, ht.1.le⟩ ⟨ht.1.le, le_rfl⟩ ht.1

/-- If `A' = -A y` and `y` solves the differentiated radial Riccati equation,
positivity of `A` and `y` forces both `y'` and `y''` to be strictly positive.
The continuous derivative at the origin is an explicit hypothesis. -/
lemma radial_logderiv_strict_convex {A y y1 y2 : ℝ → ℝ} {d k : ℝ}
    (hd : 0 < d)
    (hAc : ContinuousOn A (Ico 0 k)) (hyc : ContinuousOn y (Ico 0 k))
    (hy1c : ContinuousOn y1 (Ico 0 k))
    (hA : ∀ t ∈ Ioo 0 k, HasDerivAt A (-A t * y t) t)
    (hy : ∀ t ∈ Ioo 0 k, HasDerivAt y (y1 t) t)
    (hy1 : ∀ t ∈ Ioo 0 k, HasDerivAt y1 (y2 t) t)
    (hode : ∀ t ∈ Ioo 0 k,
      y2 t = 2 * y t * y1 t - d * y1 t / t + d * y t / t ^ 2)
    (hAp : ∀ t ∈ Ioo 0 k, 0 < A t) (hyp : ∀ t ∈ Ioo 0 k, 0 < y t) :
    (∀ t ∈ Ioo 0 k, 0 < y1 t) ∧ (∀ t ∈ Ioo 0 k, 0 < y2 t) := by
  have hpw := continuousOn_rpow_d hd (Ico 0 k)
  set T : ℝ → ℝ := fun t => t ^ d * A t ^ 2 * y1 t
  set T1 : ℝ → ℝ := fun t => d * t ^ d * A t ^ 2 * y t / t ^ 2
  have hTc : ContinuousOn T (Ico 0 k) := (hpw.mul (hAc.pow 2)).mul hy1c
  have hT0 : T 0 = 0 := by simp [T, Real.zero_rpow hd.ne']
  have hTd : ∀ t ∈ Ioo 0 k, HasDerivAt T (T1 t) t := by
    intro t ht
    have h := (((hasDerivAt_rpow_d (d := d) ht.1).mul
      ((hA t ht).pow 2)).mul (hy1 t ht))
    convert h using 1
    dsimp only [T1, Pi.mul_apply, Pi.pow_apply]
    rw [hode t ht]
    field_simp [ht.1.ne']
    ring
  have hTp : ∀ t ∈ Ioo 0 k, 0 < T t := by
    apply positive_from_zero hTc hT0 hTd
    intro t ht
    dsimp only [T1]
    exact div_pos (mul_pos (mul_pos (mul_pos hd (Real.rpow_pos_of_pos ht.1 _))
      (sq_pos_of_pos (hAp t ht))) (hyp t ht)) (sq_pos_of_pos ht.1)
  have hy1p : ∀ t ∈ Ioo 0 k, 0 < y1 t := by
    intro t ht
    have hcoef := mul_pos (Real.rpow_pos_of_pos ht.1 d) (sq_pos_of_pos (hAp t ht))
    exact (mul_pos_iff_of_pos_left hcoef).mp (hTp t ht)
  set Z : ℝ → ℝ := fun t => t ^ d * A t ^ 2 *
    (2 * t ^ 2 * y t * y1 t - d * t * y1 t + d * y t)
  set Z1 : ℝ → ℝ := fun t =>
    2 * t ^ d * A t ^ 2 * t * y1 t * (2 * y t + t * y1 t)
  have hZc : ContinuousOn Z (Ico 0 k) := by
    exact (hpw.mul (hAc.pow 2)).mul
      ((((((continuousOn_const.mul ((continuous_pow 2).continuousOn)).mul hyc).mul
        hy1c).sub ((continuousOn_const.mul continuousOn_id).mul hy1c)).add
        (continuousOn_const.mul hyc)))
  have hZ0 : Z 0 = 0 := by simp [Z, Real.zero_rpow hd.ne']
  have hZd : ∀ t ∈ Ioo 0 k, HasDerivAt Z (Z1 t) t := by
    intro t ht
    have hL := (((((hasDerivAt_pow 2 t).const_mul 2).mul (hy t ht)).mul
      (hy1 t ht)).sub ((((hasDerivAt_id t).const_mul d).mul (hy1 t ht)))).add
      ((hy t ht).const_mul d)
    have h := ((hasDerivAt_rpow_d (d := d) ht.1).mul ((hA t ht).pow 2)).mul hL
    convert h using 1
    · rfl
    · dsimp only [Z1, Pi.mul_apply, Pi.sub_apply, Pi.add_apply, Pi.pow_apply, id]
      rw [hode t ht]
      norm_num
      field_simp [ht.1.ne']
      ring
  have hZp : ∀ t ∈ Ioo 0 k, 0 < Z t := by
    apply positive_from_zero hZc hZ0 hZd
    intro t ht
    dsimp only [Z1]
    have ha := hAp t ht
    have hb := hyp t ht
    have hc := hy1p t ht
    have hw : 0 < t ^ d := Real.rpow_pos_of_pos ht.1 _
    have ht0 := ht.1
    positivity
  refine ⟨hy1p, fun t ht => ?_⟩
  have hZeq : Z t = (t ^ d * A t ^ 2 * t ^ 2) * y2 t := by
    dsimp only [Z]
    rw [hode t ht]
    field_simp [ht.1.ne'] <;> ring
  have hcoef := mul_pos (mul_pos (Real.rpow_pos_of_pos ht.1 d)
    (sq_pos_of_pos (hAp t ht))) (sq_pos_of_pos ht.1)
  have hz := hZp t ht
  rw [hZeq] at hz
  exact (mul_pos_iff_of_pos_left hcoef).mp hz

end FourthRatio

end
