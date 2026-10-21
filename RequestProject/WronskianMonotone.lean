module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-! # A Wronskian monotonicity criterion for radial Sturm--Liouville equations -/

@[expose] public section

open Set

noncomputable section

namespace FourthRatio

private lemma wronskian_hasDerivAt_rpow {d r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun x : ℝ => x ^ d) (d * r ^ d / r) r := by
  have := Real.hasDerivAt_rpow_const (p := d) (Or.inl hr.ne')
  rwa [Real.rpow_sub_one hr.ne', ← mul_div_assoc] at this

private lemma wronskian_continuousOn_rpow {d : ℝ} (hd : 0 < d) (s : Set ℝ) :
    ContinuousOn (fun x : ℝ => x ^ d) s :=
  fun r _ => (Real.continuousAt_rpow_const r d (Or.inr hd.le)).continuousWithinAt

/-- A function whose derivative changes from nonnegative to nonpositive, and
which vanishes at both endpoints, is nonnegative between them. The quadratic
coefficient form avoids choosing the point at which the sign changes. -/
lemma nonneg_of_quadratic_derivative {f f' : ℝ → ℝ} {d δ : ℝ}
    (hδ : 0 ≤ δ) (hc : ContinuousOn f (Icc 0 1)) (h0 : f 0 = 0) (h1 : f 1 = 0)
    (hf : ∀ t ∈ Ioo 0 1, HasDerivAt f (f' t) t)
    (hpos : ∀ t ∈ Ioo 0 1, 0 ≤ d - δ * t ^ 2 → 0 ≤ f' t)
    (hneg : ∀ t ∈ Ioo 0 1, d - δ * t ^ 2 ≤ 0 → f' t ≤ 0) :
    ∀ x ∈ Icc 0 1, 0 ≤ f x := by
  intro x hx
  by_cases hcut : 0 ≤ d - δ * x ^ 2
  · have hm : MonotoneOn f (Icc 0 x) := by
      refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := f') (convex_Icc _ _)
        (hc.mono ?_) ?_ ?_
      · intro t ht
        exact ⟨ht.1, ht.2.trans hx.2⟩
      · intro t ht
        rw [interior_Icc] at ht
        exact (hf t ⟨ht.1, ht.2.trans_le hx.2⟩).hasDerivWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        apply hpos t ⟨ht.1, ht.2.trans_le hx.2⟩
        have hs : t ^ 2 ≤ x ^ 2 := by nlinarith [hx.1, ht.1, ht.2]
        linarith [mul_le_mul_of_nonneg_left hs hδ]
    simpa [h0] using hm ⟨le_rfl, hx.1⟩ ⟨hx.1, le_rfl⟩ hx.1
  · have hm : AntitoneOn f (Icc x 1) := by
      refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := f') (convex_Icc _ _)
        (hc.mono ?_) ?_ ?_
      · intro t ht
        exact ⟨hx.1.trans ht.1, ht.2⟩
      · intro t ht
        rw [interior_Icc] at ht
        exact (hf t ⟨hx.1.trans_lt ht.1, ht.2⟩).hasDerivWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        apply hneg t ⟨hx.1.trans_lt ht.1, ht.2⟩
        have hd : d - δ * x ^ 2 < 0 := lt_of_not_ge hcut
        have hs : x ^ 2 ≤ t ^ 2 := by nlinarith [hx.1, ht.1]
        linarith [mul_le_mul_of_nonneg_left hs hδ]
    simpa [h1] using hm ⟨le_rfl, hx.2⟩ ⟨hx.2, le_rfl⟩ hx.2

/-- The Wronskian argument for radial ground states of angular degrees zero and
one. This form uses entire radial functions, so no singular Bessel values occur
at the origin. -/
lemma radial_ratio_monotone {A A1 A2 B B1 B2 : ℝ → ℝ} {a b d : ℝ}
    (hd : 0 < d) (hab : a ≤ b)
    (hA : ∀ t, HasDerivAt A (A1 t) t)
    (hA1 : ∀ t, HasDerivAt A1 (A2 t) t)
    (hB : ∀ t, HasDerivAt B (B1 t) t)
    (hB1 : ∀ t, HasDerivAt B1 (B2 t) t)
    (hodeA : ∀ t, t * A2 t + d * A1 t + a * t * A t = 0)
    (hodeB : ∀ t, t ^ 2 * B2 t + d * t * B1 t + (b * t ^ 2 - d) * B t = 0)
    (hAz : A 1 = 0) (hBz : B 1 = 0)
    (hAp : ∀ t ∈ Ico 0 1, 0 < A t) (hBp : ∀ t ∈ Icc 0 1, 0 ≤ B t) :
    MonotoneOn (fun t => B t / A t) (Ico 0 1) := by
  have hAc : Continuous A := continuous_iff_continuousAt.mpr fun t => (hA t).continuousAt
  have hA1c : Continuous A1 := continuous_iff_continuousAt.mpr fun t => (hA1 t).continuousAt
  have hBc : Continuous B := continuous_iff_continuousAt.mpr fun t => (hB t).continuousAt
  have hB1c : Continuous B1 := continuous_iff_continuousAt.mpr fun t => (hB1 t).continuousAt
  set W : ℝ → ℝ := fun t => t ^ d * (A t * B1 t - A1 t * B t)
  set W1 : ℝ → ℝ := fun t => t ^ d / t ^ 2 * A t * B t * (d - (b - a) * t ^ 2)
  have hWc : ContinuousOn W (Icc 0 1) :=
    (wronskian_continuousOn_rpow hd _).mul ((hAc.mul hB1c).sub (hA1c.mul hBc)).continuousOn
  have hW0 : W 0 = 0 := by simp [W, Real.zero_rpow hd.ne']
  have hW1 : W 1 = 0 := by simp [W, hAz, hBz]
  have hWd : ∀ t ∈ Ioo 0 1, HasDerivAt W (W1 t) t := by
    intro t ht
    have ht0 := ht.1
    have h := (wronskian_hasDerivAt_rpow (d := d) ht0).mul
      (((hA t).mul (hB1 t)).sub ((hA1 t).mul (hB t)))
    convert h using 1
    have hA2 : A2 t = -(d * A1 t + a * t * A t) / t := by
      field_simp
      linarith [hodeA t]
    have hB2 : B2 t = -(d * t * B1 t + (b * t ^ 2 - d) * B t) / t ^ 2 := by
      field_simp
      linarith [hodeB t]
    dsimp only [W1, Pi.mul_apply, Pi.sub_apply]
    rw [hA2, hB2]
    field_simp
    ring
  have hWnn : ∀ t ∈ Icc 0 1, 0 ≤ W t := by
    apply nonneg_of_quadratic_derivative (sub_nonneg.mpr hab) hWc hW0 hW1 hWd
    · intro t ht hcut
      have hp : 0 ≤ t ^ d / t ^ 2 * A t * B t := by
        exact mul_nonneg (mul_nonneg (div_nonneg
          (Real.rpow_nonneg ht.1.le _) (sq_nonneg _))
          (hAp t ⟨ht.1.le, ht.2⟩).le) (hBp t ⟨ht.1.le, ht.2.le⟩)
      exact mul_nonneg hp hcut
    · intro t ht hcut
      have hp : 0 ≤ t ^ d / t ^ 2 * A t * B t := by
        exact mul_nonneg (mul_nonneg (div_nonneg
          (Real.rpow_nonneg ht.1.le _) (sq_nonneg _))
          (hAp t ⟨ht.1.le, ht.2⟩).le) (hBp t ⟨ht.1.le, ht.2.le⟩)
      exact mul_nonpos_of_nonneg_of_nonpos hp hcut
  refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun t =>
    (B1 t * A t - B t * A1 t) / A t ^ 2) (convex_Ico _ _)
    (hBc.continuousOn.div hAc.continuousOn (fun t ht => (hAp t ht).ne')) ?_ ?_
  · intro t ht
    rw [interior_Ico] at ht
    exact ((hB t).div (hA t) (hAp t ⟨ht.1.le, ht.2⟩).ne').hasDerivWithinAt
  · intro t ht
    rw [interior_Ico] at ht
    have ht0 := ht.1
    have hW := hWnn t ⟨ht.1.le, ht.2.le⟩
    have hp : 0 < t ^ d := Real.rpow_pos_of_pos ht0 _
    have hn : 0 ≤ A t * B1 t - A1 t * B t := (mul_nonneg_iff_of_pos_left hp).mp hW
    apply div_nonneg _ (sq_nonneg _)
    nlinarith


end FourthRatio
end
