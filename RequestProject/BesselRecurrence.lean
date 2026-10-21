module

public import RequestProject.BesselGap

/-!
# Adjacent-order recurrences for the normalized Bessel series

These identities follow directly from the defining coefficients. They avoid
singular powers at the origin in the remaining Ashbaugh--Benguria argument.
-/

@[expose] public section

noncomputable section

namespace FourthRatio

/-- Differentiating the entire series raises its order by one. -/
lemma besselSeries1_succ {ν : ℝ} (hν : 0 ≤ ν) (s : ℝ) :
    besselSeries1 ν s = (-1 / 4 : ℝ) * besselSeries (ν + 1) 1 s := by
  unfold besselSeries1 besselSeries
  rw [← tsum_mul_left]
  apply tsum_congr
  intro m
  have hm : (m : ℝ) + 1 ≠ 0 := by positivity
  have hfac : (m.factorial : ℝ) ≠ 0 := by positivity
  have hΓ : Real.Gamma ((m : ℝ) + (ν + 1) + 1) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by positivity)).ne'
  simp only [besselCoef, pow_succ, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one]
  rw [show (m : ℝ) + 1 + ν + 1 = (m : ℝ) + (ν + 1) + 1 by ring]
  field_simp [hm, hfac, hΓ]

/-- The ordinary radial derivative in adjacent-order form. -/
lemma besselF1_succ {ν : ℝ} (hν : 0 ≤ ν) (x : ℝ) :
    besselF1 ν x = -(x / 2) * besselF (ν + 1) x := by
  dsimp only [besselF1, besselF]
  rw [besselSeries1_succ hν]
  ring

/-- The three-term recurrence, in the entire normalization used by this project. -/
lemma besselF_succ_rel {ν : ℝ} (hν : 0 ≤ ν) (x : ℝ) :
    (ν + 1) * besselF (ν + 1) x =
      besselF ν x + x ^ 2 / 4 * besselF (ν + 2) x := by
  have hν1 : 0 ≤ ν + 1 := by linarith
  have h := besselSeries_succ_rel hν (x ^ 2)
  rw [besselSeries1_succ hν1,
    show ν + 1 + 1 = ν + 2 by ring] at h
  dsimp only [besselF]
  linear_combination h

end FourthRatio

end
