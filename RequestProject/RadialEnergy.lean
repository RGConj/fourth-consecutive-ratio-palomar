module

public import RequestProject.BesselGap

/-!
# The energy consequence of a decreasing logarithmic slope

This is the final elementary step in the Ashbaugh--Benguria energy lemma.
It does not assert that the actual Bessel quotient has the required slope.
-/

@[expose] public section

open Set

noncomputable section

namespace FourthRatio

/-- If the logarithmic slope `q = t w'/w` lies in `[0,1]` and decreases,
the radial energy `w'^2 + d (w/t)^2` decreases. -/
lemma radial_energy_antitone {w q q1 : ℝ → ℝ} {a b d : ℝ}
    (ha : 0 ≤ a) (hd : 0 ≤ d)
    (hw : ∀ t ∈ Ioo a b, HasDerivAt w (q t * w t / t) t)
    (hq : ∀ t ∈ Ioo a b, HasDerivAt q (q1 t) t)
    (hqr : ∀ t ∈ Ioo a b, q t ∈ Icc 0 1)
    (hq1 : ∀ t ∈ Ioo a b, q1 t ≤ 0) :
    AntitoneOn (fun t => deriv w t ^ 2 + d * (w t / t) ^ 2) (Ioo a b) := by
  set B : ℝ → ℝ := fun t => (w t / t) ^ 2 * (q t ^ 2 + d)
  set B1 : ℝ → ℝ := fun t => 2 * (w t / t) ^ 2 / t *
    (t * q t * q1 t + (q t ^ 2 + d) * (q t - 1))
  have htpos : ∀ t ∈ Ioo a b, 0 < t := fun t ht => ha.trans_lt ht.1
  have hBd : ∀ t ∈ Ioo a b, HasDerivAt B (B1 t) t := by
    intro t ht
    have h := (((hw t ht).div (hasDerivAt_id t) (htpos t ht).ne').pow 2).mul
      (((hq t ht).pow 2).add_const d)
    convert h using 1
    · rfl
    · dsimp only [B1, Pi.div_apply, Pi.pow_apply, id]
      norm_num
      field_simp [(htpos t ht).ne']
      ring
  have hmono : AntitoneOn B (Ioo a b) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := B1) (convex_Ioo _ _) ?_ ?_ ?_
    · intro t ht
      exact (hBd t ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ioo] at ht
      exact (hBd t ht).hasDerivWithinAt
    · intro t ht
      rw [interior_Ioo] at ht
      dsimp only [B1]
      apply mul_nonpos_of_nonneg_of_nonpos (div_nonneg (by positivity) (htpos t ht).le)
      have h1 : t * q t * q1 t ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (htpos t ht).le (hqr t ht).1) (hq1 t ht)
      have h2 : (q t ^ 2 + d) * (q t - 1) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (add_nonneg (sq_nonneg _) hd)
          (sub_nonpos.mpr (hqr t ht).2)
      exact add_nonpos h1 h2
  have hBeq : ∀ t ∈ Ioo a b, deriv w t ^ 2 + d * (w t / t) ^ 2 = B t := by
    intro t ht
    rw [(hw t ht).deriv]
    dsimp only [B]
    field_simp
  intro x hx y hy hxy
  change deriv w y ^ 2 + d * (w y / y) ^ 2 ≤ deriv w x ^ 2 + d * (w x / x) ^ 2
  rw [hBeq x hx, hBeq y hy]
  exact hmono hx hy hxy

end FourthRatio

end
