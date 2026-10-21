module

public import RequestProject.BesselRecurrence

/-!
# A radial Rayleigh bound and a sharper comparison of adjacent Bessel zeros

The Rayleigh bound follows from Picone's identity, using positive Bessel
profiles below their first zero and then taking the frequency limit.
-/

@[expose] public section

open Filter Topology Set MeasureTheory

noncomputable section

namespace FourthRatio

/-- The first radial Bessel zero bounds the weighted Rayleigh quotient on an
interval. No condition on the trial function at the origin is needed. -/
lemma bessel_rayleigh_lower {ν k : ℝ} (hν : 0 ≤ ν) (hk : 0 < k)
    {g g1 : ℝ → ℝ} (hg : ∀ r, HasDerivAt g (g1 r) r)
    (hg1c : Continuous g1) (hgk : g k = 0) :
    (besselZero ν 1 / k) ^ 2 *
        (∫ r in (0 : ℝ)..k, r ^ (2 * ν + 1) * g r ^ 2) ≤
      ∫ r in (0 : ℝ)..k, r ^ (2 * ν + 1) * g1 r ^ 2 := by
  have hj : 0 < besselZero ν 1 := (besselZero_props hν).1
  have hd : 0 < 2 * ν + 1 := by positivity
  set A := ∫ r in (0 : ℝ)..k, r ^ (2 * ν + 1) * g r ^ 2
  set B := ∫ r in (0 : ℝ)..k, r ^ (2 * ν + 1) * g1 r ^ 2
  have hβ : 0 < besselZero ν 1 / k := div_pos hj hk
  have hPic : ∀ β ∈ Ioo 0 (besselZero ν 1 / k), β ^ 2 * A ≤ B := by
    intro β hβ'
    have hb0 : 0 < β := hβ'.1
    exact picone_ineq (d := 2 * ν + 1) (b := β ^ 2) hd hk
      (ρ := fun r => besselF ν (β * r)) (ρ1 := fun r => β * besselF1 ν (β * r))
      (ρ2 := fun r => β ^ 2 * besselF2 ν (β * r))
      (fun r => by
        have h := (hasDerivAt_besselF' hν (β * r)).comp r
          ((hasDerivAt_id r).const_mul β)
        convert h using 1
        · rfl
        · ring)
      (fun r => by
        have h := ((hasDerivAt_besselF1' hν (β * r)).comp r
          ((hasDerivAt_id r).const_mul β)).const_mul β
        convert h using 1
        · rfl
        · ring)
      (fun r => by
        have h := besselF_ode' hν (β * r)
        linear_combination β * h)
      (fun r hr => by
        refine besselF_pos_before hν (mul_nonneg hb0.le hr.1) ?_
        have h1 : β * r ≤ β * k := mul_le_mul_of_nonneg_left hr.2 hb0.le
        have h2 := mul_lt_mul_of_pos_right hβ'.2 hk
        rw [div_mul_cancel₀ _ hk.ne'] at h2
        exact h1.trans_lt h2)
      hg hg1c hgk
  have ht : Tendsto (fun β : ℝ => β ^ 2 * A)
      (𝓝[<] (besselZero ν 1 / k)) (𝓝 ((besselZero ν 1 / k) ^ 2 * A)) :=
    ((continuous_pow 2).mul continuous_const).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  refine le_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsLT hβ] with β hβ'
  exact hPic β hβ'

end FourthRatio

end
