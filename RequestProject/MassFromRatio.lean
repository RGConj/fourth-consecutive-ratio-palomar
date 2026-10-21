module

public import RequestProject.ChitiCrossing
public import Mathlib.Tactic

/-!
# Cumulative square-mass comparison from an increasing ratio

This step converts a one-dimensional quotient comparison into the mass form
used in Chiti comparison, for any measure supported on the positive half-line.
It does not construct an eigenfunction rearrangement.
-/

@[expose] public section

open Set MeasureTheory Filter

namespace FourthRatio

/-- Equal square masses and an increasing ratio to a positive compactly
supported comparison profile imply ordered cumulative square masses. -/
theorem cumulative_sq_le_of_ratio_monotone {μ : Measure ℝ} {f g : ℝ → ℝ} {R : ℝ}
    (hR : 0 < R) (hμ : ∀ᵐ s ∂μ, 0 < s)
    (hf : Integrable (fun s => f s ^ 2) μ)
    (hg : Integrable (fun s => g s ^ 2) μ)
    (heq : (∫ s, f s ^ 2 ∂μ) = ∫ s, g s ^ 2 ∂μ)
    (hf0 : ∀ s > 0, 0 ≤ f s)
    (hgp : ∀ s ∈ Ioo 0 R, 0 < g s)
    (hgz : ∀ s, R ≤ s → g s = 0)
    (hratio : MonotoneOn (fun s => f s / g s) (Ioo 0 R)) (r : ℝ) :
    (∫ s in Iio r, f s ^ 2 ∂μ) ≤ ∫ s in Iio r, g s ^ 2 ∂μ := by
  have hsmall (h : ∀ s > 0, s < r → f s ^ 2 ≤ g s ^ 2) :
      (∫ s in Iio r, f s ^ 2 ∂μ) ≤ ∫ s in Iio r, g s ^ 2 ∂μ := by
    apply setIntegral_mono_ae_restrict hf.integrableOn hg.integrableOn
    filter_upwards [ae_restrict_of_ae hμ, ae_restrict_mem measurableSet_Iio] with s hs hsr
    exact h s hs hsr
  have hlarge (h : ∀ s > 0, r ≤ s → g s ^ 2 ≤ f s ^ 2) :
      (∫ s in Iio r, f s ^ 2 ∂μ) ≤ ∫ s in Iio r, g s ^ 2 ∂μ := by
    have hcomp : (∫ s in (Iio r)ᶜ, g s ^ 2 ∂μ) ≤
        ∫ s in (Iio r)ᶜ, f s ^ 2 ∂μ := by
      apply setIntegral_mono_ae_restrict hg.integrableOn hf.integrableOn
      filter_upwards [ae_restrict_of_ae hμ,
        ae_restrict_mem measurableSet_Iio.compl] with s hs hsr
      exact h s hs (by simpa only [mem_compl_iff, mem_Iio, not_lt] using hsr)
    have hsf := integral_add_compl (s := Iio r) measurableSet_Iio hf
    have hsg := integral_add_compl (s := Iio r) measurableSet_Iio hg
    linarith
  by_cases hr0 : r ≤ 0
  · apply hsmall
    intro s hs hsr
    exact False.elim (not_lt_of_ge (hr0.trans_lt hs).le hsr)
  have hrpos : 0 < r := lt_of_not_ge hr0
  by_cases hrR : R ≤ r
  · apply hlarge
    intro s _ hrs
    rw [hgz s (hrR.trans hrs), zero_pow (by decide : (2 : ℕ) ≠ 0)]
    exact sq_nonneg _
  have hr : r ∈ Ioo 0 R := ⟨hrpos, lt_of_not_ge hrR⟩
  by_cases hfr : f r ≤ g r
  · apply hsmall
    intro s hs hsr
    have hsin : s ∈ Ioo 0 R := ⟨hs, hsr.trans hr.2⟩
    have hdiv : f s / g s ≤ 1 :=
      (hratio hsin hr hsr.le).trans ((div_le_one (hgp r hr)).mpr hfr)
    have hfg : f s ≤ g s := (div_le_one (hgp s hsin)).mp hdiv
    exact (sq_le_sq₀ (hf0 s hs) (hgp s hsin).le).mpr hfg
  · apply hlarge
    intro s hs hrs
    by_cases hsR : R ≤ s
    · rw [hgz s hsR, zero_pow (by decide : (2 : ℕ) ≠ 0)]
      exact sq_nonneg _
    have hsin : s ∈ Ioo 0 R := ⟨hs, lt_of_not_ge hsR⟩
    have hrf : g r ≤ f r := (lt_of_not_ge hfr).le
    have hdiv : 1 ≤ f s / g s :=
      ((one_le_div (hgp r hr)).mpr hrf).trans (hratio hr hsin hrs)
    have hgf : g s ≤ f s := (one_le_div (hgp s hsin)).mp hdiv
    exact (sq_le_sq₀ (hgp s hsin).le (hf0 s hs)).mpr hgf

end FourthRatio
