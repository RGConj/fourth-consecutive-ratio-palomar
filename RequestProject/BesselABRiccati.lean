module

public import RequestProject.BesselABLogSlope
public import RequestProject.RadialRiccati

/-! # The Riccati equation of the regular Bessel logarithmic slope -/

@[expose] public section

open Set Filter Topology

noncomputable section

namespace FourthRatio

lemma abDenom_ode {ν : ℝ} (hν : 0 ≤ ν) (t : ℝ) :
    t * abDenomDD ν t + (2 * ν + 1) * abDenomD ν t +
      besselZero ν 1 ^ 2 * t * abDenom ν t = 0 := by
  have h := besselF_ode' hν (besselZero ν 1 * t)
  dsimp only [abDenom, abDenomD, abDenomDD]
  linear_combination besselZero ν 1 * h

lemma abLogSlope_eq_raw {ν : ℝ} (hν : 0 ≤ ν) {t : ℝ} (ht : t ∈ Ioo 0 1) :
    abLogSlope ν t = 1 + t *
      (abDenomD (ν + 1) t / abDenom (ν + 1) t - abDenomD ν t / abDenom ν t) := by
  have hμ : 0 ≤ ν + 1 := by linarith
  have hAne := (abDenom_pos hν ⟨ht.1.le, ht.2⟩).ne'
  have hCne := (abDenom_pos hμ ⟨ht.1.le, ht.2⟩).ne'
  have heq : abRegularFactor ν =ᶠ[𝓝 t]
      (fun s => abDenom (ν + 1) s / abDenom ν s) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact abRegularFactor_eq hν (ne_of_lt hs.2)
  have hD := ((hasDerivAt_abDenom hμ t).div (hasDerivAt_abDenom hν t) hAne).congr_of_eventuallyEq heq
  dsimp only [abLogSlope]
  rw [hD.deriv, abRegularFactor_eq hν (ne_of_lt ht.2)]
  field_simp [hAne, hCne] <;> ring

lemma abLogSlope_hasDerivAt_raw {ν : ℝ} (hν : 0 ≤ ν) {t : ℝ} (ht : t ∈ Ioo 0 1) :
    HasDerivAt (abLogSlope ν)
      ((besselZero ν 1 ^ 2 - besselZero (ν + 1) 1 ^ 2) * t +
        (1 - abLogSlope ν t) * (abLogSlope ν t + (2 * ν + 1)) / t -
          2 * abLogSlope ν t * abDenomD ν t / abDenom ν t) t := by
  have hμ : 0 ≤ ν + 1 := by linarith
  have hC : t * abDenomDD (ν + 1) t + ((2 * ν + 1) + 2) * abDenomD (ν + 1) t +
      besselZero (ν + 1) 1 ^ 2 * t * abDenom (ν + 1) t = 0 := by
    convert abDenom_ode hμ t using 1 <;> ring
  have hraw := quotient_log_slope_deriv ht.1.ne'
    (abDenom_pos hν ⟨ht.1.le, ht.2⟩).ne' (abDenom_pos hμ ⟨ht.1.le, ht.2⟩).ne'
    (hasDerivAt_abDenom hν t) (hasDerivAt_abDenomD hν t)
    (hasDerivAt_abDenom hμ t) (hasDerivAt_abDenomD hμ t) (abDenom_ode hν t) hC
  have heq : abLogSlope ν =ᶠ[𝓝 t] (fun s => 1 + s *
      (abDenomD (ν + 1) s / abDenom (ν + 1) s - abDenomD ν s / abDenom ν s)) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact abLogSlope_eq_raw hν hs
  have h := hraw.congr_of_eventuallyEq heq
  simpa only [abLogSlope_eq_raw hν ht] using h

/-- The vector field with a fixed slope as its second argument. -/
def abRiccati (ν q t : ℝ) : ℝ :=
  (besselZero ν 1 ^ 2 - besselZero (ν + 1) 1 ^ 2) * t +
    (1 - q) * (q + (2 * ν + 1)) / t +
      2 * besselZero ν 1 * q * besselOrderRatio ν (besselZero ν 1 * t)

theorem hasDerivAt_abLogSlope {ν : ℝ} (hν : 0 ≤ ν) {t : ℝ} (ht : t ∈ Ioo 0 1) :
    HasDerivAt (abLogSlope ν) (abRiccati ν (abLogSlope ν t) t) t := by
  apply (abLogSlope_hasDerivAt_raw hν ht).congr_deriv
  dsimp only [abRiccati, abDenomD, abDenom, besselOrderRatio]
  ring

end FourthRatio

end
