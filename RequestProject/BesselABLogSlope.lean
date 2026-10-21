module

public import RequestProject.BesselABRegular
public import RequestProject.BesselAB
public import RequestProject.RadialLogSlope

/-! # Unit-interval bounds for the actual Ashbaugh--Benguria logarithmic slope -/

@[expose] public section

open Set

noncomputable section

namespace FourthRatio

lemma abRegularFactor_antitone {ν : ℝ} (hν : 0 ≤ ν) :
    AntitoneOn (abRegularFactor ν) (Ioo 0 1) := by
  intro x hx y hy hxy
  rw [abRegularFactor_eq hν (ne_of_lt hy.2), abRegularFactor_eq hν (ne_of_lt hx.2)]
  exact ab_bessel_factor_antitone hν ⟨hx.1.le, hx.2⟩ ⟨hy.1.le, hy.2⟩ hxy

lemma abRegularProfile_monotone {ν : ℝ} (hν : 0 ≤ ν) :
    MonotoneOn (fun t => t * abRegularFactor ν t) (Ioo 0 1) := by
  intro x hx y hy hxy
  change x * abRegularFactor ν x ≤ y * abRegularFactor ν y
  rw [abRegularFactor_eq hν (ne_of_lt hx.2), abRegularFactor_eq hν (ne_of_lt hy.2)]
  have h := ab_bessel_monotone hν ⟨hx.1.le, hx.2⟩ ⟨hy.1.le, hy.2⟩ hxy
  simpa only [abDenom, besselF, mul_pow, mul_div_assoc] using h

/-- The genuine regular slope lies in `[0,1]` throughout the positive interval. -/
theorem abLogSlope_mem_Icc {ν : ℝ} (hν : 0 ≤ ν) {t : ℝ} (ht : t ∈ Ioo 0 1) :
    abLogSlope ν t ∈ Icc 0 1 := by
  apply log_slope_bounds_of_monotone_factor (a := 0) (b := 1) (H := abRegularFactor ν)
    (H1 := deriv (abRegularFactor ν)) le_rfl
    (fun s hs => (abRegularFactor_analytic hν s ⟨hs.1.le, hs.2.le⟩).differentiableAt.hasDerivAt)
    (fun s hs => abRegularFactor_pos hν ⟨hs.1.le, hs.2.le⟩)
    (abRegularFactor_antitone hν) (abRegularProfile_monotone hν) t ht

end FourthRatio

end
