module

public import RequestProject.BesselABSlopeAntitone
public import RequestProject.RadialEnergy

/-! # The decreasing Ashbaugh--Benguria energy weight -/

@[expose] public section

open Set Filter Topology

noncomputable section

namespace FourthRatio

/-- The unextended Bessel quotient, agreeing with `abW` in PPWDeep. -/
def abRawProfile (ν t : ℝ) : ℝ := t * abDenom (ν + 1) t / abDenom ν t

lemma abRawProfile_eq {ν : ℝ} (hν : 0 ≤ ν) {t : ℝ} (ht : t ≠ 1) :
    abRawProfile ν t = t * abRegularFactor ν t := by
  rw [abRegularFactor_eq hν ht]
  exact mul_div_assoc _ _ _

theorem ab_bessel_energy_antitone {ν : ℝ} (hν : 0 ≤ ν) :
    AntitoneOn (fun t => deriv (abRawProfile ν) t ^ 2 +
      (2 * ν + 1) * (abRawProfile ν t / t) ^ 2) (Ioo 0 1) := by
  let w : ℝ → ℝ := fun t => t * abRegularFactor ν t
  have hwd : ∀ t ∈ Ioo 0 1, HasDerivAt w (abLogSlope ν t * w t / t) t := by
    intro t ht
    have hH := (abRegularFactor_analytic hν t ⟨ht.1.le, ht.2.le⟩).differentiableAt.hasDerivAt
    have hw : HasDerivAt w (abRegularFactor ν t + t * deriv (abRegularFactor ν) t) t := by
      convert (hasDerivAt_id t).mul hH using 1 <;> (try rfl)
      simp only [one_mul, id]
    apply hw.congr_deriv
    dsimp only [w, abLogSlope]
    field_simp [ht.1.ne', (abRegularFactor_pos hν ⟨ht.1.le, ht.2.le⟩).ne'] <;> ring
  have hmon := radial_energy_antitone (a := 0) (b := 1) (d := 2 * ν + 1)
    (w := w) (q := abLogSlope ν) (q1 := deriv (abLogSlope ν)) le_rfl (by linarith) hwd
    (fun t ht => (hasDerivAt_abLogSlope hν ht).differentiableAt.hasDerivAt)
    (fun t ht => abLogSlope_mem_Icc hν ht) (fun t ht => abLogSlope_deriv_nonpos hν ht)
  have heq : ∀ t ∈ Ioo 0 1,
      deriv (abRawProfile ν) t ^ 2 + (2 * ν + 1) * (abRawProfile ν t / t) ^ 2 =
        deriv w t ^ 2 + (2 * ν + 1) * (w t / t) ^ 2 := by
    intro t ht
    have hfun : abRawProfile ν =ᶠ[𝓝 t] w := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      exact abRawProfile_eq hν (ne_of_lt hs.2)
    have hval : abRawProfile ν t = w t := abRawProfile_eq hν (ne_of_lt ht.2)
    rw [hfun.deriv_eq, hval]
  intro x hx y hy hxy
  change deriv (abRawProfile ν) y ^ 2 + (2 * ν + 1) * (abRawProfile ν y / y) ^ 2 ≤
    deriv (abRawProfile ν) x ^ 2 + (2 * ν + 1) * (abRawProfile ν x / x) ^ 2
  rw [heq y hy, heq x hx]
  exact hmon hx hy hxy

end FourthRatio

end
