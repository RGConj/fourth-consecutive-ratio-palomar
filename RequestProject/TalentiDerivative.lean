module

public import RequestProject.TalentiFiniteIncrement
public import RequestProject.InitialMass
public import Mathlib.Analysis.Calculus.Monotone
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-! # Talenti's a.e. derivative inequality for the actual decreasing profile -/

@[expose] public section
open Set MeasureTheory Filter Topology Metric
open scoped ENNReal RealInnerProductSpace
noncomputable section
namespace FourthRatio
variable {N : ℕ}

/-- Passing to one-sided difference quotients in the actual finite-increment
estimate gives the differential inequality at every differentiability point. -/
theorem talenti_derivative_bound (hN : 2 ≤ N)
    {D : Set (RN N)} (hD : MeasurableSet D) (hfin : volume D ≠ ∞)
    {p : Amb N} {lam : ℝ} (hp : IsEigenfunction D p lam) (hlam : 0 ≤ lam)
    (hp0 : ∀ᵐ x, 0 ≤ (p.1 : RN N → ℝ) x)
    {s d : ℝ} (hs : 0 < s)
    (hd : HasDerivAt (decreasingProfile volume (p.1 : RN N → ℝ)) d s) :
    -(lam * initialMass (decreasingProfile volume (p.1 : RN N → ℝ)) s /
      ((N : ℝ) * s ^ (1 - (N : ℝ)⁻¹) * volume.real (ball (0 : RN N) 1) ^ (N : ℝ)⁻¹) ^ 2) ≤ d := by
  let f := decreasingProfile volume (p.1 : RN N → ℝ)
  let K := (N : ℝ) * s ^ (1 - (N : ℝ)⁻¹) * volume.real (ball (0 : RN N) 1) ^ (N : ℝ)⁻¹
  have hpi := (integrable_components_of_mem_H hD hfin hp.1).1
  have hfi : IntegrableOn f (Ioi (0 : ℝ)) := decreasingProfile_integrableOn_ae hpi hp0
  have hUc : ContinuousAt (initialMass f) s :=
    (initialMass_continuousOn hfi).continuousAt (isOpen_Ioi.mem_nhds hs)
  have hplus : Tendsto (fun t : ℝ => s + t) (𝓝[>] 0) (𝓝 s) := by
    simpa only [add_zero] using
      ((show Continuous (fun t : ℝ => s + t) from continuous_const.add continuous_id).tendsto 0).mono_left nhdsWithin_le_nhds
  have hUlim := hUc.tendsto.comp hplus
  have hlo : Tendsto (fun t : ℝ => -(lam * initialMass f (s + t) / K ^ 2))
      (𝓝[>] 0) (𝓝 (-(lam * initialMass f s / K ^ 2))) :=
    ((hUlim.const_mul lam).div_const (K ^ 2)).neg
  have hhi : Tendsto (fun t : ℝ => (f (s + t) - f s) / t) (𝓝[>] 0) (𝓝 d) := by
    simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using hd.tendsto_slope_zero_right
  apply le_of_tendsto_of_tendsto hlo hhi
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hst : s < s + t := lt_add_of_pos_right s ht
  have hstpos : 0 < s + t := hs.trans hst
  have hanti : f (s + t) ≤ f s := decreasingProfile_antitoneOn hpi hs hstpos hst.le
  by_cases hgt : f (s + t) < f s
  · have htal := talenti_finite_increment hN hD hfin hp hlam hp0 hs hst hgt
    change f s - f (s + t) ≤ lam * ((s + t) - s) * initialMass f (s + t) / K ^ 2 at htal
    rw [add_sub_cancel_left] at htal
    apply (le_div_iff₀ ht).mpr
    have htal' : f s - f (s + t) ≤ (lam * initialMass f (s + t) / K ^ 2) * t := by
      convert htal using 1 <;> ring
    linarith [htal']
  · have heq : f (s + t) = f s := le_antisymm hanti (not_lt.mp hgt)
    rw [heq, sub_self, zero_div]
    exact neg_nonpos.mpr (div_nonneg (mul_nonneg hlam
      (integral_nonneg (decreasingProfile_nonneg _ _))) (sq_nonneg _))

/-- The actual eigenfunction rearrangement satisfies Talenti's inequality a.e.
on its positive volume axis. -/
theorem talenti_derivative_bound_ae (hN : 2 ≤ N)
    {D : Set (RN N)} (hD : MeasurableSet D) (hfin : volume D ≠ ∞)
    {p : Amb N} {lam : ℝ} (hp : IsEigenfunction D p lam) (hlam : 0 ≤ lam)
    (hp0 : ∀ᵐ x, 0 ≤ (p.1 : RN N → ℝ) x) :
    ∀ᵐ s : ℝ, 0 < s →
      HasDerivAt (decreasingProfile volume (p.1 : RN N → ℝ))
        (deriv (decreasingProfile volume (p.1 : RN N → ℝ)) s) s ∧
      -(lam * initialMass (decreasingProfile volume (p.1 : RN N → ℝ)) s /
        ((N : ℝ) * s ^ (1 - (N : ℝ)⁻¹) * volume.real (ball (0 : RN N) 1) ^ (N : ℝ)⁻¹) ^ 2) ≤
          deriv (decreasingProfile volume (p.1 : RN N → ℝ)) s := by
  let f := decreasingProfile volume (p.1 : RN N → ℝ)
  have hpi := (integrable_components_of_mem_H hD hfin hp.1).1
  have hanti : AntitoneOn f (Ioi 0) := decreasingProfile_antitoneOn hpi
  have hm : MonotoneOn (fun s => -f s) (Ioi 0) := fun a ha b hb hab => neg_le_neg (hanti ha hb hab)
  filter_upwards [hm.ae_differentiableWithinAt_of_mem] with s hd hs
  have hneg := (hd hs).differentiableAt (isOpen_Ioi.mem_nhds hs)
  have hdiff : DifferentiableAt ℝ f s := by
    have hdd := hneg.neg
    have heq : (-(fun t : ℝ => -f t)) = f := by funext t; simp
    rw [heq] at hdd
    exact hdd
  exact ⟨hdiff.hasDerivAt, talenti_derivative_bound hN hD hfin hp hlam hp0 hs hdiff.hasDerivAt⟩

end FourthRatio
end
