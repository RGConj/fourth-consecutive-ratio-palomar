module

public import RequestProject.MaxPrinciple

/-!
# Simplicity of the first eigenvalue

The simplicity part of the "connected sets" clause of the external spectral package is derived
here from the existence of a strictly positive first eigenfunction (`ground_state_pos`, proved in
`RequestProject/MaxPrinciple.lean`),
interior analyticity, Lemma 3.1 and unique continuation:

* a minimiser of the Rayleigh quotient is an eigenfunction (`eigen_of_rayleigh_eq`);
* a first eigenfunction which is `L²`-orthogonal to the positive ground state vanishes
  (`first_eigen_orth_eq_zero`): if it changed sign, its positive part would be a first
  eigenfunction vanishing on the open set where the function is negative, contradicting unique
  continuation; if it does not change sign, it cannot be orthogonal to a positive function.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Function
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

variable {N : ℕ}

/-- If a continuous representative of `w ∈ H_D` is nonnegative on `D`, then `w ≥ 0` a.e. -/
lemma ae_nonneg_of_contRep {D : Set (RN N)} (hDm : MeasurableSet D) {w : Amb N}
    (hw : w ∈ H D) {f : RN N → ℝ} (hf : IsContRep D w f) (hnn : ∀ x ∈ D, 0 ≤ f x) :
    0 ≤ᵐ[volume] (w.1 : RN N → ℝ) := by
  obtain ⟨hw1, -⟩ := mem_vanishOn.mp (H_le_vanishOn D hw)
  rw [EventuallyEq, ae_restrict_iff' hDm.compl] at hw1
  have hf2 := hf.2
  rw [EventuallyEq, ae_restrict_iff' hDm] at hf2
  filter_upwards [hw1, hf2] with x h1 h2
  by_cases hx : x ∈ D
  · rw [Pi.zero_apply, h2 hx]; exact hnn x hx
  · rw [Pi.zero_apply, h1 hx]; rfl

/-- A first eigenfunction which is `L²`-orthogonal to a positive first eigenfunction is zero. -/
lemma first_eigen_orth_eq_zero {D : Set (RN N)} (hD : IsDomain D)
    {u : Amb N} (hu : u ∈ H D) {g : RN N → ℝ} (hg : IsContRep D u g)
    (hgpos : ∀ x ∈ D, 0 < g x) {w : Amb N} (hw : w ∈ H D)
    (hw' : ∀ φ ∈ H D, qf w φ = eigenvalue D 1 * l2 w φ) (horth : l2 w u = 0) : w = 0 := by
  by_contra hw0
  have hDm : MeasurableSet D := hD.1.1.measurableSet
  obtain ⟨f, -, hf⟩ := ext_analytic hD hw hw'
  set P := posSign D f
  set M := negSign D f
  rcases M.eq_empty_or_nonempty with hM | hM
  · -- `w ≥ 0`
    have hnn : ∀ x ∈ D, 0 ≤ f x := by
      intro x hx
      by_contra hlt
      have : x ∈ M := ⟨hx, lt_of_not_ge hlt⟩
      rw [hM] at this
      exact this
    have := l2_pos_of_nonneg hD.1 hw hw0 (ae_nonneg_of_contRep hDm hw hf hnn) hu hg hgpos
    linarith
  rcases P.eq_empty_or_nonempty with hP | hP
  · -- `w ≤ 0`
    have hnn : ∀ x ∈ D, 0 ≤ (-f) x := by
      intro x hx
      by_contra hlt
      have : x ∈ P := ⟨hx, by simp only [Pi.neg_apply, neg_nonneg, not_le] at hlt; exact hlt⟩
      rw [hP] at this
      exact this
    have hfneg : IsContRep D (-w) (-f) := by
      refine ⟨hf.1.neg, ?_⟩
      have := hf.2
      filter_upwards [this, ae_restrict_of_ae (Lp.coeFn_neg w.1)] with x h1 h2
      simp only [Prod.fst_neg, h2, Pi.neg_apply, h1]
    have := l2_pos_of_nonneg hD.1 ((H D).neg_mem hw) (neg_ne_zero.mpr hw0)
      (ae_nonneg_of_contRep hDm ((H D).neg_mem hw) hfneg hnn) hu hg hgpos
    rw [l2_neg_left] at this
    linarith
  -- `w` changes sign
  exact first_eigen_no_sign_change hD hw hw' hf hP hM

/-- **Spectral package, connected sets.** On a domain the first eigenvalue is simple and has a
strictly positive (continuous) eigenfunction.  The positivity part is the external input
`ground_state_pos` (`RequestProject/MaxPrinciple.lean`); simplicity is derived from it. -/
theorem ground_state (hN : 2 ≤ N) {D : Set (RN N)} (hD : IsDomain D) :
    (∀ u v, IsEigenfunction D u (eigenvalue D 1) → IsEigenfunction D v (eigenvalue D 1) →
      ∃ c : ℝ, v = c • u) ∧
    ∃ u f, IsEigenfunction D u (eigenvalue D 1) ∧ IsContRep D u f ∧ ∀ x ∈ D, 0 < f x := by
  obtain ⟨p, g, hp, hg, hgpos⟩ := ground_state_pos hN hD
  refine ⟨?_, p, g, hp, hg, hgpos⟩
  have hpp := l2_self_pos hp.1 hp.2.1
  have hmult : ∀ u, IsEigenfunction D u (eigenvalue D 1) →
      u = (l2 u p / l2 p p) • p := by
    intro u hu
    set c := l2 u p / l2 p p
    have hz := first_eigen_orth_eq_zero hD hp.1 hg hgpos (w := u - c • p)
      ((H D).sub_mem hu.1 ((H D).smul_mem c hp.1))
      (by
        intro φ hφ
        simp only [qf_sub_left, qf_smul_left, l2_sub_left, l2_smul_left]
        rw [hu.2.2 φ hφ, hp.2.2 φ hφ]
        ring)
      (by
        simp only [l2_sub_left, l2_smul_left, c]
        field_simp
        ring)
    exact sub_eq_zero.mp hz
  intro u v hu hv
  have hu' := hmult u hu
  have hv' := hmult v hv
  have ha : l2 u p / l2 p p ≠ 0 := by
    intro h
    rw [h, zero_smul] at hu'
    exact hu.2.1 hu'
  refine ⟨(l2 v p / l2 p p) / (l2 u p / l2 p p), ?_⟩
  calc v = (l2 v p / l2 p p) • p := hv'
    _ = ((l2 v p / l2 p p) / (l2 u p / l2 p p)) • ((l2 u p / l2 p p) • p) := by
      rw [smul_smul, div_mul_cancel₀ _ ha]
    _ = _ := by rw [← hu']

end FourthRatio

end
