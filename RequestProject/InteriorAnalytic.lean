module

public import RequestProject.HelmholtzLift

/-!
# Interior analyticity of weak eigenfunctions (External theorem 2.2, proved)

A weak solution `u ∈ H_D` of `-Δu = λu` in a domain `D` has a representative which is real
analytic in `D`.

Proof: for `λ < 0` (or `u = 0`) the function `u` vanishes.  For `λ ≥ 0`, `u` is a distributional
solution of `Δu + λu = 0` in `D`, so `w(x, t) = u(x) cosh(√λ t)` is weakly harmonic in `D × ℝ`
(`weakHarmonic_lift`).  By Weyl's lemma and the analyticity of harmonic functions
(`weakHarmonic_analytic`), `w` agrees a.e. with a function `g` analytic in `D × ℝ`.  By Fubini,
for almost every `t₀` we get `u(x) = g(x, t₀)/cosh(√λ t₀)` for a.e. `x ∈ D`.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Function Set
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

variable {N : ℕ}

/-- The weak eigenvalue equation tested against test functions supported in `D`. -/
lemma weak_helmholtz {D : Set (RN N)} {u : Amb N} {lam : ℝ} (hu : u ∈ H D)
    (hweak : ∀ φ ∈ H D, qf u φ = lam * l2 u φ) (φ : RN N → ℝ)
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hφD : tsupport φ ⊆ D) :
    ∫ x, (u.1 : RN N → ℝ) x * Laplacian.laplacian φ x =
      -lam * ∫ x, (u.1 : RN N → ℝ) x * φ x := by
  have hp : testPair φ hφ hφc ∈ H D := testGraph_subset_H D (testPair_mem hφ hφc hφD)
  have hwe := hweak _ hp
  have hq : qf u (testPair φ hφ hφc) = -∫ x, (u.1 : RN N → ℝ) x * Laplacian.laplacian φ x := by
    rw [qf, weak_gradient_identity hu φ hφ hφc, MeasureTheory.L2.inner_def]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [lapL2_ae φ hφ hφc] with x h2
    simp only [RCLike.inner_apply, conj_trivial]
    rw [h2, mul_comm]
  have hl : l2 u (testPair φ hφ hφc) = ∫ x, (u.1 : RN N → ℝ) x * φ x := by
    rw [l2, MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (memLp_of_testFun hφ hφc)] with x h2
    simp only [RCLike.inner_apply, conj_trivial]
    simp only [testPair] at *
    rw [h2, mul_comm]
  rw [hq, hl] at hwe
  linarith

/-- **Interior analyticity** of weak solutions of `-Δu = λu` (External theorem 2.2). -/
theorem interior_analytic {D : Set (RN N)} (hDo : IsOpen D) {u : Amb N} {lam : ℝ}
    (hu : u ∈ H D) (hweak : ∀ φ ∈ H D, qf u φ = lam * l2 u φ) :
    ∃ f : RN N → ℝ, AnalyticOnNhd ℝ f D ∧ IsContRep D u f := by
  by_cases h0 : l2 u u = 0
  · -- `u = 0`
    have hu0 : u.1 = 0 := by
      rw [l2] at h0
      exact inner_self_eq_zero.mp h0
    refine ⟨fun _ => 0, fun x _ => analyticAt_const, continuousOn_const, ?_⟩
    refine ae_restrict_of_ae ?_
    filter_upwards [Lp.coeFn_zero ℝ 2 (volume : Measure (RN N))] with x hx
    rw [hu0, hx]
    rfl
  have hl2 : 0 < l2 u u := lt_of_le_of_ne (real_inner_self_nonneg) (Ne.symm h0)
  have hlam : 0 ≤ lam := by
    have h1 := hweak u hu
    have h2 : 0 ≤ qf u u := real_inner_self_nonneg
    by_contra h
    push_neg at h
    nlinarith
  set U : RN N → ℝ := (u.1 : RN N → ℝ)
  have hU : LocallyIntegrable U := (Lp.memLp u.1).locallyIntegrable (by norm_num)
  have hW := weakHarmonic_lift hU hlam (weak_helmholtz hu hweak)
  set c := Real.sqrt lam
  have hV : IsOpen (xpartL N ⁻¹' D) := hDo.preimage (xpartL N).continuous
  obtain ⟨g, hga, hgae⟩ := weakHarmonic_analytic (n := N + 1) (by omega) hV hW
  -- transfer to `ℝ^N × ℝ` and use Fubini
  have h1 := measurePreserving_joinEq.quasiMeasurePreserving.ae hgae
  have h2 := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
    (ν := (volume : Measure (RN N)))).quasiMeasurePreserving.ae h1
  have h3 := Measure.ae_ae_of_ae_prod h2
  obtain ⟨t0, ht0⟩ := h3.exists
  set f : RN N → ℝ := fun x => g (joinEq N (x, t0)) / Real.cosh (c * t0)
  have hcosh : 0 < Real.cosh (c * t0) := Real.cosh_pos _
  have hfa : AnalyticOnNhd ℝ f D := by
    intro x hx
    have hmem : joinL N x + t0 • eLast N ∈ xpartL N ⁻¹' D := by
      rw [← joinEq_eq]; simpa [xpartL_joinEq] using hx
    have haff : AnalyticAt ℝ (fun y => joinL N y + t0 • eLast N) x :=
      (joinL N).analyticAt x |>.add analyticAt_const
    have hcomp : AnalyticAt ℝ (g ∘ fun y => joinL N y + t0 • eLast N) x :=
      AnalyticAt.comp (g := g) (f := fun y => joinL N y + t0 • eLast N) (hga _ hmem) haff
    have e : f = fun y => (g ∘ fun y => joinL N y + t0 • eLast N) y * (Real.cosh (c * t0))⁻¹ := by
      funext y; simp [f, joinEq_eq, div_eq_mul_inv]
    rw [e]
    exact hcomp.mul (analyticAt_const (v := (Real.cosh (c * t0))⁻¹))
  refine ⟨f, hfa, hfa.continuousOn, ?_⟩
  rw [EventuallyEq, ae_restrict_iff' hDo.measurableSet]
  filter_upwards [ht0] with x hx hxD
  have hmem : joinEq N (x, t0) ∈ xpartL N ⁻¹' D := by simpa [xpartL_joinEq] using hxD
  have := hx hmem
  simp only [Prod.swap, liftFun_joinEq] at this
  simp only [f]
  rw [eq_div_iff hcosh.ne']
  exact this

/-- **External theorem 2.2 (interior analyticity), proved.** Weak solutions of `-Δw = λw` in a
domain `D` lying in `H_D` are real analytic in `D`: there is a function `f` which is real analytic
on `D` and agrees with `u` almost everywhere on `D`.  (Only the openness of `D` is used.) -/
theorem ext_analytic {D : Set (RN N)} (hD : IsDomain D) {u : Amb N} {lam : ℝ}
    (hu : u ∈ H D) (hweak : ∀ φ ∈ H D, qf u φ = lam * l2 u φ) :
    ∃ f : RN N → ℝ, AnalyticOnNhd ℝ f D ∧ IsContRep D u f :=
  interior_analytic hD.1.1 hu hweak

end FourthRatio

end
