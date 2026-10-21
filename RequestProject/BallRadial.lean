module

public import RequestProject.BallSym
public import RequestProject.BesselInterlace

/-!
# Radial eigenfunctions of the ball

A weak eigenfunction `u` of `B = B_R(y)` (`R = j_{ν,1}/√a`) that is invariant under all
reflections through `y` has a radial continuous representative.  For such `u` with eigenvalue `μ`
we show `μ = a` or `μ > C_N a`:

* if `u` does not change sign, `μ = λ₁(B) = a`;
* otherwise its representative does not vanish at the centre (isolated zeros of the analytic
  profile and the strong minimum principle), and if `f(y) > 0` the first sphere where `f` vanishes
  bounds a ball `B_ρ` on which `u` is a positive eigenfunction, so `μ = λ₁(B_ρ)` and
  `ρ = j_{ν,1}/√μ`; the negative part of `u` then lives in the annulus `ρ < |x - y| < R`, and
  comparing with the annulus `j_{ν,1}/√μ < |x - y| < j_{ν,2}/√μ` (whose first eigenvalue is `μ`)
  forces `R ≥ j_{ν,2}/√μ`, i.e. `μ ≥ (j_{ν,2}/j_{ν,1})² a > C_N a` by interlacing.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Function Set
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

variable {N : ℕ}

/-- The reflection `σ_{x - x'}` exchanges two points at the same distance from `y`. -/
lemma sigC_swap (y x x' : RN N) (hxx : x ≠ x') (hn : ‖x - y‖ = ‖x' - y‖) :
    sigC y (x - x') x = x' := by
  have hc : x - x' ≠ 0 := sub_ne_zero.mpr hxx
  have hcn : 0 < ‖x - x'‖ := norm_pos_iff.mpr hc
  have key : ⟪x - x', x - y⟫ = ‖x - x'‖ ^ 2 / 2 := by
    have e : x - x' = (x - y) - (x' - y) := by abel
    rw [e]
    generalize x - y = p at hn ⊢
    generalize x' - y = q at hn ⊢
    rw [inner_sub_left, real_inner_self_eq_norm_sq, norm_sub_sq_real, hn, real_inner_comm]
    ring
  have h2 : 2 * (‖x - x'‖ ^ 2 / 2 / ‖x - x'‖ ^ 2) = 1 := by field_simp
  have h3 : x - sigC y (x - x') x = x - x' := by rw [sub_sigC, key, h2, one_smul]
  exact sub_right_injective h3

/-- **Symmetric elements have radial representatives.** -/
lemma radial_of_sym {R : ℝ} (y : RN N) {u : Amb N} {f : RN N → ℝ}
    (hf : IsContRep (ball y R) u f) (hsym : ∀ c : RN N, c ≠ 0 → opC y c u = u) :
    ∀ x ∈ ball y R, ∀ x' ∈ ball y R, ‖x - y‖ = ‖x' - y‖ → f x = f x' := by
  intro x hx x' hx' hn
  by_cases hxx : x = x'
  · rw [hxx]
  set c := x - x' with hcdef
  have hc : c ≠ 0 := sub_ne_zero.mpr hxx
  have hBm : MeasurableSet (ball y R) := isOpen_ball.measurableSet
  have hmaps : MapsTo (sigC y c) (ball y R) (ball y R) := fun z hz => by
    rw [isoMap_mem_ball_iff]; exact hz
  have hrep : IsContRep (ball y R) u (fun z => f (sigC y c z)) := by
    refine ⟨hf.1.comp (continuous_isoMap _ y).continuousOn hmaps, ?_⟩
    have h1 : ∀ᵐ z, z ∈ ball y R → (u.1 : RN N → ℝ) z = f z :=
      (ae_restrict_iff' hBm).mp hf.2
    have h2 := (measurePreserving_isoMap (reflC c) y).quasiMeasurePreserving.ae h1
    rw [EventuallyEq, ae_restrict_iff' hBm]
    have h3 := isoOp_fst_ae (reflC c) y u
    rw [hsym c hc] at h3
    filter_upwards [h2, h3] with z e2 e3 hz
    rw [e3]
    exact e2 (hmaps hz)
  have heq := eqOn_of_contRep isOpen_ball hf hrep hx
  rw [heq, sigC_swap y x x' hxx hn]

/-- A unit vector of `ℝ^N`. -/
lemma exists_unit (hN : 2 ≤ N) : ∃ e : RN N, ‖e‖ = 1 :=
  ⟨EuclideanSpace.single ⟨0, by omega⟩ 1, by simp [PiLp.norm_single]⟩

lemma norm_add_smul_unit {e : RN N} (he : ‖e‖ = 1) (y : RN N) {s : ℝ} (hs : 0 ≤ s) :
    ‖(y + s • e) - y‖ = s := by
  rw [add_sub_cancel_left, norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_nonneg hs]

/-- The radial profile of a radial function. -/
lemma radial_eq_profile {R : ℝ} {y e : RN N} (he : ‖e‖ = 1) {f : RN N → ℝ}
    (hrad : ∀ x ∈ ball y R, ∀ x' ∈ ball y R, ‖x - y‖ = ‖x' - y‖ → f x = f x')
    {x : RN N} (hx : x ∈ ball y R) : f x = f (y + ‖x - y‖ • e) := by
  refine hrad x hx _ ?_ (norm_add_smul_unit he y (norm_nonneg _)).symm
  rw [mem_ball, dist_eq_norm, norm_add_smul_unit he y (norm_nonneg _)]
  simpa [dist_eq_norm] using hx

/-- **The centre value of a sign-changing radial eigenfunction is nonzero.** -/
lemma center_ne_zero (hN : 2 ≤ N) {R : ℝ} (hR : 0 < R) (y : RN N) {f : RN N → ℝ} {μ : ℝ}
    (hμ : 0 ≤ μ) (hfa : AnalyticOnNhd ℝ f (ball y R))
    (hΔ : ∀ x ∈ ball y R, Laplacian.laplacian f x = -μ * f x)
    (hrad : ∀ x ∈ ball y R, ∀ x' ∈ ball y R, ‖x - y‖ = ‖x' - y‖ → f x = f x')
    (hne : ∃ x ∈ ball y R, f x ≠ 0) : f y ≠ 0 := by
  intro hy
  obtain ⟨e, he⟩ := exists_unit hN
  have hyB : y ∈ ball y R := mem_ball_self hR
  set g : ℝ → ℝ := fun s => f (y + s • e) with hgdef
  have hline : AnalyticAt ℝ (fun s : ℝ => y + s • e) 0 :=
    analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  have hga : AnalyticAt ℝ g 0 := by
    have := (hfa y hyB)
    exact AnalyticAt.comp (by simpa using this) hline
  have hfx : ∀ x ∈ ball y R, f x = g ‖x - y‖ := fun x hx => radial_eq_profile he hrad hx
  have hsB : ∀ s, 0 ≤ s → s < R → y + s • e ∈ ball y R := fun s hs hsR => by
    rw [mem_ball, dist_eq_norm, norm_add_smul_unit he y hs]; exact hsR
  rcases hga.eventually_eq_zero_or_eventually_ne_zero with h0 | h0
  · -- `f` vanishes near `y`, hence on `B`
    obtain ⟨ε, hε, hεg⟩ := Metric.eventually_nhds_iff.mp h0
    have hloc : f =ᶠ[𝓝 y] 0 := by
      filter_upwards [ball_mem_nhds y (lt_min hε hR)] with x hx
      have hxB : x ∈ ball y R := ball_subset_ball (min_le_right _ _) hx
      rw [hfx x hxB, Pi.zero_apply]
      apply hεg
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
      have : dist x y < min ε R := hx
      rw [dist_eq_norm] at this
      exact lt_of_lt_of_le this (min_le_left _ _)
    have hz := hfa.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball y R).isPreconnected hyB hloc
    obtain ⟨x, hx, hfx0⟩ := hne
    exact hfx0 (hz hx)
  · -- `g` has no zeros near `0` except `0`: constant sign on `(0, ε)`
    obtain ⟨ε0, hε0, hεg⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp h0)
    set ε := min ε0 R with hεdef
    have hε : 0 < ε := lt_min hε0 hR
    have hgne : ∀ s, 0 < s → s < ε → g s ≠ 0 := fun s hs hsε => by
      refine hεg ?_ hs.ne'
      rw [Real.dist_eq, sub_zero, abs_of_pos hs]
      exact lt_of_lt_of_le hsε (min_le_left _ _)
    have hgc : ContinuousOn g (Icc 0 (ε / 2 + ε / 4)) := by
      have hc : ContinuousOn (fun s : ℝ => y + s • e) (Icc 0 (ε / 2 + ε / 4)) :=
        (continuous_const.add (continuous_id.smul continuous_const)).continuousOn
      refine hfa.continuousOn.comp hc fun s hs => hsB s hs.1 ?_
      have : ε ≤ R := min_le_right _ _
      linarith [hs.2]
    -- sign on `(0, ε)` agrees with that of `g (ε/2)`
    have hsgn : ∀ s, 0 < s → s < ε → 0 < g s * g (ε / 2) := by
      intro s hs hsε
      have h1 := hgne s hs hsε
      have h2 := hgne (ε / 2) (by linarith) (by linarith)
      by_contra hneg
      push_neg at hneg
      have hlt : g s * g (ε / 2) < 0 := lt_of_le_of_ne hneg (mul_ne_zero h1 h2)
      have hcont : ContinuousOn g (uIcc s (ε / 2)) := by
        have hc : ContinuousOn (fun s : ℝ => y + s • e) (uIcc s (ε / 2)) :=
          (continuous_const.add (continuous_id.smul continuous_const)).continuousOn
        refine hfa.continuousOn.comp hc fun t ht => hsB t ?_ ?_
        · rcases le_total s (ε / 2) with h | h
          · rw [uIcc_of_le h] at ht; linarith [ht.1]
          · rw [uIcc_of_ge h] at ht; linarith [ht.1]
        · have : ε ≤ R := min_le_right _ _
          rcases le_total s (ε / 2) with h | h
          · rw [uIcc_of_le h] at ht; linarith [ht.2]
          · rw [uIcc_of_ge h] at ht; linarith [ht.2]
      have h0mem : (0 : ℝ) ∈ uIcc (g s) (g (ε / 2)) := by
        rcases lt_or_gt_of_ne h1 with hs1 | hs1
        · have : 0 < g (ε / 2) := by nlinarith
          exact mem_uIcc.mpr (Or.inl ⟨hs1.le, this.le⟩)
        · have : g (ε / 2) < 0 := by nlinarith
          exact mem_uIcc.mpr (Or.inr ⟨this.le, hs1.le⟩)
      obtain ⟨t, ht, hgt⟩ := intermediate_value_uIcc hcont h0mem
      have ht0 : 0 < t := by
        rcases le_total s (ε / 2) with h | h
        · rw [uIcc_of_le h] at ht; linarith [ht.1]
        · rw [uIcc_of_ge h] at ht; linarith [ht.1]
      have htε : t < ε := by
        rcases le_total s (ε / 2) with h | h
        · rw [uIcc_of_le h] at ht; linarith [ht.2]
        · rw [uIcc_of_ge h] at ht; linarith [ht.2]
      exact hgne t ht0 htε hgt
    -- apply the strong minimum principle to `±f` on `B_ε(y)`
    have hεB : ball y ε ⊆ ball y R := ball_subset_ball (min_le_right _ _)
    have hg2 := hgne (ε / 2) (by linarith) (by linarith)
    set σ : ℝ := if 0 < g (ε / 2) then 1 else -1 with hσ
    have hσg : 0 < σ * g (ε / 2) := by
      by_cases h : 0 < g (ε / 2)
      · simp [σ, h]
      · simp only [σ, if_neg h, neg_one_mul, neg_pos]
        exact lt_of_le_of_ne (not_lt.mp h) hg2
    have hσ2 : σ * σ = 1 := by by_cases h : 0 < g (ε / 2) <;> simp [σ, h]
    have hF2 : ∀ x ∈ ball y ε, ContDiffAt ℝ 2 (σ • f) x := fun x hx =>
      ((hfa x (hεB hx)).contDiffAt).const_smul σ |>.of_le le_top
    have hFnn : ∀ x ∈ ball y ε, 0 ≤ (σ • f) x := by
      intro x hx
      simp only [Pi.smul_apply, smul_eq_mul]
      by_cases hxy : x = y
      · rw [hxy, hy, mul_zero]
      have hs : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
      have hsε : ‖x - y‖ < ε := by simpa [dist_eq_norm] using hx
      rw [hfx x (hεB hx)]
      have hprod := hsgn _ hs hsε
      have h3 : 0 < (σ * g ‖x - y‖) * (σ * g (ε / 2)) := by
        have he : (σ * g ‖x - y‖) * (σ * g (ε / 2)) = (σ * σ) * (g ‖x - y‖ * g (ε / 2)) := by ring
        rw [he, hσ2, one_mul]; exact hprod
      exact (pos_of_mul_pos_left h3 hσg.le).le
    have hFΔ : ∀ x ∈ ball y ε, Laplacian.laplacian (σ • f) x ≤ 0 := by
      intro x hx
      have hc2 : ContDiffAt ℝ 2 f x := ((hfa x (hεB hx)).contDiffAt).of_le le_top
      rw [InnerProductSpace.laplacian_smul σ hc2, hΔ x (hεB hx), smul_eq_mul]
      have := hFnn x hx
      simp only [Pi.smul_apply, smul_eq_mul] at this
      nlinarith
    have hx1 : y + (ε / 2) • e ∈ ball y ε := by
      rw [mem_ball, dist_eq_norm, norm_add_smul_unit he y (by linarith)]; linarith
    have hpos := strong_min_principle isOpen_ball
      ((convex_ball y ε).isConnected (nonempty_ball.mpr hε)) hF2 hFnn hFΔ hx1
      (by simp only [Pi.smul_apply, smul_eq_mul]; exact hσg.ne') y (mem_ball_self hε)
    simp only [Pi.smul_apply, smul_eq_mul, hy, mul_zero] at hpos
    exact lt_irrefl _ hpos

end FourthRatio

end
