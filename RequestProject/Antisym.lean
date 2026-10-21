module

public import RequestProject.HalfBall

/-!
# Antisymmetric elements of `H₀¹(B)` restricted to a half ball

If `p ∈ H₀¹(B)` then the restriction of `p - p ∘ σ_c` to the half ball `B⁺` lies in `H₀¹(B⁺)`.
For a test function `φ` the function `Ψ = φ - φ ∘ σ_c` vanishes on the hyperplane, so it is
dominated by `M Ψ_c` near the hyperplane; the positive part of `Ψ + M Ψ_c` (an element of
`H₀¹(B)` with sign set exactly `B⁺`) lies in `H₀¹(B⁺)`, and subtracting `M Ψ_c|_{B⁺}` gives the
claim.  The general case follows by density.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Function Set
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

variable {N : ℕ}

lemma norm_sub_sigC (y c x : RN N) (hc : c ≠ 0) :
    ‖x - sigC y c x‖ = 2 * |⟪c, x - y⟫| / ‖c‖ := by
  have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hc
  rw [sub_sigC, norm_smul, Real.norm_eq_abs, abs_mul, abs_div, abs_two,
    abs_of_pos (pow_pos hcn 2)]
  field_simp

lemma real_dom {ψ t g m l M : ℝ} (ht : 0 < t) (hm : 0 < m) (hg : m ≤ g) (hl : 0 ≤ l)
    (hψ : |ψ| ≤ l * t) (hM : M = l / m + 1) : 0 < ψ + M * (t * g) := by
  have hM0 : 0 < M := by rw [hM]; positivity
  have e1 : M * (t * m) ≤ M * (t * g) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hg ht.le) hM0.le
  have e2 : M * (t * m) = l * t + t * m := by rw [hM]; field_simp
  have e3 : 0 < t * m := mul_pos ht hm
  have := neg_abs_le ψ
  linarith

/-- Domination of an antisymmetric test function by a multiple of `Ψ_c` on the half ball. -/
lemma antisym_dom (hN : 2 ≤ N) {a : ℝ} (ha : 0 < a) (y : RN N) {c : RN N} (hc : c ≠ 0)
    {Ψ : RN N → ℝ} (hΨs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ) (hΨc : HasCompactSupport Ψ)
    (hΨB : tsupport Ψ ⊆ ball y (annR N a)) (hΨσ : ∀ x, Ψ (sigC y c x) = -Ψ x) :
    ∃ M > 0, ∀ x ∈ ball y (annR N a), 0 < ⟪c, x - y⟫ → 0 < Ψ x + M * deg1Fun N a y c x := by
  have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hc
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hΨc hΨs (by simp)
  have hgc : Continuous fun x : RN N => deg1G N a (‖x - y‖ ^ 2) :=
    (contDiff_deg1Rad hN ha y).continuous
  obtain ⟨m, hm, hmK⟩ : ∃ m > 0, ∀ x ∈ tsupport Ψ, m ≤ deg1G N a (‖x - y‖ ^ 2) := by
    rcases (tsupport Ψ).eq_empty_or_nonempty with hK | hK
    · exact ⟨1, one_pos, by simp [hK]⟩
    obtain ⟨x0, hx0, hmin⟩ := hΨc.isCompact.exists_isMinOn hK hgc.continuousOn
    refine ⟨deg1G N a (‖x0 - y‖ ^ 2), deg1G_pos hN ha ?_, fun x hx => hmin hx⟩
    simpa [dist_eq_norm] using hΨB hx0
  refine ⟨(L : ℝ) / ‖c‖ / m + 1, by positivity, fun x hxB ht => ?_⟩
  have hg : 0 < deg1G N a (‖x - y‖ ^ 2) := deg1G_pos hN ha (by simpa [dist_eq_norm] using hxB)
  have hdF : deg1Fun N a y c x = ⟪c, x - y⟫ * deg1G N a (‖x - y‖ ^ 2) := rfl
  rw [hdF]
  by_cases hxK : x ∈ tsupport Ψ
  · refine real_dom ht hm (hmK x hxK) (by positivity) ?_ rfl
    have h := hL.dist_le_mul x (sigC y c x)
    rw [Real.dist_eq, hΨσ, dist_eq_norm, norm_sub_sigC y c x hc, abs_of_pos ht] at h
    have e0 : |Ψ x - -Ψ x| = 2 * |Ψ x| := by
      rw [sub_neg_eq_add, ← two_mul, abs_mul, abs_two]
    rw [e0] at h
    have e : (L : ℝ) * (2 * ⟪c, x - y⟫ / ‖c‖) = 2 * ((L : ℝ) / ‖c‖ * ⟪c, x - y⟫) := by ring
    linarith
  · rw [image_eq_zero_of_notMem_tsupport hxK, zero_add]
    exact mul_pos (by positivity) (mul_pos ht hg)

/-- The sign set of `Ψ + M Ψ_c` in `B` is the half ball. -/
lemma antisym_posSign (y : RN N) (r : ℝ) {c : RN N} {F : RN N → ℝ}
    (hFσ : ∀ x, F (sigC y c x) = -F x)
    (hFpos : ∀ x ∈ ball y r, 0 < ⟪c, x - y⟫ → 0 < F x) :
    posSign (ball y r) F = halfB y r c := by
  ext x
  simp only [posSign, halfB, mem_inter_iff, mem_setOf_eq]
  constructor
  · rintro ⟨hxB, hFx⟩
    refine ⟨hxB, ?_⟩
    rcases lt_trichotomy 0 ⟪c, x - y⟫ with h | h | h
    · exact h
    · exfalso
      have hσx : sigC y c x = x := by
        have := sub_sigC y c x
        rw [← h, zero_div, mul_zero, zero_smul, sub_eq_zero] at this
        exact this.symm
      have := hFσ x
      rw [hσx] at this
      linarith
    · exfalso
      have hσB : sigC y c x ∈ ball y r := by
        rw [isoMap_mem_ball_iff]; exact hxB
      have := hFpos (sigC y c x) hσB (by rw [inner_sigC]; linarith)
      rw [hFσ] at this
      linarith
  · rintro ⟨hxB, ht⟩
    exact ⟨hxB, hFpos x hxB ht⟩

/-- The test-function case. -/
lemma restrict_antisym_test (hN : 2 ≤ N) {a : ℝ} (ha : 0 < a) (y : RN N) {c : RN N}
    (hc : c ≠ 0) {p : Amb N} (hp : p ∈ testGraph (ball y (annR N a))) :
    restrictTo (halfB y (annR N a) c) (p - opC y c p) ∈ H (halfB y (annR N a) c) := by
  have hpH : p ∈ H (ball y (annR N a)) := testGraph_subset_H _ hp
  obtain ⟨φ, hφ, hφc, hφs, h1, h2⟩ := hp
  have hR := annR_pos hN ha
  have hBm : MeasurableSet (ball y (annR N a)) := isOpen_ball.measurableSet
  have hSm : MeasurableSet (halfB y (annR N a) c) := (isOpen_halfB _ _ _).measurableSet
  have hσs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (sigC y c) :=
    contDiff_const.add (((reflC c).toContinuousLinearEquiv : RN N →L[ℝ] RN N).contDiff.comp
      (contDiff_id.sub contDiff_const))
  obtain ⟨Ψ, hΨdef⟩ : ∃ Ψ : RN N → ℝ, Ψ = fun x => φ x - φ (sigC y c x) := ⟨_, rfl⟩
  have hΨσ : ∀ x, Ψ (sigC y c x) = -Ψ x := fun x => by
    simp only [hΨdef, sigC_sigC]; ring
  have hΨs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ := hΨdef ▸ hφ.sub (hφ.comp hσs)
  have hΨc : HasCompactSupport Ψ :=
    hΨdef ▸ hφc.sub (hφc.comp_homeomorph (isoHomeo (reflC c) y))
  have hKB : tsupport φ ∪ (isoHomeo (reflC c) y) ⁻¹' tsupport φ ⊆ ball y (annR N a) := by
    rintro x (hx | hx)
    · exact hφs hx
    · have := hφs hx
      rwa [isoHomeo_apply, isoMap_mem_ball_iff] at this
  have hΨB : tsupport Ψ ⊆ ball y (annR N a) := by
    rw [hΨdef]
    refine (tsupport_sub _ _).trans ((union_subset_union_right _ ?_).trans hKB)
    exact (tsupport_comp_eq_preimage φ (isoHomeo (reflC c) y)).le
  have hΨB' : ∀ x ∉ ball y (annR N a), Ψ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun h => hx (hΨB h))
  obtain ⟨M, hM, hdom⟩ := antisym_dom hN ha y hc hΨs hΨc hΨB hΨσ
  obtain ⟨F, hFdef⟩ : ∃ F : RN N → ℝ, F = fun x => Ψ x + M * deg1Fun N a y c x := ⟨_, rfl⟩
  have hFc : Continuous F := hFdef ▸ hΨs.continuous.add
    (continuous_const.mul (contDiff_deg1Fun hN ha y c).continuous)
  have hFσ : ∀ x, F (sigC y c x) = -F x := fun x => by
    simp only [hFdef, hΨσ, deg1Fun_sigC]; ring
  have hFpos : ∀ x ∈ ball y (annR N a), 0 < ⟪c, x - y⟫ → 0 < F x := fun x hx ht => by
    rw [hFdef]; exact hdom x hx ht
  have hsign := antisym_posSign y (annR N a) hFσ hFpos
  obtain ⟨wB, hwH, hw1, hw2, -⟩ := exists_deg1' hN ha y c
  obtain ⟨wh, hwhH, hwh1, hwh2⟩ := exists_half_deg1 hN ha y c
  obtain ⟨q, hqdef⟩ : ∃ q, q = p - opC y c p := ⟨_, rfl⟩
  rw [← hqdef]
  have hqH : q ∈ H (ball y (annR N a)) := hqdef ▸ (H _).sub_mem hpH (isoOp_mem_H _ y _ hpH)
  have hq1 : (q.1 : RN N → ℝ) =ᵐ[volume] Ψ := by
    have hq := (measurePreserving_isoMap (reflC c) y).quasiMeasurePreserving.ae_eq_comp h1
    filter_upwards [Lp.coeFn_sub p.1 (opC y c p).1, isoOp_fst_ae (reflC c) y p, h1, hq]
      with x e1 e2 e3 e4
    rw [hqdef, Prod.fst_sub, e1, Pi.sub_apply, e2, e3, hΨdef]
    simp only [Function.comp_apply] at e4
    rw [e4]
  obtain ⟨v, hvdef⟩ : ∃ v, v = q + M • wB := ⟨_, rfl⟩
  have hvH : v ∈ H (ball y (annR N a)) := hvdef ▸ (H _).add_mem hqH ((H _).smul_mem M hwH)
  have hv1 : (v.1 : RN N → ℝ) =ᵐ[volume]
      fun x => Ψ x + M * (ball y (annR N a)).indicator (deg1Fun N a y c) x := by
    filter_upwards [Lp.coeFn_add q.1 (M • wB).1, Lp.coeFn_smul M wB.1, hq1, hw1]
      with x e1 e2 e3 e4
    rw [hvdef, Prod.fst_add, e1, Pi.add_apply, Prod.smul_fst, e2, Pi.smul_apply, e3, e4,
      smul_eq_mul]
  have hv2 : (v.2 : RN N → RN N) =ᵐ[volume]
      fun x => (q.2 : RN N → RN N) x +
        M • (ball y (annR N a)).indicator (gradient (deg1Fun N a y c)) x := by
    filter_upwards [Lp.coeFn_add q.2 (M • wB).2, Lp.coeFn_smul M wB.2, hw2]
      with x e1 e2 e3
    rw [hvdef, Prod.snd_add, e1, Pi.add_apply, Prod.smul_snd, e2, Pi.smul_apply, e3]
  have hrep : IsContRep (ball y (annR N a)) v F := by
    refine ⟨hFc.continuousOn, ?_⟩
    rw [EventuallyEq, ae_restrict_iff' hBm]
    filter_upwards [hv1] with x hx hxB
    rw [hx, indicator_of_mem hxB, hFdef]
  have hpos := posPart_mem_H_posSign (isDomain_ball y hR).1 hvH hrep
  rw [hsign] at hpos
  have hSB : halfB y (annR N a) c ⊆ ball y (annR N a) := halfB_subset _ _ _
  have hFS : ∀ x ∈ ball y (annR N a), x ∉ halfB y (annR N a) c → F x ≤ 0 := fun x hxB hxS => by
    by_contra h
    exact hxS (hsign ▸ ⟨hxB, lt_of_not_ge h⟩)
  have heq : restrictTo (halfB y (annR N a) c) q = posPart v - M • wh := by
    refine Prod.ext (Lp.ext ?_) (Lp.ext ?_)
    · filter_upwards [restrictTo_fst_ae hSm q, Lp.coeFn_sub (posPart v).1 (M • wh).1,
        Lp.coeFn_smul M wh.1, posPart_fst_ae' v, hv1, hq1, hwh1] with x e1 e2 e3 e4 e5 e6 e7
      rw [Prod.fst_sub, e1, e2, Pi.sub_apply, Prod.smul_fst, e3, Pi.smul_apply, e4, e5, e7,
        smul_eq_mul]
      by_cases hxS : x ∈ halfB y (annR N a) c
      · have hxB := hSB hxS
        rw [indicator_of_mem hxS, indicator_of_mem hxB, indicator_of_mem hxS, e6]
        have : 0 < F x := hFpos x hxB hxS.2
        rw [hFdef] at this
        rw [max_eq_left this.le]; ring
      · rw [indicator_of_notMem hxS, indicator_of_notMem hxS]
        by_cases hxB : x ∈ ball y (annR N a)
        · have := hFS x hxB hxS
          rw [hFdef] at this
          rw [indicator_of_mem hxB, max_eq_right this]; ring
        · rw [indicator_of_notMem hxB, hΨB' x hxB]; simp
    · filter_upwards [restrictTo_snd_ae hSm q, Lp.coeFn_sub (posPart v).2 (M • wh).2,
        Lp.coeFn_smul M wh.2, posPart_snd_ae_ite v, hv1, hv2, hwh2] with x e1 e2 e3 e4 e5 e6 e7
      rw [Prod.snd_sub, e1, e2, Pi.sub_apply, Prod.smul_snd, e3, Pi.smul_apply, e4, e5, e6, e7]
      by_cases hxS : x ∈ halfB y (annR N a) c
      · have hxB := hSB hxS
        rw [indicator_of_mem hxS, indicator_of_mem hxB, indicator_of_mem hxS, indicator_of_mem hxB]
        have : 0 < F x := hFpos x hxB hxS.2
        rw [hFdef] at this
        rw [if_pos this, one_smul]; abel
      · rw [indicator_of_notMem hxS, indicator_of_notMem hxS]
        by_cases hxB : x ∈ ball y (annR N a)
        · have := hFS x hxB hxS
          rw [hFdef] at this
          rw [indicator_of_mem hxB, if_neg (not_lt.mpr this)]; simp
        · rw [indicator_of_notMem hxB, hΨB' x hxB]; simp
  rw [heq]
  exact (H _).sub_mem hpos ((H _).smul_mem M hwhH)

/-- **Antisymmetrised elements restrict to the half ball.** For `p ∈ H₀¹(B)`, the restriction of
`p - p ∘ σ_c` to `B⁺` lies in `H₀¹(B⁺)`. -/
theorem restrict_antisym (hN : 2 ≤ N) {a : ℝ} (ha : 0 < a) (y : RN N) {c : RN N}
    (hc : c ≠ 0) {p : Amb N} (hp : p ∈ H (ball y (annR N a))) :
    restrictTo (halfB y (annR N a) c) (p - opC y c p) ∈ H (halfB y (annR N a) c) := by
  obtain ⟨q, hqT, hq⟩ := exists_seq_testGraph hp
  have hSm : MeasurableSet (halfB y (annR N a) c) := (isOpen_halfB _ _ _).measurableSet
  set Φ : Amb N →L[ℝ] Amb N := (restrictCLM hSm).comp (ContinuousLinearMap.id ℝ _ - opC y c)
  have hΦ : ∀ u, Φ u = restrictTo (halfB y (annR N a) c) (u - opC y c u) := fun u => rfl
  have := ((Φ.continuous.tendsto p).comp hq)
  rw [hΦ] at this
  exact mem_H_of_tendsto (fun n => by
    simpa [Function.comp_apply, hΦ] using restrict_antisym_test hN ha y hc (hqT n)) this

end FourthRatio

end
