module

public import RequestProject.TestPair

/-!
# Dilations and form domains of balls

If `p ∈ H₀¹(B_{r'}(c))` for every `r' > r`, then `p ∈ H₀¹(B_r(c))`.  The proof approximates `p`
by test pairs supported in slightly larger balls and shrinks them by dilations centred at `c`;
dilations are uniformly bounded on test pairs and converge to the identity on each fixed test
pair.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Function
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

variable {N : ℕ}

/-- The dilation `x ↦ c + t⁻¹ (x - c)`. -/
def dilMap (c : RN N) (t : ℝ) (x : RN N) : RN N := c + t⁻¹ • (x - c)

lemma contDiff_dilMap (c : RN N) (t : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dilMap c t) := by
  unfold dilMap; fun_prop

lemma continuous_dilMap (c : RN N) (t : ℝ) : Continuous (dilMap c t) := by
  unfold dilMap; fun_prop

/-- `dilMap c t` as a homeomorphism (`t ≠ 0`). -/
def dilHomeo (c : RN N) {t : ℝ} (ht : t ≠ 0) : RN N ≃ₜ RN N where
  toFun := dilMap c t
  invFun := dilMap c t⁻¹
  left_inv x := by simp [dilMap, smul_smul, ht]
  right_inv x := by simp [dilMap, smul_smul, ht]
  continuous_toFun := continuous_dilMap c t
  continuous_invFun := continuous_dilMap c t⁻¹

lemma dilMap_mem_ball_iff (c : RN N) {t : ℝ} (ht : 0 < t) (x : RN N) (ρ : ℝ) :
    dilMap c t x ∈ ball c ρ ↔ x ∈ ball c (t * ρ) := by
  simp only [mem_ball, dist_eq_norm, dilMap, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_of_pos ht]
  rw [inv_mul_lt_iff₀ ht]

lemma hasFDerivAt_dilMap (c : RN N) (t : ℝ) (x : RN N) :
    HasFDerivAt (dilMap c t) ((t⁻¹ : ℝ) • ContinuousLinearMap.id ℝ (RN N)) x := by
  have h := (((hasFDerivAt_id (𝕜 := ℝ) x).sub_const c).const_smul (t⁻¹ : ℝ)).const_add c
  exact h

/-- Gradient of `φ ∘ dilMap c t`. -/
lemma gradient_comp_dilMap (c : RN N) (t : ℝ) {φ : RN N → ℝ} (hφ : Differentiable ℝ φ)
    (x : RN N) :
    gradient (fun z => φ (dilMap c t z)) x = t⁻¹ • gradient φ (dilMap c t x) := by
  have hφ' : HasGradientAt φ (gradient φ (dilMap c t x)) (dilMap c t x) :=
    (hφ _).hasGradientAt
  rw [hasGradientAt_iff_hasFDerivAt] at hφ'
  have hc := hφ'.comp x (hasFDerivAt_dilMap c t x)
  have hg : HasGradientAt (fun z => φ (dilMap c t z)) (t⁻¹ • gradient φ (dilMap c t x)) x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    convert hc using 1
    · rfl
    · ext v
      change inner ℝ (t⁻¹ • gradient φ (dilMap c t x)) v =
        inner ℝ (gradient φ (dilMap c t x)) (t⁻¹ • v)
      simp only [real_inner_smul_left, inner_smul_right]
  exact hg.gradient

/-- Change of variables for the dilation. -/
lemma integral_comp_dilMap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : RN N) {t : ℝ} (ht : 0 < t) (g : RN N → E) :
    ∫ x, g (dilMap c t x) = t ^ N • ∫ x, g x := by
  have h1 : ∫ x, g (dilMap c t x) = ∫ x, g (c + t⁻¹ • x) := by
    simp only [dilMap]
    exact integral_sub_right_eq_self (fun x => g (c + t⁻¹ • x)) c
  have h2 := MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg (volume : Measure (RN N))
    (fun x => g (c + x)) ht.le
  rw [h1, h2, finrank_euclideanSpace_fin]
  congr 1
  exact integral_add_left_eq_self g c

/-- `L²` norm square of `toLp`. -/
lemma norm_toLp_sq_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {g : RN N → E} (h : MemLp g 2 volume) : ‖h.toLp g‖ ^ 2 = ∫ x, ‖g x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp h] with x hx
  rw [hx, real_inner_self_eq_norm_sq]

/-- Distance between test pairs in terms of integrals. -/
lemma dist_testPair_le {φ ψ : RN N → ℝ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hφc : HasCompactSupport φ) (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) {a : ℝ} (ha : 0 ≤ a)
    (h1 : ∫ x, ‖φ x - ψ x‖ ^ 2 ≤ a ^ 2)
    (h2 : ∫ x, ‖gradient φ x - gradient ψ x‖ ^ 2 ≤ a ^ 2) :
    dist (testPair φ hφ hφc) (testPair ψ hψ hψc) ≤ a := by
  rw [Prod.dist_eq]
  refine max_le ?_ ?_
  · rw [dist_eq_norm]
    simp only [testPair]
    rw [← MemLp.toLp_sub]
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) ha two_ne_zero).mp ?_
    rw [norm_toLp_sq_eq]; exact h1
  · rw [dist_eq_norm]
    simp only [testPair]
    rw [← MemLp.toLp_sub]
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) ha two_ne_zero).mp ?_
    rw [norm_toLp_sq_eq]; exact h2

/-- Integrals controlled by the distance between test pairs. -/
lemma integral_le_dist_testPair {φ ψ : RN N → ℝ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hφc : HasCompactSupport φ) (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) :
    ∫ x, ‖φ x - ψ x‖ ^ 2 ≤ dist (testPair φ hφ hφc) (testPair ψ hψ hψc) ^ 2 ∧
    ∫ x, ‖gradient φ x - gradient ψ x‖ ^ 2 ≤
      dist (testPair φ hφ hφc) (testPair ψ hψ hψc) ^ 2 := by
  rw [Prod.dist_eq]
  constructor
  · have : ∫ x, ‖φ x - ψ x‖ ^ 2 = dist (testPair φ hφ hφc).1 (testPair ψ hψ hψc).1 ^ 2 := by
      rw [dist_eq_norm]; simp only [testPair]; rw [← MemLp.toLp_sub, norm_toLp_sq_eq]; rfl
    rw [this]
    exact pow_le_pow_left₀ dist_nonneg (le_max_left _ _) 2
  · have : ∫ x, ‖gradient φ x - gradient ψ x‖ ^ 2 =
        dist (testPair φ hφ hφc).2 (testPair ψ hψ hψc).2 ^ 2 := by
      rw [dist_eq_norm]; simp only [testPair]; rw [← MemLp.toLp_sub, norm_toLp_sq_eq]; rfl
    rw [this]
    exact pow_le_pow_left₀ dist_nonneg (le_max_right _ _) 2

section DilTest

variable (c : RN N) {t : ℝ}

lemma contDiff_dil {φ : RN N → ℝ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => φ (dilMap c t x)) :=
  hφ.comp (contDiff_dilMap c t)

lemma hasCompactSupport_dil (ht : t ≠ 0) {φ : RN N → ℝ} (hc : HasCompactSupport φ) :
    HasCompactSupport (fun x => φ (dilMap c t x)) :=
  hc.comp_homeomorph (dilHomeo c ht)

lemma tsupport_dil_subset (ht : 0 < t) {φ : RN N → ℝ} {ρ : ℝ} (hs : tsupport φ ⊆ ball c ρ) :
    tsupport (fun x => φ (dilMap c t x)) ⊆ ball c (t * ρ) := by
  intro x hx
  have : x ∈ dilHomeo c ht.ne' ⁻¹' tsupport φ := by
    rw [← tsupport_comp_eq_preimage]; exact hx
  exact (dilMap_mem_ball_iff c ht x ρ).mp (hs this)

end DilTest

/-- Dilations by `t ∈ [1/2, 1]` are Lipschitz (constant `2`) on test pairs. -/
lemma dist_dil_testPair_le (c : RN N) {t : ℝ} (ht0 : 0 < t) (ht : 1 / 2 ≤ t) (ht1 : t ≤ 1)
    {φ ψ : RN N → ℝ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hφc : HasCompactSupport φ) (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) :
    dist (testPair _ (contDiff_dil c hφ) (hasCompactSupport_dil c ht0.ne' hφc))
      (testPair _ (contDiff_dil c hψ) (hasCompactSupport_dil c ht0.ne' hψc)) ≤
      2 * dist (testPair φ hφ hφc) (testPair ψ hψ hψc) := by
  obtain ⟨i1, i2⟩ := integral_le_dist_testPair hφ hφc hψ hψc
  set d := dist (testPair φ hφ hφc) (testPair ψ hψ hψc)
  have htN : t ^ N ≤ 1 := pow_le_one₀ ht0.le ht1
  have htN0 : 0 ≤ t ^ N := by positivity
  refine dist_testPair_le _ _ _ _ (by positivity) ?_ ?_
  · rw [integral_comp_dilMap c ht0 (fun x => ‖φ x - ψ x‖ ^ 2), smul_eq_mul]
    have h0 : 0 ≤ ∫ x, ‖φ x - ψ x‖ ^ 2 := integral_nonneg fun _ => by positivity
    calc t ^ N * ∫ x, ‖φ x - ψ x‖ ^ 2 ≤ 1 * d ^ 2 := mul_le_mul htN i1 h0 zero_le_one
      _ ≤ (2 * d) ^ 2 := by nlinarith [sq_nonneg d]
  · have hd : Differentiable ℝ φ := hφ.differentiable (by simp)
    have hd' : Differentiable ℝ ψ := hψ.differentiable (by simp)
    simp_rw [gradient_comp_dilMap c t hd, gradient_comp_dilMap c t hd', ← smul_sub, norm_smul,
      mul_pow]
    rw [integral_const_mul,
      integral_comp_dilMap c ht0 (fun x => ‖gradient φ x - gradient ψ x‖ ^ 2), smul_eq_mul]
    have h0 : 0 ≤ ∫ x, ‖gradient φ x - gradient ψ x‖ ^ 2 := integral_nonneg fun _ => by positivity
    have hinv : ‖t⁻¹‖ ^ 2 ≤ 4 := by
      rw [Real.norm_eq_abs, abs_inv, abs_of_pos ht0, inv_pow]
      rw [inv_le_comm₀ (by positivity) (by norm_num)]
      nlinarith
    calc ‖t⁻¹‖ ^ 2 * (t ^ N * ∫ x, ‖gradient φ x - gradient ψ x‖ ^ 2) ≤ 4 * (1 * d ^ 2) :=
          mul_le_mul hinv (mul_le_mul htN i2 h0 zero_le_one) (by positivity) (by norm_num)
      _ = 2 ^ 2 * d ^ 2 := by ring

/-- Dominated convergence for dilations of a continuous compactly supported function. -/
lemma tendsto_integral_dil {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c : RN N) {g : RN N → E} (hg : Continuous g) (hc : HasCompactSupport g)
    {t a : ℕ → ℝ} (ht0 : ∀ n, 0 < t n) (ht : Tendsto t atTop (𝓝 1))
    (ha : Tendsto a atTop (𝓝 1)) :
    Tendsto (fun n => ∫ x, ‖a n • g (dilMap c (t n) x) - g x‖ ^ 2) atTop (𝓝 0) := by
  obtain ⟨M, hM⟩ := hg.bounded_above_of_compact_support hc
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall c
  set R' := max R 0 with hR'
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM c)
  have hsupp : ∀ y, g y ≠ 0 → ‖y - c‖ ≤ R' := fun y hy => by
    have := mem_closedBall.mp (hR (subset_tsupport _ hy))
    rw [dist_eq_norm] at this
    exact this.trans (le_max_left _ _)
  have hev : ∀ᶠ n in atTop, t n < 2 ∧ a n ∈ Set.Ioo (0 : ℝ) 2 :=
    (ht.eventually (gt_mem_nhds (by norm_num : (1 : ℝ) < 2))).and
      (ha.eventually (Ioo_mem_nhds (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) < 2)))
  have hlim0 : (0 : ℝ) = ∫ x, (fun x : RN N => ‖(1 : ℝ) • g (dilMap c 1 x) - g x‖ ^ 2) x := by
    simp [dilMap]
  rw [hlim0]
  refine tendsto_integral_filter_of_dominated_convergence
    (Set.indicator (closedBall c (2 * R')) (fun _ => (3 * M) ^ 2)) ?_ ?_ ?_ ?_
  · refine Eventually.of_forall fun n => ?_
    exact (((continuous_const.smul (hg.comp (continuous_dilMap c (t n)))).sub hg).norm.pow 2
      ).aestronglyMeasurable
  · filter_upwards [hev] with n hn
    refine Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    by_cases hx : x ∈ closedBall c (2 * R')
    · rw [Set.indicator_of_mem hx]
      have h1 : ‖a n • g (dilMap c (t n) x) - g x‖ ≤ 3 * M := by
        calc _ ≤ ‖a n • g (dilMap c (t n) x)‖ + ‖g x‖ := norm_sub_le _ _
          _ ≤ 2 * M + M := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos hn.2.1]
            gcongr
            · linarith [hn.2.2]
            · exact hM _
            · exact hM _
          _ = 3 * M := by ring
      exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    · rw [Set.indicator_of_notMem hx]
      rw [mem_closedBall, dist_eq_norm, not_le] at hx
      have hgx : g x = 0 := by
        by_contra h
        have := hsupp x h
        have : 0 ≤ R' := le_max_right _ _
        linarith
      have hgd : g (dilMap c (t n) x) = 0 := by
        by_contra h
        have h2 := hsupp _ h
        simp only [dilMap, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_inv,
          abs_of_pos (ht0 n)] at h2
        rw [inv_mul_le_iff₀ (ht0 n)] at h2
        have : 0 ≤ R' := le_max_right _ _
        nlinarith [hn.1]
      simp [hgx, hgd]
  · exact (integrableOn_const (C := (3 * M) ^ 2)
      (measure_closedBall_lt_top (μ := (volume : Measure (RN N))) (x := c) (r := 2 * R')).ne
      ).integrable_indicator measurableSet_closedBall
  · refine Eventually.of_forall fun x => ?_
    have hd : Tendsto (fun n => dilMap c (t n) x) atTop (𝓝 (dilMap c 1 x)) :=
      tendsto_const_nhds.add ((ht.inv₀ one_ne_zero).smul tendsto_const_nhds)
    exact ((ha.smul ((hg.tendsto _).comp hd)).sub tendsto_const_nhds).norm.pow 2

/-- For a fixed test pair, dilations converge to the identity as `t → 1`. -/
lemma tendsto_dil_testPair (c : RN N) {φ : RN N → ℝ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (hφc : HasCompactSupport φ)
    {t : ℕ → ℝ} (ht0 : ∀ n, 0 < t n) (ht : Tendsto t atTop (𝓝 1)) :
    Tendsto (fun n => testPair _ (contDiff_dil c (t := t n) hφ)
      (hasCompactSupport_dil c (ht0 n).ne' hφc)) atTop (𝓝 (testPair φ hφ hφc)) := by
  have hd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have h1 := tendsto_integral_dil c hφ.continuous hφc ht0 ht (tendsto_const_nhds (x := (1 : ℝ)))
  have h2 := tendsto_integral_dil c (continuous_gradient_of_contDiff hφ)
    (hasCompactSupport_gradient hφc) ht0 ht ((ht.inv₀ one_ne_zero).trans (by simp))
  simp only [one_smul] at h1
  rw [tendsto_iff_dist_tendsto_zero]
  have hs : Tendsto (fun n => Real.sqrt ((∫ x, ‖φ (dilMap c (t n) x) - φ x‖ ^ 2) +
      ∫ x, ‖(t n)⁻¹ • gradient φ (dilMap c (t n) x) - gradient φ x‖ ^ 2)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, zero_add, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto _).comp (h1.add h2)
  refine squeeze_zero (fun _ => dist_nonneg) (fun n => ?_) hs
  have i1 : 0 ≤ ∫ x, ‖φ (dilMap c (t n) x) - φ x‖ ^ 2 := integral_nonneg fun _ => by positivity
  have i2 : 0 ≤ ∫ x, ‖(t n)⁻¹ • gradient φ (dilMap c (t n) x) - gradient φ x‖ ^ 2 :=
    integral_nonneg fun _ => by positivity
  refine dist_testPair_le _ _ _ _ (Real.sqrt_nonneg _) ?_ ?_
  · rw [Real.sq_sqrt (by positivity)]; linarith
  · rw [Real.sq_sqrt (by positivity)]
    simp_rw [gradient_comp_dilMap c (t n) hd]
    linarith

/-- Elements of `H_D` are approximated by test pairs supported in `D`. -/
lemma exists_testPair_near_of_mem_H {D : Set (RN N)} {p : Amb N} (hp : p ∈ H D) {δ : ℝ}
    (hδ : 0 < δ) : ∃ (ψ : RN N → ℝ) (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
      (hψc : HasCompactSupport ψ), tsupport ψ ⊆ D ∧ dist p (testPair ψ hψ hψc) < δ := by
  rw [← SetLike.mem_coe, H_eq_closure, Metric.mem_closure_iff] at hp
  obtain ⟨q, hq, hpq⟩ := hp δ hδ
  obtain ⟨ψ, hψ, hψc, hs, rfl⟩ := eq_testPair hq
  exact ⟨ψ, hψ, hψc, hs, hpq⟩

/-- **Dilation lemma.** An element of `H₀¹(B_{r'}(c))` for every `r' > r` lies in `H₀¹(B_r(c))`. -/
theorem mem_H_ball_of_forall_gt {c : RN N} {r : ℝ} (hr : 0 < r) {p : Amb N}
    (hp : ∀ r' > r, p ∈ H (ball c r')) : p ∈ H (ball c r) := by
  rw [← SetLike.mem_coe, H_eq_closure, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨ψ₀, h₀, h₀c, -, hd₀⟩ := exists_testPair_near_of_mem_H (hp (2 * r) (by linarith))
    (by positivity : 0 < ε / 8)
  set s : ℕ → ℝ := fun k => r / (r + 1 / ((k : ℝ) + 1)) with hs_def
  have hpos : ∀ k : ℕ, 0 < r + 1 / ((k : ℝ) + 1) := fun k => by positivity
  have hs0 : ∀ k, 0 < s k := fun k => div_pos hr (hpos k)
  have hs1 : ∀ k, s k ≤ 1 := fun k =>
    (div_le_one (hpos k)).mpr (le_add_of_nonneg_right (by positivity))
  have hslim : Tendsto s atTop (𝓝 1) := by
    have h : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have := (tendsto_const_nhds (x := r)).div (tendsto_const_nhds.add h) (by linarith : r + 0 ≠ 0)
    rw [add_zero, div_self hr.ne'] at this
    exact this
  have hev := ((tendsto_dil_testPair c h₀ h₀c hs0 hslim).eventually
    (Metric.ball_mem_nhds _ (by positivity : 0 < ε / 8))).and
    (hslim.eventually (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)))
  obtain ⟨K, hK⟩ := hev.exists
  obtain ⟨ψ₁, h₁, h₁c, hsupp₁, hd₁⟩ := exists_testPair_near_of_mem_H
    (hp (r + 1 / ((K : ℝ) + 1)) (by linarith [hpos K, (by positivity : 0 < 1 / ((K : ℝ) + 1))]))
    (by positivity : 0 < ε / 8)
  refine ⟨testPair _ (contDiff_dil c (t := s K) h₁) (hasCompactSupport_dil c (hs0 K).ne' h₁c),
    testPair_mem _ _ ?_, ?_⟩
  · have := tsupport_dil_subset c (hs0 K) hsupp₁
    have heq : s K * (r + 1 / ((K : ℝ) + 1)) = r := by
      simp only [hs_def]; field_simp
    rwa [heq] at this
  · have hL := dist_dil_testPair_le c (hs0 K) (le_of_lt hK.2) (hs1 K) h₀ h₀c h₁ h₁c
    have hK1 := hK.1
    have h01 : dist (testPair ψ₀ h₀ h₀c) (testPair ψ₁ h₁ h₁c) < ε / 4 := by
      have := dist_triangle_left (testPair ψ₀ h₀ h₀c) (testPair ψ₁ h₁ h₁c) p
      linarith
    calc dist p _ ≤ dist p (testPair ψ₀ h₀ h₀c) + dist (testPair ψ₀ h₀ h₀c)
            (testPair _ (contDiff_dil c (t := s K) h₀) (hasCompactSupport_dil c (hs0 K).ne' h₀c)) +
          dist (testPair _ (contDiff_dil c (t := s K) h₀) (hasCompactSupport_dil c (hs0 K).ne' h₀c))
            (testPair _ (contDiff_dil c (t := s K) h₁) (hasCompactSupport_dil c (hs0 K).ne' h₁c)) :=
          dist_triangle4 _ _ _ _
      _ < ε := by rw [dist_comm] at hK1; linarith

end FourthRatio

end
