module

public import RequestProject.SpectralAbstract
public import RequestProject.TestPair

/-!
# The spectral theorem for `H_D`, assuming only compactness of the embedding

For a bounded open set `D` the form domain `H_D` satisfies the hypotheses of the abstract
spectral theorem (`RequestProject/SpectralAbstract.lean`) except for the compactness of the
embedding `H_D ↪ L²(D)`:

* `H_D` is closed and the `L²` part is positive definite on it (closability of the gradient);
* Poincaré inequality `‖v‖² ≤ 4R² q(v,v)` for `D ⊆ B_R(0)` (integration by parts against the
  coordinate function `x₁`);
* `H_D` is infinite dimensional for `D` nonempty (bump functions with disjoint supports).

Hence the Dirichlet spectral package follows from the compactness of the embedding
(`spectral_of_compact`).
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Function Set
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

variable {N : ℕ}

/-! ### Poincaré inequality -/

lemma hasCompactSupport_of_vanish {β : Type*} [Zero β] {φ : RN N → β} {F : RN N → ℝ}
    (hc : HasCompactSupport φ)
    (h : ∀ x, φ x = 0 → F x = 0) : HasCompactSupport F :=
  hc.mono' (fun x hx => subset_tsupport φ (fun h0 => hx (h x h0)))

lemma poincare_testFun (hN : 1 ≤ N) {R : ℝ} {φ : RN N → ℝ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (hc : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ closedBall 0 R) :
    ∫ x, φ x ^ 2 ≤ 4 * R ^ 2 * ∫ x, ‖gradient φ x‖ ^ 2 := by
  set e : RN N := EuclideanSpace.single ⟨0, hN⟩ 1 with he_def
  have he : ‖e‖ = 1 := by simp [e]
  set g : RN N → ℝ := fun x => innerSL ℝ e x with hg_def
  have hgd : Differentiable ℝ g := (innerSL ℝ e).differentiable
  have hg' : ∀ x, fderiv ℝ g x e = 1 := by
    intro x
    rw [show g = ⇑(innerSL ℝ e) from rfl, ContinuousLinearMap.fderiv, innerSL_apply_apply,
      real_inner_self_eq_norm_sq, he, one_pow]
  have hgc : Continuous g := (innerSL ℝ e).continuous
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  set d : RN N → ℝ := fun x => fderiv ℝ φ x e with hd_def
  have hdc : Continuous d := (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hfd : Differentiable ℝ (fun x => φ x ^ 2) := hφd.pow 2
  have hf' : ∀ x, fderiv ℝ (fun x => φ x ^ 2) x e = 2 * φ x * d x := by
    intro x
    rw [((hφd x).hasFDerivAt.pow 2).fderiv]
    simp [d]
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (v := e)
    (f := fun x => φ x ^ 2) (g := g)
    (by
      simp_rw [hf']
      exact ((continuous_const.mul hφ.continuous).mul hdc |>.mul hgc).integrable_of_hasCompactSupport
        (hasCompactSupport_of_vanish hc (fun x hx => by simp [hx])))
    (by
      simp_rw [hg']
      exact (hφ.continuous.pow 2 |>.mul continuous_const).integrable_of_hasCompactSupport
        (hasCompactSupport_of_vanish hc (fun x hx => by simp [hx])))
    (by
      exact (hφ.continuous.pow 2 |>.mul hgc).integrable_of_hasCompactSupport
        (hasCompactSupport_of_vanish hc (fun x hx => by simp [hx])))
    (fun x _ => hfd x) (fun x _ => hgd x)
  simp_rw [hg', hf', mul_one] at hibp
  -- hibp : ∫ φ² = -∫ 2 φ d g
  have hdcs : HasCompactSupport d := hc.fderiv_apply (𝕜 := ℝ) e
  have hint_d : Integrable (fun x => d x ^ 2) :=
    (hdc.pow 2).integrable_of_hasCompactSupport
      (hasCompactSupport_of_vanish hdcs (fun x hx => by simp [hx]))
  have hint_f : Integrable (fun x => φ x ^ 2) :=
    (hφ.continuous.pow 2).integrable_of_hasCompactSupport
      (hasCompactSupport_of_vanish hc (fun x hx => by simp [hx]))
  have hint_l : Integrable (fun x => -(2 * φ x * d x * g x)) :=
    (((continuous_const.mul hφ.continuous).mul hdc).mul hgc).neg.integrable_of_hasCompactSupport
      (hasCompactSupport_of_vanish hc (fun x hx => by simp [hx]))
  have hgrad_c := continuous_gradient_of_contDiff hφ
  have hint_g : Integrable (fun x => ‖gradient φ x‖ ^ 2) :=
    (hgrad_c.norm.pow 2).integrable_of_hasCompactSupport
      (hasCompactSupport_of_vanish (hasCompactSupport_gradient hc) (fun x hx => by simp [hx]))
  have hpt : ∀ x, -(2 * φ x * d x * g x) ≤ φ x ^ 2 / 2 + 2 * R ^ 2 * d x ^ 2 := by
    intro x
    by_cases h0 : φ x = 0
    · simp only [h0]; nlinarith [sq_nonneg (R * d x)]
    · have hx : x ∈ closedBall (0 : RN N) R := hsupp (subset_tsupport φ h0)
      have hgx : |g x| ≤ R := by
        calc |g x| = |⟪e, x⟫| := rfl
          _ ≤ ‖e‖ * ‖x‖ := abs_real_inner_le_norm e x
          _ ≤ R := by rw [he, one_mul]; simpa using hx
      have hR2 : g x ^ 2 ≤ R ^ 2 := by
        have := abs_nonneg (g x)
        rw [← sq_abs (g x)]
        nlinarith
      nlinarith [sq_nonneg (φ x + 2 * g x * d x), mul_nonneg (sq_nonneg (d x)) (sub_nonneg.mpr hR2)]
  have hint_s : Integrable (fun x => φ x ^ 2 / 2 + 2 * R ^ 2 * d x ^ 2) :=
    (hint_f.div_const 2).add (hint_d.const_mul (2 * R ^ 2))
  have hmono := integral_mono hint_l hint_s hpt
  have hsplit : ∫ x, (φ x ^ 2 / 2 + 2 * R ^ 2 * d x ^ 2) =
      (∫ x, φ x ^ 2) / 2 + 2 * R ^ 2 * ∫ x, d x ^ 2 := by
    rw [integral_add (hint_f.div_const 2) (hint_d.const_mul _), integral_div, integral_const_mul]
  rw [integral_neg, ← hibp, hsplit] at hmono
  have hdg : ∫ x, d x ^ 2 ≤ ∫ x, ‖gradient φ x‖ ^ 2 := by
    refine integral_mono hint_d hint_g fun x => ?_
    have hdx : d x = ⟪gradient φ x, e⟫ := by
      simp only [d, gradient, InnerProductSpace.toDual_symm_apply]
    have h1 : |d x| ≤ ‖gradient φ x‖ := by
      rw [hdx]
      calc |⟪gradient φ x, e⟫| ≤ ‖gradient φ x‖ * ‖e‖ := abs_real_inner_le_norm _ _
        _ = ‖gradient φ x‖ := by rw [he, mul_one]
    rw [← sq_abs (d x)]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  nlinarith [mul_le_mul_of_nonneg_left hdg (by positivity : (0 : ℝ) ≤ 4 * R ^ 2)]


lemma l2_testPair (φ ψ : RN N → ℝ) (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hφc : HasCompactSupport φ) (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) :
    l2 (testPair φ hφ hφc) (testPair ψ hψ hψc) = ∫ x, φ x * ψ x := by
  rw [l2, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (memLp_of_testFun hφ hφc),
    MemLp.coeFn_toLp (memLp_of_testFun hψ hψc)] with x h1 h2
  simp only [testPair]
  rw [h1, h2]
  simp [mul_comm]

lemma qf_testPair_self (φ : RN N → ℝ) (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hφc : HasCompactSupport φ) :
    qf (testPair φ hφ hφc) (testPair φ hφ hφc) = ∫ x, ‖gradient φ x‖ ^ 2 := by
  rw [qf, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (memLp_gradient_of_testFun hφ hφc)] with x h1
  simp only [testPair]
  rw [h1, real_inner_self_eq_norm_sq]

/-- **Poincaré inequality** on `H_D` for bounded `D`. -/
lemma poincare_H (hN : 1 ≤ N) {D : Set (RN N)} (hb : Bornology.IsBounded D) :
    ∃ C, ∀ v ∈ H D, l2 v v ≤ C * qf v v := by
  obtain ⟨R, hR⟩ := hb.subset_closedBall 0
  refine ⟨4 * R ^ 2, fun v hv => ?_⟩
  have hS : IsClosed {p : Amb N | l2 p p ≤ 4 * R ^ 2 * qf p p} :=
    isClosed_le (continuous_l2.comp (continuous_id.prodMk continuous_id))
      (continuous_const.mul (continuous_qf.comp (continuous_id.prodMk continuous_id)))
  have hsub : testGraph D ⊆ {p : Amb N | l2 p p ≤ 4 * R ^ 2 * qf p p} := by
    intro p hp
    obtain ⟨φ, hφ, hc, hs, rfl⟩ := eq_testPair hp
    simp only [Set.mem_setOf_eq, l2_testPair, qf_testPair_self]
    simpa [sq] using poincare_testFun hN hφ hc (hs.trans hR)
  have hv' : v ∈ closure (testGraph D) := by rw [← H_eq_closure]; exact hv
  exact closure_minimal hsub hS hv'

/-! ### `H_D` is infinite dimensional -/

lemma H_not_finiteDimensional (hN : 1 ≤ N) {D : Set (RN N)} (hD : IsOpen D)
    (hne : D.Nonempty) : ¬ FiniteDimensional ℝ (H D) := by
  intro hfin
  obtain ⟨x, hx⟩ := hne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hD x hx
  obtain ⟨e, he⟩ : ∃ e : RN N, ‖e‖ = 1 := ⟨EuclideanSpace.single ⟨0, hN⟩ 1, by simp⟩
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℝ, a = fun k => (1 / 2 : ℝ) ^ (k + 1) := ⟨_, rfl⟩
  have ha_pos : ∀ k, 0 < a k := fun k => by rw [ha]; positivity
  have ha_half : ∀ k, a k ≤ 1 / 2 := fun k => by
    rw [ha]; exact pow_le_of_le_one (by norm_num) (by norm_num) (by omega) |>.trans (by norm_num)
  have ha_lt : ∀ k l, k < l → a l ≤ a k / 2 := by
    intro k l hkl
    rw [ha]
    have : (1 / 2 : ℝ) ^ (l + 1) ≤ (1 / 2) ^ (k + 2) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    calc (1 / 2 : ℝ) ^ (l + 1) ≤ (1 / 2) ^ (k + 2) := this
      _ = (1 / 2) ^ (k + 1) / 2 := by ring
  obtain ⟨c, hc⟩ : ∃ c : ℕ → RN N, c = fun k => x + (r * a k) • e := ⟨_, rfl⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℕ → ℝ, ρ = fun k => r * a k / 4 := ⟨_, rfl⟩
  have hρpos : ∀ k, 0 < ρ k := fun k => by rw [hρ]; have := ha_pos k; positivity
  have hdist : ∀ k l, dist (c k) (c l) = r * |a k - a l| := by
    intro k l
    rw [hc, dist_eq_norm]
    simp only
    rw [add_sub_add_left_eq_sub, ← sub_smul, norm_smul, he, mul_one, Real.norm_eq_abs,
      ← mul_sub, abs_mul, abs_of_pos hr]
  have hdistx : ∀ k, dist (c k) x = r * a k := by
    intro k
    rw [hc, dist_eq_norm]
    simp only
    rw [add_sub_cancel_left, norm_smul, he, mul_one, Real.norm_eq_abs,
      abs_of_pos (mul_pos hr (ha_pos k))]
  let bump : (k : ℕ) → ContDiffBump (c k) := fun k =>
    ⟨ρ k / 2, ρ k, by have := hρpos k; positivity, by have := hρpos k; linarith⟩
  have hψs : ∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (bump k) := fun k => (bump k).contDiff
  have hψc : ∀ k, HasCompactSupport (bump k) := fun k => (bump k).hasCompactSupport
  have hsupp : ∀ k, support (bump k) = ball (c k) (ρ k) := fun k => (bump k).support_eq
  have htsupp : ∀ k, tsupport (bump k) = closedBall (c k) (ρ k) := fun k => (bump k).tsupport_eq
  have hinD : ∀ k, closedBall (c k) (ρ k) ⊆ D := by
    intro k y hy
    apply hball
    rw [mem_ball]
    have h1 : dist y (c k) ≤ ρ k := hy
    have h3 := ha_half k
    have h4 := ha_pos k
    calc dist y x ≤ dist y (c k) + dist (c k) x := dist_triangle _ _ _
      _ ≤ ρ k + r * a k := add_le_add h1 (hdistx k).le
      _ < r := by rw [hρ]; simp only; nlinarith
  have hdisj : ∀ k l, k < l → Disjoint (ball (c k) (ρ k)) (ball (c l) (ρ l)) := by
    intro k l hkl
    apply Metric.ball_disjoint_ball
    rw [hdist, hρ]
    simp only
    have h1 := ha_lt k l hkl
    have h2 := ha_pos l
    have h3 := ha_pos k
    rw [abs_of_pos (by linarith)]
    nlinarith
  let f : ℕ → Amb N := fun k => testPair (bump k) (hψs k) (hψc k)
  have hfH : ∀ k, f k ∈ H D := fun k =>
    testGraph_subset_H D (testPair_mem _ _ ((htsupp k).le.trans (hinD k)))
  have horth : ∀ k l, k ≠ l → l2 (f k) (f l) = 0 := by
    intro k l hkl
    simp only [f]
    rw [l2_testPair]
    refine integral_eq_zero_of_ae (Eventually.of_forall fun y => ?_)
    show bump k y * bump l y = 0
    by_contra hne
    have hk : y ∈ support (bump k) := left_ne_zero_of_mul hne
    have hl : y ∈ support (bump l) := right_ne_zero_of_mul hne
    rw [hsupp] at hk hl
    rcases lt_or_gt_of_ne hkl with h | h
    · exact Set.disjoint_left.mp (hdisj k l h) hk hl
    · exact Set.disjoint_left.mp (hdisj l k h) hl hk
  have hpos : ∀ k, l2 (f k) (f k) ≠ 0 := by
    intro k
    simp only [f]
    rw [l2_testPair]
    have h1 : bump k (c k) = 1 :=
      (bump k).one_of_mem_closedBall (mem_closedBall_self (by have := hρpos k; positivity))
    refine (Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := c k)
      ((hψs k).continuous.mul (hψs k).continuous) (hψc k).mul_left
      (fun y => mul_self_nonneg _) ?_).ne'
    simp [h1]
  have hli : LinearIndependent ℝ f := by
    rw [linearIndependent_iff']
    intro s g hg i hi
    have h := congrArg (l2 (f i)) hg
    rw [l2_sum_right, l2_zero_right] at h
    simp only [l2_smul_right] at h
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [horth i j (Ne.symm hj), mul_zero])
      (fun h' => absurd hi h')] at h
    exact (mul_eq_zero.mp h).resolve_right (hpos i)
  have hli' : LinearIndependent ℝ (fun k => (⟨f k, hfH k⟩ : H D)) :=
    LinearIndependent.of_comp (H D).subtype hli
  have := hli'.finite_of_isNoetherian
  exact not_finite ℕ

/-! ### The spectral package from compactness -/

/-- **Dirichlet spectral package from the compact embedding.**  If the embedding
`H_D ↪ L²(D)` is compact, then the spectral package holds: a complete `L²`-orthonormal sequence
of eigenfunctions whose eigenvalues are the min–max values, positive, nondecreasing and tending to
`+∞`, with the spectral expansions of `q_D` and of the `L²` norm. -/
theorem spectral_of_compact (hN : 2 ≤ N) {D : Set (RN N)} (hD : IsAdmissible D)
    (hcomp : ∀ v : ℕ → Amb N, (∀ n, v n ∈ H D) → (∃ C, ∀ n, ‖v n‖ ≤ C) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : L2 N, Tendsto (fun n => (v (φ n)).1) atTop (𝓝 f)) :
    ∃ e : ℕ → Amb N,
      (∀ j, IsEigenfunction D (e j) (eigenvalue D (j + 1))) ∧
      (∀ i j, l2 (e i) (e j) = if i = j then 1 else 0) ∧
      0 < eigenvalue D 1 ∧
      Monotone (fun j => eigenvalue D (j + 1)) ∧
      Tendsto (fun j => eigenvalue D (j + 1)) atTop atTop ∧
      ∀ v ∈ H D, HasSum (fun j => eigenvalue D (j + 1) * l2 v (e j) ^ 2) (qf v v) ∧
        HasSum (fun j => l2 v (e j) ^ 2) (l2 v v) := by
  have hN1 : 1 ≤ N := by omega
  have hX : SpecHyp (H D) :=
    ⟨Submodule.isClosed_topologicalClosure _, fun v hv h => eq_zero_of_l2_self_eq_zero hv h,
      poincare_H hN1 hD.2.2, hcomp, H_not_finiteDimensional hN1 hD.1 hD.2.1⟩
  exact spectral_abstract hX

end FourthRatio

end
