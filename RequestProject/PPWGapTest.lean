module

public import RequestProject.PPWDeep

/-!
# PPW: the gap inequality for a single multiplier

For a first eigenfunction `u` of a domain `D` and a smooth function `P`,
`(λ₂ - λ₁) (∫ P² u² ∫ u² - (∫ P u²)²) ≤ ∫ |∇P|² u² ∫ u²`.
This is the min–max bound `λ₂ ‖v‖² ≤ q(v)` applied to `v = P u - t u ⊥ u`, together with the
identity `q(P u) = ∫ |∇P|² u² + λ₁ ∫ P² u²` (test the eigenvalue equation with `P² u`).
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

variable {N : ℕ}

/-- `λ₂ ‖v‖² ≤ q(v)` for `v ∈ H_D` orthogonal to a first eigenfunction of the domain `D`. -/
theorem lam2_mul_le_of_orth (hN : 2 ≤ N) {D : Set (RN N)} (hD : IsDomain D) {u : Amb N}
    (hu : IsEigenfunction D u (eigenvalue D 1)) {v : Amb N} (hv : v ∈ H D)
    (horth : l2 v u = 0) : eigenvalue D 2 * l2 v v ≤ qf v v := by
  obtain ⟨e, he, -, -, hmono, -, hexp⟩ := ext_spectral hN hD.1
  obtain ⟨k, hk⟩ := (ground_state hN hD).1 u (e 0) hu (he 0)
  have h0 : l2 v (e 0) = 0 := by rw [hk, l2_smul_right, horth, mul_zero]
  obtain ⟨hq, hl⟩ := hexp v hv
  refine hasSum_le (fun j => ?_) (hl.mul_left (eigenvalue D 2)) hq
  rcases j with _ | j
  · simp [h0]
  · have : eigenvalue D (1 + 1) ≤ eigenvalue D (j + 1 + 1) := hmono (by omega : 1 ≤ j + 1)
    exact mul_le_mul_of_nonneg_right this (sq_nonneg _)

/-- **Gap inequality for one smooth multiplier.** -/
theorem gap_test (hN : 2 ≤ N) {D : Set (RN N)} (hD : IsDomain D) {u : Amb N}
    (hu : IsEigenfunction D u (eigenvalue D 1)) {P : RN N → ℝ}
    (hP : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) P) :
    (eigenvalue D 2 - eigenvalue D 1) *
        ((∫ x, P x ^ 2 * (u.1 : RN N → ℝ) x ^ 2) * (∫ x, (u.1 : RN N → ℝ) x ^ 2) -
          (∫ x, P x * (u.1 : RN N → ℝ) x ^ 2) ^ 2) ≤
      (∫ x, ‖gradient P x‖ ^ 2 * (u.1 : RN N → ℝ) x ^ 2) * ∫ x, (u.1 : RN N → ℝ) x ^ 2 := by
  set lam := eigenvalue D 1 with hlam
  -- a cut-off equal to `1` near `D̄`
  obtain ⟨χ0, hχs, hχc, -, U, hU, hDU, hU1⟩ :=
    exists_cutoff hD.1.2.2.isCompact_closure isOpen_univ (subset_univ _)
  set Q : RN N → ℝ := fun x => χ0 x * P x with hQ_def
  have hQs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Q := hχs.mul hP
  have hQc : HasCompactSupport Q := hχc.mul_right
  have hQd : ∀ x, DifferentiableAt ℝ Q x := fun x => (hQs.differentiable (by simp)) x
  have hQP : ∀ x ∈ D, Q x = P x := fun x hx => by
    simp [Q, hU1 x (hDU (subset_closure hx))]
  have hgQP : ∀ x ∈ D, gradient Q x = gradient P x := fun x hx => by
    have : Q =ᶠ[𝓝 x] P := by
      filter_upwards [hU.mem_nhds (hDU (subset_closure hx))] with y hy
      simp [Q, hU1 y hy]
    exact this.gradient_eq
  set Q2 : RN N → ℝ := fun x => Q x * Q x with hQ2_def
  have hQ2s : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Q2 := hQs.mul hQs
  have hQ2c : HasCompactSupport Q2 := hQc.mul_right
  have hgQ2 : ∀ x, gradient Q2 x = Q x • gradient Q x + Q x • gradient Q x := fun x => by
    rw [gradient, gradient, fderiv_fun_mul (hQd x) (hQd x), map_add, map_smul]
  obtain ⟨hgQ, C, -, hC⟩ := exists_bound_cutoff hQs hQc
  obtain ⟨hgQ2c, C2, -, hC2⟩ := exists_bound_cutoff hQ2s hQ2c
  set w := Mpair hQs.continuous hgQ hC u with hw_def
  set φ := Mpair hQ2s.continuous hgQ2c hC2 u with hφ_def
  have hw : w ∈ H D := Mpair_mem_H_self _ _ _ hQs hu.1
  have hφ : φ ∈ H D := Mpair_mem_H_self _ _ _ hQ2s hu.1
  have hw1 := Mpair_fst_ae hQs.continuous hgQ hC u
  have hw2 := Mpair_snd_ae hQs.continuous hgQ hC u
  have hφ1 := Mpair_fst_ae hQ2s.continuous hgQ2c hC2 u
  have hφ2 := Mpair_snd_ae hQ2s.continuous hgQ2c hC2 u
  -- `u` vanishes outside `D`
  have hvan : ∀ᵐ x, x ∉ D → (u.1 : RN N → ℝ) x = 0 ∧ (u.2 : RN N → RN N) x = 0 := by
    obtain ⟨h1, h2⟩ := mem_vanishOn.mp (H_le_vanishOn D hu.1)
    rw [Filter.EventuallyEq, ae_restrict_iff' hD.1.1.measurableSet.compl] at h1 h2
    filter_upwards [h1, h2] with x a b hx using ⟨a hx, b hx⟩
  -- the integrals
  have hA : l2 u u = ∫ x, (u.1 : RN N → ℝ) x ^ 2 := by
    rw [l2, L2.inner_def]; congr 1; funext x; simp
  have hb : l2 w u = ∫ x, P x * (u.1 : RN N → ℝ) x ^ 2 := by
    rw [l2, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hw1, hvan] with x h1 h2
    simp only [RCLike.inner_apply, conj_trivial]
    rw [h1]
    by_cases hx : x ∈ D
    · rw [hQP x hx]; ring
    · rw [show (u.1 : RN N → ℝ) x = 0 from (h2 hx).1]; ring
  have hc : l2 w w = ∫ x, P x ^ 2 * (u.1 : RN N → ℝ) x ^ 2 := by
    rw [l2, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hw1, hvan] with x h1 h2
    simp only [RCLike.inner_apply, conj_trivial]
    rw [h1]
    by_cases hx : x ∈ D
    · rw [hQP x hx]; ring
    · rw [show (u.1 : RN N → ℝ) x = 0 from (h2 hx).1]; ring
  have hc' : l2 u φ = ∫ x, P x ^ 2 * (u.1 : RN N → ℝ) x ^ 2 := by
    rw [l2, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hφ1, hvan] with x h1 h2
    simp only [RCLike.inner_apply, conj_trivial]
    rw [h1]
    by_cases hx : x ∈ D
    · simp only [Q2]; rw [hQP x hx]; ring
    · rw [show (u.1 : RN N → ℝ) x = 0 from (h2 hx).1]; ring
  have hint1 : Integrable fun x => ⟪(u.2 : RN N → RN N) x, (φ.2 : RN N → RN N) x⟫ := L2.integrable_inner u.2 φ.2
  have hint2 : Integrable fun x => ‖gradient Q x‖ ^ 2 * (u.1 : RN N → ℝ) x ^ 2 := by
    refine ((Lp.memLp u.1).integrable_sq).bdd_mul (c := C ^ 2)
      (hgQ.norm.pow 2).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hC x).2 2
  have hqww : qf w w = qf u φ + ∫ x, ‖gradient P x‖ ^ 2 * (u.1 : RN N → ℝ) x ^ 2 := by
    have e1 : qf w w = ∫ x, (⟪(u.2 : RN N → RN N) x, (φ.2 : RN N → RN N) x⟫ + ‖gradient Q x‖ ^ 2 * (u.1 : RN N → ℝ) x ^ 2) := by
      rw [qf, L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hw2, hφ2] with x h1 h2
      rw [h1, h2, hgQ2]
      simp only [Q2, inner_add_right, inner_smul_right, inner_add_left,
        inner_smul_left, conj_trivial, real_inner_self_eq_norm_sq]
      rw [real_inner_comm (gradient Q x) ((u.2 : RN N → RN N) x)]
      ring
    have e2 : (∫ x, ‖gradient Q x‖ ^ 2 * (u.1 : RN N → ℝ) x ^ 2) = ∫ x, ‖gradient P x‖ ^ 2 * (u.1 : RN N → ℝ) x ^ 2 := by
      refine integral_congr_ae ?_
      filter_upwards [hvan] with x h2
      by_cases hx : x ∈ D
      · rw [hgQP x hx]
      · rw [show (u.1 : RN N → ℝ) x = 0 from (h2 hx).1]; ring
    rw [e1, integral_add hint1 hint2, e2, qf, L2.inner_def]
  have hqwu : qf w u = lam * l2 w u := by
    rw [qf_comm, hu.2.2 w hw, l2_comm]
  have hquu : qf u u = lam * l2 u u := hu.2.2 u hu.1
  have hqφ : qf u φ = lam * l2 u φ := hu.2.2 φ hφ
  -- the test vector
  set A := l2 u u
  set b := l2 w u
  set v := A • w - b • u with hv_def
  have hvH : v ∈ H D := (H D).sub_mem ((H D).smul_mem A hw) ((H D).smul_mem b hu.1)
  have hvorth : l2 v u = 0 := by
    simp only [v, l2_sub_left, l2_smul_left]; ring
  have key := lam2_mul_le_of_orth hN hD hu hvH hvorth
  have hl2v : l2 v v = A * (A * l2 w w - b ^ 2) := by
    simp only [v, l2_sub_left, l2_sub_right, l2_smul_left, l2_smul_right, l2_comm u w]; ring
  have hqv : qf v v = A * (A * qf w w - lam * b ^ 2) := by
    simp only [v, qf_sub_left, qf_sub_right, qf_smul_left, qf_smul_right, qf_comm u w, hqwu,
      hquu]; ring
  have hApos : 0 < A := l2_self_pos hu.1 hu.2.1
  rw [hl2v, hqv, hqww, hqφ, hc'] at key
  have key' : eigenvalue D 2 * (A * l2 w w - b ^ 2) ≤
      A * (lam * (∫ x, P x ^ 2 * (u.1 : RN N → ℝ) x ^ 2) + ∫ x, ‖gradient P x‖ ^ 2 * (u.1 : RN N → ℝ) x ^ 2) - lam * b ^ 2 := by
    have := le_of_mul_le_mul_left (by nlinarith [key] : A * (eigenvalue D 2 * (A * l2 w w - b ^ 2)) ≤
      A * (A * (lam * (∫ x, P x ^ 2 * (u.1 : RN N → ℝ) x ^ 2) + ∫ x, ‖gradient P x‖ ^ 2 * (u.1 : RN N → ℝ) x ^ 2) - lam * b ^ 2)) hApos
    exact this
  rw [hc, hb, hA] at key'
  rw [← hA, ← hb] at *
  rw [hA, hb] at key'
  nlinarith [key']

end FourthRatio

end
