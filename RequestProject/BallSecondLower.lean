module

public import RequestProject.BallRadialCore

/-!
# The lower half of the second-eigenvalue statement for the ball

With `ν = N/2 - 1`, `a > 0` and `R = j_{ν,1}/√a`, for every ball `B = B_R(y)`:
`λ₂(B) ≥ C_N a`, and every space of weak eigenfunctions of `B` with eigenvalue `C_N a` is finite
dimensional of dimension at most `N`.

This was previously an assumed external statement; it is now proved:

* an eigenfunction with eigenvalue `μ < C_N a` is symmetric under every reflection through `y`
  (`eigen_sym_of_lt`), hence radial, hence (`radial_classify`) `μ = a`; two orthonormal
  eigenfunctions for `λ₁(B) = a` would contradict simplicity of `λ₁`;
* an eigenfunction with eigenvalue `C_N a` that is `L²`-orthogonal to all degree-one
  eigenfunctions `Ψ_c` is symmetric under every reflection (`eigen_sym_of_orth`), hence radial,
  hence zero (`radial_classify`, since `C_N > 1`); so `u ↦ (c ↦ ⟨u, Ψ_c⟩)` embeds the eigenspace
  into the dual of `ℝ^N`.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Function Set
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

variable {N : ℕ}

/-- **Reflection-symmetric eigenfunctions of the ball**: their eigenvalue is `a` or exceeds
`C_N a`. -/
theorem radial_classify (hN : 2 ≤ N) {a : ℝ} (ha : 0 < a) (y : RN N) {u : Amb N} {μ : ℝ}
    (hu : u ∈ H (ball y (annR N a))) (hu0 : u ≠ 0)
    (hw : ∀ φ ∈ H (ball y (annR N a)), qf u φ = μ * l2 u φ)
    (hsym : ∀ c : RN N, c ≠ 0 → opC y c u = u) : μ = a ∨ CN N * a < μ := by
  set B := ball y (annR N a) with hBdef
  have hR := annR_pos hN ha
  have hBm : MeasurableSet B := isOpen_ball.measurableSet
  have hD := isDomain_ball y hR
  obtain ⟨f, hfa, hf⟩ := ext_analytic hD hu hw
  have hΔ := laplacian_eq_of_weak isOpen_ball hu hw hfa hf
  have hrad := radial_of_sym y hf hsym
  have hB1 := (ball_first_eigen hN ha y).1
  have hμa : a ≤ μ := by
    have h1 := qf_ge_lam1 hu
    rw [hB1, hw u hu] at h1
    have hp := l2_self_pos hu hu0
    nlinarith
  have hμ : 0 < μ := ha.trans_le hμa
  have hfB : ∀ᵐ x, x ∈ B → (u.1 : RN N → ℝ) x = f x := (ae_restrict_iff' hBm).mp hf.2
  obtain ⟨hu1, -⟩ := vanish_off_of_mem_H isOpen_ball hu
  have hwneg : ∀ φ ∈ H B, qf (-u) φ = μ * l2 (-u) φ := fun φ hφ => by
    rw [qf_neg_left, l2_neg_left, hw φ hφ]; ring
  by_cases hnn : ∀ x ∈ B, 0 ≤ f x
  · left
    have hnn' : 0 ≤ᵐ[volume] (u.1 : RN N → ℝ) := by
      filter_upwards [hfB, hu1] with x e1 e2
      by_cases hx : x ∈ B
      · rw [Pi.zero_apply, e1 hx]; exact hnn x hx
      · rw [Pi.zero_apply, e2 hx]
    have := eigenvalue_one_eq_of_nonneg hN hD ⟨hu, hu0, hw⟩ hnn'
    rw [hB1] at this; exact this.symm
  by_cases hnp : ∀ x ∈ B, f x ≤ 0
  · left
    have hnn' : 0 ≤ᵐ[volume] ((-u).1 : RN N → ℝ) := by
      filter_upwards [hfB, hu1, Lp.coeFn_neg u.1] with x e1 e2 e3
      rw [Prod.fst_neg, e3, Pi.zero_apply, Pi.neg_apply, neg_nonneg]
      by_cases hx : x ∈ B
      · rw [e1 hx]; exact hnp x hx
      · rw [e2 hx]
    have := eigenvalue_one_eq_of_nonneg hN hD ⟨(H B).neg_mem hu, neg_ne_zero.mpr hu0, hwneg⟩ hnn'
    rw [hB1] at this; exact this.symm
  push_neg at hnn hnp
  obtain ⟨xm, hxm, hfxm⟩ := hnn
  obtain ⟨xp, hxp, hfxp⟩ := hnp
  right
  have hy0 := center_ne_zero hN hR y hμ.le hfa hΔ hrad ⟨xp, hxp, hfxp.ne'⟩
  rcases lt_or_gt_of_ne hy0 with hneg | hpos
  · have hfneg : IsContRep B (-u) (-f) := by
      refine ⟨hf.1.neg, ?_⟩
      rw [EventuallyEq, ae_restrict_iff' hBm]
      filter_upwards [Lp.coeFn_neg u.1, hfB] with x e1 e2 hx
      rw [Prod.fst_neg, e1, Pi.neg_apply, e2 hx, Pi.neg_apply]
    have hrad' : ∀ x ∈ B, ∀ x' ∈ B, ‖x - y‖ = ‖x' - y‖ → (-f) x = (-f) x' :=
      fun x hx x' hx' h => by simp only [Pi.neg_apply, hrad x hx x' hx' h]
    exact radial_core hN ha y hμ ((H B).neg_mem hu) hwneg hfneg hrad'
      (by simp only [Pi.neg_apply, neg_pos]; exact hneg) hxp
      (by simp only [Pi.neg_apply, neg_lt_zero]; exact hfxp)
  · exact radial_core hN ha y hμ hu hw hf hrad hpos hxm hfxm

/-- The degree-one eigenfunctions as a linear map `c ↦ Ψ_c ∈ H₀¹(B)`. -/
lemma exists_deg1_linear (hN : 2 ≤ N) {a : ℝ} (ha : 0 < a) (y : RN N) :
    ∃ L : RN N →ₗ[ℝ] Amb N, ∀ c, L c ∈ H (ball y (annR N a)) ∧
      ((L c).1 : RN N → ℝ) =ᵐ[volume] (ball y (annR N a)).indicator (deg1Fun N a y c) := by
  choose w hwH hw1 hw2 hweq using exists_deg1' hN ha y
  set B := ball y (annR N a)
  have hadd : ∀ c d, w (c + d) = w c + w d := fun c d => by
    refine eq_of_fst_eq (hwH _) ((H B).add_mem (hwH c) (hwH d)) (Lp.ext ?_)
    filter_upwards [hw1 (c + d), hw1 c, hw1 d, Lp.coeFn_add (w c).1 (w d).1] with x e1 e2 e3 e4
    simp only [Prod.fst_add] at e4 ⊢
    rw [e1, e4, Pi.add_apply, e2, e3]
    by_cases hx : x ∈ B
    · simp only [indicator_of_mem hx, deg1Fun, inner_add_left]; ring
    · simp [indicator_of_notMem hx]
  have hsmul : ∀ (t : ℝ) c, w (t • c) = t • w c := fun t c => by
    refine eq_of_fst_eq (hwH _) ((H B).smul_mem t (hwH c)) (Lp.ext ?_)
    filter_upwards [hw1 (t • c), hw1 c, Lp.coeFn_smul t (w c).1] with x e1 e2 e3
    simp only [Prod.smul_fst] at e3 ⊢
    rw [e1, e3, Pi.smul_apply, e2, smul_eq_mul]
    by_cases hx : x ∈ B
    · simp only [indicator_of_mem hx, deg1Fun, inner_smul_left]; simp; ring
    · simp [indicator_of_notMem hx]
  exact ⟨{ toFun := w, map_add' := hadd, map_smul' := hsmul }, fun c => ⟨hwH c, hw1 c⟩⟩

/-- **The lower half of the ball's second-eigenvalue statement** (formerly an assumed external
statement): `λ₂(B) ≥ C_N a`, and every space of weak eigenfunctions of `B` with eigenvalue `C_N a`
is finite dimensional of dimension at most `N`. -/
theorem ball_second_lower (hN : 2 ≤ N) {a : ℝ} (ha : 0 < a) :
    let ν : ℝ := (N : ℝ) / 2 - 1
    let R := besselZero ν 1 / Real.sqrt a
    ∀ y : RN N,
      CN N * a ≤ eigenvalue (ball y R) 2 ∧
      ∀ V : Submodule ℝ (Amb N),
        (∀ u ∈ V, u ∈ H (ball y R) ∧ ∀ φ ∈ H (ball y R), qf u φ = CN N * a * l2 u φ) →
        FiniteDimensional ℝ V ∧ Module.finrank ℝ V ≤ N := by
  intro ν R y
  change CN N * a ≤ eigenvalue (ball y (annR N a)) 2 ∧ ∀ V : Submodule ℝ (Amb N),
    (∀ u ∈ V, u ∈ H (ball y (annR N a)) ∧
      ∀ φ ∈ H (ball y (annR N a)), qf u φ = CN N * a * l2 u φ) →
    FiniteDimensional ℝ V ∧ Module.finrank ℝ V ≤ N
  set B := ball y (annR N a) with hBdef
  have hR := annR_pos hN ha
  have hD := isDomain_ball y hR
  have hC := CN_gt_one hN
  constructor
  · by_contra hlt
    push_neg at hlt
    obtain ⟨e, he, horth, -⟩ := ext_spectral hN hD.1
    have he1 : IsEigenfunction B (e 1) (eigenvalue B 2) := he 1
    have he0 : IsEigenfunction B (e 0) (eigenvalue B 1) := he 0
    have hsym : ∀ c : RN N, c ≠ 0 → opC y c (e 1) = e 1 := fun c hc =>
      eigen_sym_of_lt hN ha y hc he1.1 he1.2.2 hlt
    rcases radial_classify hN ha y he1.1 he1.2.1 he1.2.2 hsym with h | h
    · have hB1 := (ball_first_eigen hN ha y).1
      have he1' : IsEigenfunction B (e 1) (eigenvalue B 1) := by rw [hB1, ← h]; exact he1
      obtain ⟨k, hk⟩ := (ground_state hN hD).1 (e 0) (e 1) he0 he1'
      have h01 : l2 (e 0) (e 1) = 0 := by simpa using horth 0 1
      have h11 : l2 (e 1) (e 1) = 1 := by simpa using horth 1 1
      have : l2 (e 1) (e 1) = k * l2 (e 0) (e 1) := by
        calc l2 (e 1) (e 1) = l2 (k • e 0) (e 1) := by rw [← hk]
          _ = k * l2 (e 0) (e 1) := l2_smul_left _ _ _
      rw [h01, mul_zero] at this
      rw [this] at h11
      exact zero_ne_one h11
    · linarith
  · intro V hV
    obtain ⟨L, hL⟩ := exists_deg1_linear hN ha y
    let Λ : V →ₗ[ℝ] Module.Dual ℝ (RN N) :=
      LinearMap.mk₂ ℝ (fun (u : V) (c : RN N) => l2 (u : Amb N) (L c))
        (fun u₁ u₂ c => by simp [l2_add_left])
        (fun t u c => by simp [l2_smul_left])
        (fun u c₁ c₂ => by simp [map_add, l2_add_right])
        (fun t u c => by simp [map_smul, l2_smul_right])
    have hinj : Function.Injective Λ := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro u hu
      have horth : ∀ c, l2 (u : Amb N) (L c) = 0 := fun c => by
        have := LinearMap.congr_fun hu c
        simpa [Λ] using this
      obtain ⟨huH, huw⟩ := hV u u.2
      have hsym : ∀ c : RN N, c ≠ 0 → opC y c (u : Amb N) = u := fun c hc =>
        eigen_sym_of_orth hN ha y hc huH huw (hL c).2 (horth c)
      by_contra hu0
      have hu0' : (u : Amb N) ≠ 0 := fun h => hu0 (Subtype.ext h)
      rcases radial_classify hN ha y huH hu0' huw hsym with h | h
      · have : CN N * a > 1 * a := mul_lt_mul_of_pos_right hC ha
        linarith
      · exact lt_irrefl _ h
    haveI : FiniteDimensional ℝ (Module.Dual ℝ (RN N)) := inferInstance
    refine ⟨Module.Finite.of_injective Λ hinj, ?_⟩
    calc Module.finrank ℝ V ≤ Module.finrank ℝ (Module.Dual ℝ (RN N)) :=
          LinearMap.finrank_le_finrank_of_injective hinj
      _ = N := by rw [Subspace.dual_finrank_eq, finrank_euclideanSpace_fin]

end FourthRatio

end
