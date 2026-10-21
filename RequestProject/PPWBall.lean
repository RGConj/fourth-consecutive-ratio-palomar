module

public import RequestProject.PPWDeep

/-!
# PPW equality case: a domain inside a ball with the same first eigenvalue

If a domain `D` lies in a ball `B` and `λ₁(D) = λ₁(B)`, then `H₀¹(D) = H₀¹(B)`: the first
eigenfunction of `D` is a first eigenfunction of `B`, so the ball's positive first
eigenfunction `Φ` lies in `H₀¹(D)`, and every test function `ψ` of `B` is `(ψ/Φ) Φ` with
`ψ/Φ` smooth and compactly supported.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

variable {N : ℕ}

/-- **Form domains coincide.** -/
theorem H_eq_ball_of_subset (hN : 2 ≤ N) {D : Set (RN N)} (hD : IsDomain D) {c : RN N}
    (hsub : D ⊆ ball c (annR N (eigenvalue D 1))) :
    H D = H (ball c (annR N (eigenvalue D 1))) := by
  set a := eigenvalue D 1 with ha_def
  have ha : 0 < a := by
    obtain ⟨e, -, -, h, -⟩ := ext_spectral hN hD.1
    exact h
  set B := ball c (annR N a) with hB_def
  have hR : 0 < annR N a := div_pos (besselZero_props (hN_nu hN)).1 (Real.sqrt_pos.mpr ha)
  refine le_antisymm (H_mono hsub) ?_
  obtain ⟨u, f, hu, hf, hfpos⟩ := ground_state_pos hN hD
  have hB1 : eigenvalue B 1 = a := (ball_first_eigen hN ha c).1
  obtain ⟨φ, hφH, hφ1, hφ2⟩ := exists_ball_phi hN ha c
  set E : RN N → ℝ := fun x => 1 * besselEntire N a (x - c) with hE_def
  have hEs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) E := contDiff_besselEntire_shift hN ha.le 1 c
  have hEpos : ∀ x ∈ B, 0 < E x := fun x hx => by
    simp only [E, one_mul]
    apply besselEntire_pos hN ha
    change dist x c < annR N a at hx
    simpa only [annR, dist_eq_norm] using hx
  -- `u` is a first eigenfunction of `B`
  have huB : IsEigenfunction B u (eigenvalue B 1) := by
    have huH : u ∈ H B := H_mono hsub hu.1
    refine ⟨huH, hu.2.1, ?_⟩
    have hq : qf u u = eigenvalue B 1 * l2 u u := by rw [hB1]; exact hu.2.2 u hu.1
    exact eigen_of_rayleigh_eq huH hq
  -- so is `φ`
  have hφB : IsEigenfunction B φ (eigenvalue B 1) := by
    rw [hB1]
    exact ⟨hφH, ne_zero_of_indicator_pos isOpen_ball (nonempty_ball.mpr hR) hEpos hφ1,
      weak_eigen_of_laplacian hEs (laplacian_besselEntire_shift hN ha.le 1 c) hφ1 hφ2⟩
  obtain ⟨k, hk⟩ := (ground_state hN (isDomain_ball c hR)).1 u φ huB hφB
  have hφD : φ ∈ H D := hk ▸ (H D).smul_mem k hu.1
  -- every test function of `B` lies in `H_D`
  have key : testGraph B ⊆ H D := by
    rintro p ⟨ψ, hψ, hψc, hψB, hp1, hp2⟩
    set χ : RN N → ℝ := fun x => ψ x * (E x)⁻¹ with hχ_def
    have hχs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ := by
      rw [contDiff_iff_contDiffAt]; intro x
      by_cases hx : x ∈ B
      · exact hψ.contDiffAt.mul (hEs.contDiffAt.inv (hEpos x hx).ne')
      · have hx' : x ∉ tsupport ψ := fun h => hx (hψB h)
        have h0 : χ =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
          filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx'] with y hy
          simp [χ, hy]
        exact contDiffAt_const.congr_of_eventuallyEq h0
    have hχc : HasCompactSupport χ := hψc.mul_right
    obtain ⟨hg, C, -, hC⟩ := exists_bound_cutoff hχs hχc
    have hM := Mpair_mem_H_self hχs.continuous hg hC hχs hφD
    have hpM : p = Mpair hχs.continuous hg hC φ := by
      have hχd : ∀ x, DifferentiableAt ℝ χ x := fun x => (hχs.differentiable (by simp)) x
      have hEd : ∀ x, DifferentiableAt ℝ E x := fun x => (hEs.differentiable (by simp)) x
      refine Prod.ext (Lp.ext ?_) (Lp.ext ?_)
      · filter_upwards [hp1, Mpair_fst_ae hχs.continuous hg hC φ, hφ1] with x h1 h2 h3
        rw [h1, h2, h3]
        by_cases hx : x ∈ B
        · rw [indicator_of_mem hx]
          have := (hEpos x hx).ne'
          simp only [χ]; field_simp
        · rw [indicator_of_notMem hx, mul_zero]
          exact image_eq_zero_of_notMem_tsupport (fun h => hx (hψB h))
      · filter_upwards [hp2, Mpair_snd_ae hχs.continuous hg hC φ, hφ1, hφ2]
          with x h1 h2 h3 h4
        rw [h1, h2, h3, h4]
        by_cases hx : x ∈ B
        · rw [indicator_of_mem hx, indicator_of_mem hx]
          have hloc : ψ =ᶠ[𝓝 x] fun y => χ y * E y := by
            filter_upwards [isOpen_ball.mem_nhds hx] with y hy
            have := (hEpos y hy).ne'
            simp only [χ]; field_simp
          rw [hloc.gradient_eq, gradient, gradient, gradient, fderiv_fun_mul (hχd x) (hEd x),
            map_add, map_smul, map_smul]
        · have hx' : x ∉ tsupport ψ := fun h => hx (hψB h)
          rw [indicator_of_notMem hx, indicator_of_notMem hx, smul_zero, zero_smul, add_zero]
          simp [gradient, fderiv_of_notMem_tsupport (𝕜 := ℝ) hx']
    exact hpM.symm ▸ hM
  show (Submodule.span ℝ (testGraph B)).topologicalClosure ≤ H D
  exact Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr key)
    (Submodule.isClosed_topologicalClosure _)

/-- A domain on which a first eigenfunction vanishes outside a closed ball lies in the open
ball. -/
theorem subset_ball_of_ae_zero (hN : 2 ≤ N) {D : Set (RN N)} (hD : IsDomain D) {u : Amb N}
    (hu : IsEigenfunction D u (eigenvalue D 1)) {c : RN N} {R : ℝ}
    (h0 : ∀ᵐ x, R < ‖x - c‖ → (u.1 : RN N → ℝ) x ^ 2 = 0) : D ⊆ ball c R := by
  haveI : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
  obtain ⟨hsimp, p0, g, hp0, hg, hgpos⟩ := ground_state hN hD
  obtain ⟨k, hk⟩ := hsimp p0 u hp0 hu
  have hk0 : k ≠ 0 := by
    rintro rfl; exact hu.2.1 (by rw [hk, zero_smul])
  set U := D ∩ {x | R < ‖x - c‖} with hU
  have hUo : IsOpen U :=
    hD.1.1.inter (isOpen_lt continuous_const (continuous_id.sub continuous_const).norm)
  have hU0 : volume U = 0 := by
    have hcoe : (u.1 : RN N → ℝ) =ᵐ[volume] fun x => k * (p0.1 : RN N → ℝ) x := by
      rw [hk]; exact Lp.coeFn_smul k p0.1
    have hae : ∀ᵐ x ∂volume.restrict D, x ∉ {x | R < ‖x - c‖} := by
      filter_upwards [ae_restrict_of_ae h0, ae_restrict_of_ae hcoe, hg.2,
        ae_restrict_mem hD.1.1.measurableSet] with x h1 h2 h3 hxD hxR
      have := h1 hxR
      rw [h2, h3] at this
      have hgx := hgpos x hxD
      have : k * g x ≠ 0 := mul_ne_zero hk0 hgx.ne'
      simp_all
    have := (ae_restrict_iff' hD.1.1.measurableSet).mp hae
    rw [ae_iff] at this
    refine measure_mono_null (fun x hx => ?_) this
    simp only [mem_setOf_eq]
    exact fun h => h hx.1 hx.2
  have hUe : U = ∅ := (hUo.measure_eq_zero_iff volume).mp hU0
  have hsub : D ⊆ closedBall c R := by
    intro x hxD
    by_contra hx
    have hxU : x ∈ U := ⟨hxD, by simpa [mem_closedBall, dist_eq_norm] using hx⟩
    rw [hUe] at hxU; exact hxU
  have := interior_maximal hsub hD.1.1
  rwa [interior_closedBall'] at this

end FourthRatio

end
