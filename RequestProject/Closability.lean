module

public import RequestProject.Defs

/-!
# Closability of the gradient

If `(v, g) ∈ H_D` and `v = 0`, then `g = 0`.  Every element of `H_D` satisfies the integration by
parts identity `∫ θ ⟨g, e⟩ = -∫ ∂_e θ · v` against smooth compactly supported `θ` (it holds for
test pairs and passes to `H¹`-limits), so `v = 0` forces `∫ θ ⟨g, e⟩ = 0` for all `θ`, hence
`⟨g, e⟩ = 0` almost everywhere for every `e`.

This is proved directly, without the spectral package.
-/

@[expose] public section

open MeasureTheory Filter Topology Function
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

variable {N : ℕ}

/-- Smooth compactly supported test functions. -/
abbrev TestFn (N : ℕ) := {θ : RN N → ℝ // ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) θ ∧ HasCompactSupport θ}

lemma memLp_testFn_smul (θ : TestFn N) (e : RN N) :
    MemLp (fun x => θ.1 x • e) 2 (volume : Measure (RN N)) :=
  (θ.2.1.continuous.smul continuous_const).memLp_of_hasCompactSupport (θ.2.2.smul_right)

lemma memLp_testFn_deriv (θ : TestFn N) (e : RN N) :
    MemLp (fun x => fderiv ℝ θ.1 x e) 2 (volume : Measure (RN N)) := by
  have hc : Continuous (fun x => fderiv ℝ θ.1 x e) :=
    (θ.2.1.continuous_fderiv (by simp)).clm_apply continuous_const
  exact hc.memLp_of_hasCompactSupport (θ.2.2.fderiv_apply (𝕜 := ℝ) e)

/-- The continuous linear functional `p ↦ ⟨θ e, p.2⟩ + ⟨∂_e θ, p.1⟩`. -/
def ibpFunctional (θ : TestFn N) (e : RN N) : Amb N →L[ℝ] ℝ :=
  (innerSL ℝ ((memLp_testFn_smul θ e).toLp _ : L2v N)).comp (ContinuousLinearMap.snd ℝ _ _) +
  (innerSL ℝ ((memLp_testFn_deriv θ e).toLp _ : L2 N)).comp (ContinuousLinearMap.fst ℝ _ _)

lemma ibpFunctional_apply (θ : TestFn N) (e : RN N) (p : Amb N) :
    ibpFunctional θ e p = (∫ x, θ.1 x * ⟪e, (p.2 : RN N → RN N) x⟫) +
      ∫ x, fderiv ℝ θ.1 x e * (p.1 : RN N → ℝ) x := by
  have h1 : ∫ x, ⟪(((memLp_testFn_smul θ e).toLp _ : L2v N) : RN N → RN N) x,
      (p.2 : RN N → RN N) x⟫ = ∫ x, θ.1 x * ⟪e, (p.2 : RN N → RN N) x⟫ := by
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (memLp_testFn_smul θ e)] with x hx
    rw [hx, real_inner_smul_left]
  have h2 : ∫ x, ⟪(((memLp_testFn_deriv θ e).toLp _ : L2 N) : RN N → ℝ) x,
      (p.1 : RN N → ℝ) x⟫ = ∫ x, fderiv ℝ θ.1 x e * (p.1 : RN N → ℝ) x := by
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (memLp_testFn_deriv θ e)] with x hx
    rw [hx]
    simp [mul_comm]
  simp only [ibpFunctional, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_fst',
    MeasureTheory.L2.inner_def]
  exact congrArg₂ (· + ·) h1 h2

/-- Integration by parts for test pairs. -/
lemma ibpFunctional_testGraph {D : Set (RN N)} {p : Amb N} (hp : p ∈ testGraph D)
    (θ : TestFn N) (e : RN N) : ibpFunctional θ e p = 0 := by
  obtain ⟨φ, hφ, hφc, -, h4, h5⟩ := hp
  rw [ibpFunctional_apply]
  have e1 : ∫ x, θ.1 x * ⟪e, (p.2 : RN N → RN N) x⟫ = ∫ x, θ.1 x * fderiv ℝ φ x e := by
    refine integral_congr_ae ?_
    filter_upwards [h5] with x hx
    rw [hx, real_inner_comm, gradient, InnerProductSpace.toDual_symm_apply]
  have e2 : ∫ x, fderiv ℝ θ.1 x e * (p.1 : RN N → ℝ) x = ∫ x, fderiv ℝ θ.1 x e * φ x := by
    refine integral_congr_ae ?_
    filter_upwards [h4] with x hx
    rw [hx]
  have hθd : Continuous (fun x => fderiv ℝ θ.1 x e) :=
    (θ.2.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hφd : Continuous (fun x => fderiv ℝ φ x e) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    ((hθd.mul hφ.continuous).integrable_of_hasCompactSupport hφc.mul_left)
    ((θ.2.1.continuous.mul hφd).integrable_of_hasCompactSupport θ.2.2.mul_right)
    ((θ.2.1.continuous.mul hφ.continuous).integrable_of_hasCompactSupport θ.2.2.mul_right)
    (fun x _ => θ.2.1.differentiable (by simp) x)
    (fun x _ => hφ.differentiable (by simp) x)
  rw [e1, e2, key]
  ring

/-- Integration by parts holds on all of `H_D`. -/
lemma ibpFunctional_H {D : Set (RN N)} {p : Amb N} (hp : p ∈ H D) (θ : TestFn N) (e : RN N) :
    ibpFunctional θ e p = 0 := by
  have hle : H D ≤ LinearMap.ker (ibpFunctional θ e).toLinearMap := by
    refine Submodule.topologicalClosure_minimal _ ?_ (ContinuousLinearMap.isClosed_ker _)
    rw [Submodule.span_le]
    intro q hq
    exact ibpFunctional_testGraph hq θ e
  exact hle hp

/-- **Closability of the gradient.** An element of `H_D` whose function part vanishes is zero. -/
theorem snd_eq_zero_of_mem_H {D : Set (RN N)} {v : Amb N} (hv : v ∈ H D) (h1 : v.1 = 0) :
    v.2 = 0 := by
  have h1' : (v.1 : RN N → ℝ) =ᵐ[volume] 0 := by rw [h1]; exact Lp.coeFn_zero _ _ _
  have he : ∀ e : RN N, ∀ᵐ x ∂(volume : Measure (RN N)), ⟪e, (v.2 : RN N → RN N) x⟫ = 0 := by
    intro e
    have hli : LocallyIntegrable (fun x => ⟪e, (v.2 : RN N → RN N) x⟫) volume := by
      have hm : MemLp (fun x => ⟪e, (v.2 : RN N → RN N) x⟫) 2 volume :=
        (Lp.memLp v.2).const_inner e
      exact hm.locallyIntegrable (by norm_num)
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hli fun θ hθ hθc => ?_
    have h := ibpFunctional_H hv ⟨θ, hθ, hθc⟩ e
    rw [ibpFunctional_apply] at h
    have h0 : ∫ x, fderiv ℝ θ x e * (v.1 : RN N → ℝ) x = 0 := by
      rw [integral_congr_ae (g := fun _ => (0 : ℝ))]
      · simp
      · filter_upwards [h1'] with x hx
        simp [hx]
    simp only [h0, add_zero] at h
    simpa [smul_eq_mul] using h
  set b := EuclideanSpace.basisFun (Fin N) ℝ
  have hall : ∀ᵐ x ∂(volume : Measure (RN N)), ∀ i, ⟪b i, (v.2 : RN N → RN N) x⟫ = 0 :=
    ae_all_iff.mpr fun i => he (b i)
  rw [Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [hall] with x hx
  have : (v.2 : RN N → RN N) x = ∑ i, ⟪b i, (v.2 : RN N → RN N) x⟫ • b i :=
    (b.sum_repr' _).symm
  rw [this]
  simp [hx]

end FourthRatio

end
