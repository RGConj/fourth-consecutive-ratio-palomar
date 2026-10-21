module

public import RequestProject.SobolevLocal
public import RequestProject.TestPair

/-!
# Test functions and integration by parts

* the pair `(φ, ∇φ)` of a test function `φ ∈ C_c^∞(ℝ^N)`;
* integration by parts `∫ ⟨∇Ψ, ∇φ⟩ = -∫ ΔΨ φ` for smooth `Ψ` and a test function `φ`;
* the defining identity of the weak gradient: `⟨g, ∇φ⟩_{L²} = -⟨v, Δφ⟩_{L²}` for every
  `(v, g) ∈ H_D` and every test function `φ`.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Function Set
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

variable {N : ℕ}

/-! ### Test pairs -/

/- The test pair `(φ, ∇φ)` (`testPair`, `testPair_mem`, `eq_testPair`) is defined in
`RequestProject/TestPair.lean`. -/

/-! ### Integration by parts -/

/-- `⟨∇Ψ, ∇φ⟩` in coordinates. -/
lemma inner_gradient_eq_sum (Ψ φ : RN N → ℝ) (x : RN N) :
    ⟪gradient Ψ x, gradient φ x⟫ =
      ∑ i, fderiv ℝ Ψ x (EuclideanSpace.basisFun (Fin N) ℝ i) *
        fderiv ℝ φ x (EuclideanSpace.basisFun (Fin N) ℝ i) := by
  rw [← (EuclideanSpace.basisFun (Fin N) ℝ).sum_inner_mul_inner (gradient Ψ x) (gradient φ x)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_comm (gradient φ x), gradient, gradient,
    InnerProductSpace.toDual_symm_apply, InnerProductSpace.toDual_symm_apply]

/-- The Laplacian in coordinates. -/
lemma laplacian_eq_sum {Ψ : RN N → ℝ} (hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ)
    (x : RN N) :
    Laplacian.laplacian Ψ x = ∑ i, fderiv ℝ (fun z => fderiv ℝ Ψ z
      (EuclideanSpace.basisFun (Fin N) ℝ i)) x (EuclideanSpace.basisFun (Fin N) ℝ i) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _
    (EuclideanSpace.basisFun (Fin N) ℝ)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedFDeriv_two_apply]
  have hd : DifferentiableAt ℝ (fderiv ℝ Ψ) x :=
    ((hΨ.fderiv_right (m := 1) (WithTop.coe_le_coe.mpr le_top)).differentiable (by simp)) x
  rw [fderiv_clm_apply hd (differentiableAt_const _)]
  simp

/-- **Integration by parts** `∫ ⟨∇Ψ, ∇φ⟩ = -∫ ΔΨ φ` for smooth `Ψ` and a test function `φ`. -/
lemma integral_inner_gradient_eq_neg_laplacian {Ψ φ : RN N → ℝ}
    (hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ) (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hφc : HasCompactSupport φ) :
    ∫ x, ⟪gradient Ψ x, gradient φ x⟫ = - ∫ x, Laplacian.laplacian Ψ x * φ x := by
  set b := EuclideanSpace.basisFun (Fin N) ℝ
  simp_rw [inner_gradient_eq_sum, laplacian_eq_sum hΨ, Finset.sum_mul]
  have hΨ1 : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => fderiv ℝ Ψ z (b i)) := fun i =>
    (hΨ.fderiv_right (m := (⊤ : ℕ∞)) (WithTop.coe_le_coe.mpr le_top)).clm_apply contDiff_const
  have hc1 : ∀ i, Continuous (fun x => fderiv ℝ Ψ x (b i) * fderiv ℝ φ x (b i)) := fun i =>
    (hΨ1 i).continuous.mul ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hc2 : ∀ i, Continuous (fun x => fderiv ℝ (fun z => fderiv ℝ Ψ z (b i)) x (b i) * φ x) :=
    fun i => (((hΨ1 i).continuous_fderiv (by simp)).clm_apply continuous_const).mul hφ.continuous
  rw [integral_finsetSum _ (fun i _ => (hc1 i).integrable_of_hasCompactSupport
      (hφc.fderiv_apply (𝕜 := ℝ) (b i)).mul_left),
    integral_finsetSum _ (fun i _ => (hc2 i).integrable_of_hasCompactSupport hφc.mul_left),
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    ((hc2 i).integrable_of_hasCompactSupport hφc.mul_left)
    ((hc1 i).integrable_of_hasCompactSupport (hφc.fderiv_apply (𝕜 := ℝ) (b i)).mul_left)
    (((hΨ1 i).continuous.mul hφ.continuous).integrable_of_hasCompactSupport hφc.mul_left)
    (fun x _ => (hΨ1 i).differentiable (by simp) x)
    (fun x _ => hφ.differentiable (by simp) x)

lemma gradient_eq_zero_of_notMem_tsupport {φ : RN N → ℝ} {x : RN N} (hx : x ∉ tsupport φ) :
    gradient φ x = 0 := by
  have : fderiv ℝ φ x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hx (tsupport_fderiv_subset ℝ h))
  simp [gradient, this]


/-! ### The Laplacian of a test function -/

lemma contDiff_laplacian {ψ : RN N → ℝ} (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Laplacian.laplacian ψ) := by
  have : Laplacian.laplacian ψ = fun x => ∑ i, fderiv ℝ (fun z => fderiv ℝ ψ z
      (EuclideanSpace.basisFun (Fin N) ℝ i)) x (EuclideanSpace.basisFun (Fin N) ℝ i) :=
    funext (laplacian_eq_sum hψ)
  rw [this]
  refine ContDiff.sum fun i _ => ?_
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => fderiv ℝ ψ z (EuclideanSpace.basisFun (Fin N) ℝ i)) :=
    (hψ.fderiv_right (m := (⊤ : ℕ∞)) (WithTop.coe_le_coe.mpr le_top)).clm_apply contDiff_const
  exact (h1.fderiv_right (m := (⊤ : ℕ∞)) (WithTop.coe_le_coe.mpr le_top)).clm_apply
    contDiff_const

lemma laplacian_eq_zero_of_notMem_tsupport {ψ : RN N → ℝ} {x : RN N} (hx : x ∉ tsupport ψ) :
    Laplacian.laplacian ψ x = 0 := by
  have h : ψ =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    have := (isClosed_tsupport ψ).isOpen_compl.mem_nhds hx
    filter_upwards [this] with z hz
    exact image_eq_zero_of_notMem_tsupport hz
  rw [(InnerProductSpace.laplacian_congr_nhds h).eq_of_nhds,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _
    (EuclideanSpace.basisFun (Fin N) ℝ)]
  simp

lemma hasCompactSupport_laplacian {ψ : RN N → ℝ} (hψc : HasCompactSupport ψ) :
    HasCompactSupport (Laplacian.laplacian ψ) :=
  hψc.mono' fun _ hx => by
    by_contra h
    exact hx (laplacian_eq_zero_of_notMem_tsupport h)

/-- Symmetric integration by parts `∫ ΔΨ φ = ∫ Ψ Δφ` for two test functions. -/
lemma integral_laplacian_mul_comm {Ψ φ : RN N → ℝ}
    (hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ) (hΨc : HasCompactSupport Ψ)
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (hφc : HasCompactSupport φ) :
    ∫ x, Laplacian.laplacian Ψ x * φ x = ∫ x, Ψ x * Laplacian.laplacian φ x := by
  have h1 := integral_inner_gradient_eq_neg_laplacian hΨ hφ hφc
  have h2 := integral_inner_gradient_eq_neg_laplacian hφ hΨ hΨc
  have h3 : ∫ x, ⟪gradient Ψ x, gradient φ x⟫ = ∫ x, ⟪gradient φ x, gradient Ψ x⟫ := by
    simp_rw [real_inner_comm (gradient Ψ _)]
  have : ∫ x, Laplacian.laplacian φ x * Ψ x = ∫ x, Ψ x * Laplacian.laplacian φ x := by
    simp_rw [mul_comm]
  linarith

/-- `Δφ` as an element of `L²` for a test function `φ`. -/
def lapL2 (φ : RN N → ℝ) (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hc : HasCompactSupport φ) : L2 N :=
  MemLp.toLp _ ((contDiff_laplacian hφ).continuous.memLp_of_hasCompactSupport
    (hasCompactSupport_laplacian hc))

lemma lapL2_ae (φ : RN N → ℝ) (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hc : HasCompactSupport φ) :
    (lapL2 φ hφ hc : RN N → ℝ) =ᵐ[volume] Laplacian.laplacian φ :=
  MemLp.coeFn_toLp _

/-- **Weak gradient identity.** For `(v, g) ∈ H_D` and a test function `φ`:
`⟨g, ∇φ⟩ = -⟨v, Δφ⟩` in `L²`. -/
lemma weak_gradient_identity {D : Set (RN N)} {p : Amb N} (hp : p ∈ H D) (φ : RN N → ℝ)
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (hc : HasCompactSupport φ) :
    ⟪p.2, (testPair φ hφ hc).2⟫ = -⟪p.1, lapL2 φ hφ hc⟫ := by
  set L : Amb N →L[ℝ] ℝ := (innerSL ℝ (testPair φ hφ hc).2).comp
    (ContinuousLinearMap.snd ℝ _ _) + (innerSL ℝ (lapL2 φ hφ hc)).comp
    (ContinuousLinearMap.fst ℝ _ _) with hL
  have hLapp : ∀ q : Amb N, L q = ⟪q.2, (testPair φ hφ hc).2⟫ + ⟪q.1, lapL2 φ hφ hc⟫ := by
    intro q; simp [hL, real_inner_comm]
  have hle : H D ≤ LinearMap.ker L.toLinearMap := by
    refine Submodule.topologicalClosure_minimal _ ?_ (ContinuousLinearMap.isClosed_ker _)
    rw [Submodule.span_le]
    intro q hq
    obtain ⟨ψ, hψ, hψc, -, rfl⟩ := eq_testPair hq
    change L _ = 0
    rw [hLapp]
    have e1 : ⟪(testPair ψ hψ hψc).2, (testPair φ hφ hc).2⟫ =
        ∫ x, ⟪gradient ψ x, gradient φ x⟫ := by
      rw [MeasureTheory.L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [MemLp.coeFn_toLp (memLp_gradient_of_testFun hψ hψc),
        MemLp.coeFn_toLp (memLp_gradient_of_testFun hφ hc)] with x h1 h2
      simp only [testPair] at *
      rw [h1, h2]
    have e2 : ⟪(testPair ψ hψ hψc).1, lapL2 φ hφ hc⟫ =
        ∫ x, ψ x * Laplacian.laplacian φ x := by
      rw [MeasureTheory.L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [MemLp.coeFn_toLp (memLp_of_testFun hψ hψc), lapL2_ae φ hφ hc] with x h1 h2
      simp only [testPair] at *
      rw [h1, h2]
      simp [mul_comm]
    rw [e1, e2, integral_inner_gradient_eq_neg_laplacian hψ hφ hc,
      integral_laplacian_mul_comm hψ hψc hφ hc]
    ring
  have := hle hp
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hLapp] at this
  linarith

end FourthRatio

end
