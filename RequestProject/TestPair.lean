module

public import RequestProject.Basic

/-!
# Test pairs

The pair `(φ, ∇φ) ∈ L² × L²` of a test function `φ ∈ C_c^∞(ℝ^N)`, and the fact that the test
graph `{(φ, ∇φ) : φ ∈ C_c^∞(D)}` is a linear subspace (so that `H_D` is the closure of the test
graph itself).
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Function Set
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

variable {N : ℕ}

lemma continuous_gradient_of_contDiff {φ : RN N → ℝ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) : Continuous (gradient φ) :=
  (InnerProductSpace.toDual ℝ (RN N)).symm.continuous.comp (hφ.continuous_fderiv (by simp))

lemma hasCompactSupport_gradient {φ : RN N → ℝ} (hc : HasCompactSupport φ) :
    HasCompactSupport (gradient φ) :=
  (hc.fderiv (𝕜 := ℝ)).comp_left (g := (InnerProductSpace.toDual ℝ (RN N)).symm) (map_zero _)

lemma memLp_of_testFun {φ : RN N → ℝ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hc : HasCompactSupport φ) : MemLp φ 2 (volume : Measure (RN N)) :=
  hφ.continuous.memLp_of_hasCompactSupport hc

lemma memLp_gradient_of_testFun {φ : RN N → ℝ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hc : HasCompactSupport φ) : MemLp (gradient φ) 2 (volume : Measure (RN N)) :=
  (continuous_gradient_of_contDiff hφ).memLp_of_hasCompactSupport (hasCompactSupport_gradient hc)

/-- The pair `(φ, ∇φ)` of a test function. -/
def testPair (φ : RN N → ℝ) (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hc : HasCompactSupport φ) : Amb N :=
  (MemLp.toLp φ (memLp_of_testFun hφ hc), MemLp.toLp _ (memLp_gradient_of_testFun hφ hc))

lemma testPair_mem {φ : RN N → ℝ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hc : HasCompactSupport φ) {D : Set (RN N)} (hD : tsupport φ ⊆ D) :
    testPair φ hφ hc ∈ testGraph D :=
  ⟨φ, hφ, hc, hD, MemLp.coeFn_toLp (memLp_of_testFun hφ hc),
    MemLp.coeFn_toLp (memLp_gradient_of_testFun hφ hc)⟩

lemma eq_testPair {D : Set (RN N)} {p : Amb N} (hp : p ∈ testGraph D) :
    ∃ φ : RN N → ℝ, ∃ (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (hc : HasCompactSupport φ),
      tsupport φ ⊆ D ∧ p = testPair φ hφ hc := by
  obtain ⟨φ, h1, h2, h3, h4, h5⟩ := hp
  refine ⟨φ, h1, h2, h3, Prod.ext (Lp.ext ?_) (Lp.ext ?_)⟩
  · exact h4.trans (MemLp.coeFn_toLp (memLp_of_testFun h1 h2)).symm
  · exact h5.trans (MemLp.coeFn_toLp (memLp_gradient_of_testFun h1 h2)).symm

/-! ### The test graph is a subspace -/

lemma gradient_add_of_contDiff {φ ψ : RN N → ℝ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (x : RN N) :
    gradient (fun y => φ y + ψ y) x = gradient φ x + gradient ψ x := by
  have h1 := (hφ.differentiable (by simp)) x
  have h2 := (hψ.differentiable (by simp)) x
  rw [gradient, gradient, gradient, fderiv_fun_add h1 h2, map_add]

lemma gradient_smul_of_contDiff (c : ℝ) {φ : RN N → ℝ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (x : RN N) : gradient (fun y => c * φ y) x = c • gradient φ x := by
  have h1 := (hφ.differentiable (by simp)) x
  rw [gradient, gradient, fderiv_const_mul h1 c, map_smul]

lemma zero_mem_testGraph (D : Set (RN N)) : (0 : Amb N) ∈ testGraph D := by
  refine ⟨0, contDiff_const, HasCompactSupport.zero, by simp, ?_, ?_⟩
  · exact Lp.coeFn_zero _ _ _
  · have : gradient (0 : RN N → ℝ) = 0 := by
      ext1 x; simp [gradient]
    rw [this]; exact Lp.coeFn_zero _ _ _

lemma add_mem_testGraph {D : Set (RN N)} {p q : Amb N} (hp : p ∈ testGraph D)
    (hq : q ∈ testGraph D) : p + q ∈ testGraph D := by
  obtain ⟨φ, h1, h2, h3, h4, h5⟩ := hp
  obtain ⟨ψ, k1, k2, k3, k4, k5⟩ := hq
  refine ⟨fun y => φ y + ψ y, h1.add k1, h2.add k2, ?_, ?_, ?_⟩
  · exact (tsupport_add φ ψ).trans (Set.union_subset h3 k3)
  · filter_upwards [Lp.coeFn_add p.1 q.1, h4, k4] with x a b c
    simp only [Prod.fst_add] at a ⊢
    rw [a, Pi.add_apply, b, c]
  · filter_upwards [Lp.coeFn_add p.2 q.2, h5, k5] with x a b c
    rw [Prod.snd_add, a, Pi.add_apply, b, c, gradient_add_of_contDiff h1 k1]

lemma smul_mem_testGraph {D : Set (RN N)} (c : ℝ) {p : Amb N} (hp : p ∈ testGraph D) :
    c • p ∈ testGraph D := by
  obtain ⟨φ, h1, h2, h3, h4, h5⟩ := hp
  refine ⟨fun y => c * φ y, contDiff_const.mul h1, h2.mul_left, ?_, ?_, ?_⟩
  · exact (tsupport_mul_subset_right).trans h3
  · filter_upwards [Lp.coeFn_smul c p.1, h4] with x a b
    simp only [Prod.smul_fst] at a ⊢
    rw [a, Pi.smul_apply, b, smul_eq_mul]
  · filter_upwards [Lp.coeFn_smul c p.2, h5] with x a b
    rw [Prod.smul_snd, a, Pi.smul_apply, b, gradient_smul_of_contDiff c h1]

lemma mem_testGraph_of_mem_span {D : Set (RN N)} {p : Amb N}
    (hp : p ∈ Submodule.span ℝ (testGraph D)) : p ∈ testGraph D := by
  induction hp using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact zero_mem_testGraph D
  | add x y _ _ hx hy => exact add_mem_testGraph hx hy
  | smul c x _ hx => exact smul_mem_testGraph c hx

lemma exists_seq_testGraph {D : Set (RN N)} {p : Amb N} (hp : p ∈ H D) :
    ∃ q : ℕ → Amb N, (∀ n, q n ∈ testGraph D) ∧ Tendsto q atTop (𝓝 p) := by
  have : p ∈ closure (Submodule.span ℝ (testGraph D) : Set (Amb N)) := by
    rw [← Submodule.topologicalClosure_coe]; exact hp
  obtain ⟨q, hq, hlim⟩ := mem_closure_iff_seq_limit.mp this
  exact ⟨q, fun n => mem_testGraph_of_mem_span (hq n), hlim⟩

lemma mem_H_of_tendsto {D : Set (RN N)} {q : ℕ → Amb N} {p : Amb N} (hq : ∀ n, q n ∈ H D)
    (hlim : Tendsto q atTop (𝓝 p)) : p ∈ H D :=
  (Submodule.isClosed_topologicalClosure (Submodule.span ℝ (testGraph D))).mem_of_tendsto hlim
    (Eventually.of_forall hq)

/-- `H_D` is the closure of the test graph. -/
lemma H_eq_closure (D : Set (RN N)) : (H D : Set (Amb N)) = closure (testGraph D) := by
  rw [H, Submodule.topologicalClosure_coe]
  exact subset_antisymm (closure_mono fun _ hp => mem_testGraph_of_mem_span hp)
    (closure_mono Submodule.subset_span)

end FourthRatio

end
