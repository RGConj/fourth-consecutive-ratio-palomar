module

public import RequestProject.SobolevTrunc

/-! # A smooth scalar chain rule for the original graph-closure Sobolev space -/

@[expose] public section
open MeasureTheory Metric Filter Topology Function
open scoped RealInnerProductSpace ENNReal
noncomputable section
namespace FourthRatio

/-- Smooth scalar maps fixing zero, with explicitly bounded derivatives. -/
structure SmoothScalarChain where
  toFun : ℝ → ℝ
  derivFun : ℝ → ℝ
  smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) toFun
  zero : toFun 0 = 0
  hasDeriv : ∀ t, HasDerivAt toFun (derivFun t) t
  deriv_continuous : Continuous derivFun
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  lipschitz : ∀ a b, |toFun a - toFun b| ≤ bound * |a - b|
  deriv_bound : ∀ t, |derivFun t| ≤ bound

lemma SmoothScalarChain.abs_le (F : SmoothScalarChain) (t : ℝ) :
    |F.toFun t| ≤ F.bound * |t| := by
  simpa only [F.zero, sub_zero] using F.lipschitz t 0

variable {N : ℕ}

lemma chain_memLp_fun (F : SmoothScalarChain) (f : L2 N) :
    MemLp (fun x => F.toFun ((f : RN N → ℝ) x)) 2 volume := by
  refine (Lp.memLp f).of_le_mul (c := F.bound) ((F.smooth).continuous.comp_aestronglyMeasurable
    (Lp.aestronglyMeasurable f)) (Eventually.of_forall fun x => ?_)
  simpa only [Real.norm_eq_abs] using F.abs_le _

lemma chain_memLp_deriv_smul (F : SmoothScalarChain) (p : Amb N) :
    MemLp (fun x => F.derivFun ((p.1 : RN N → ℝ) x) • (p.2 : RN N → RN N) x) 2 volume := by
  refine (Lp.memLp p.2).of_le_mul (c := F.bound)
    (((F.deriv_continuous).comp_aestronglyMeasurable (Lp.aestronglyMeasurable p.1)).smul
      (Lp.aestronglyMeasurable p.2)) (Eventually.of_forall fun x => ?_)
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (F.deriv_bound _) (norm_nonneg _)

/-- The composition `G_n ∘ p` of a pair with the smooth truncation `G_n`, with the gradient
given by the chain rule. -/
def chainPair (F : SmoothScalarChain) (p : Amb N) : Amb N :=
  (MemLp.toLp _ (chain_memLp_fun F p.1), MemLp.toLp _ (chain_memLp_deriv_smul F p))

lemma chainPair_fst_ae (F : SmoothScalarChain) (p : Amb N) :
    ((chainPair F p).1 : RN N → ℝ) =ᵐ[volume] fun x => F.toFun ((p.1 : RN N → ℝ) x) :=
  MemLp.coeFn_toLp (chain_memLp_fun F p.1)

lemma chainPair_snd_ae (F : SmoothScalarChain) (p : Amb N) :
    ((chainPair F p).2 : RN N → RN N) =ᵐ[volume]
      fun x => F.derivFun ((p.1 : RN N → ℝ) x) • (p.2 : RN N → RN N) x :=
  MemLp.coeFn_toLp (chain_memLp_deriv_smul F p)

lemma chainPair_mem_testGraph (F : SmoothScalarChain) {D : Set (RN N)} {p : Amb N} (hp : p ∈ testGraph D) :
    chainPair F p ∈ testGraph D := by
  obtain ⟨φ, h1, h2, h3, h4, h5⟩ := hp
  have hG0 : F.toFun 0 = 0 := F.zero
  refine ⟨fun y => F.toFun (φ y), (F.smooth).comp h1, h2.comp_left hG0,
    (tsupport_comp_subset hG0 φ).trans h3, ?_, ?_⟩
  · filter_upwards [chainPair_fst_ae F p, h4] with x a b
    rw [a, b]
  · filter_upwards [chainPair_snd_ae F p, h4, h5] with x a b c
    rw [a, b, c, gradient_comp_real (F.hasDeriv (φ x))
      ((h1.differentiable (by simp)) x)]

lemma exists_subseq_chainPair_tendsto (F : SmoothScalarChain) {q : ℕ → Amb N} {p : Amb N}
    (hq : Tendsto q atTop (𝓝 p)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (fun k => chainPair F (q (φ k))) atTop (𝓝 (chainPair F p)) := by
  have h1 : Tendsto (fun k => (q k).1) atTop (𝓝 p.1) := (continuous_fst.tendsto p).comp hq
  have h2 : Tendsto (fun k => (q k).2) atTop (𝓝 p.2) := (continuous_snd.tendsto p).comp hq
  obtain ⟨φ, hφ, hae⟩ := (tendstoInMeasure_of_tendsto_Lp h1).exists_seq_tendsto_ae
  refine ⟨φ, hφ, ?_⟩
  have hC : 0 ≤ F.bound := F.bound_nonneg
  have hf : Tendsto (fun k => (chainPair F (q (φ k))).1) atTop (𝓝 (chainPair F p).1) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hb : ∀ k, ‖(chainPair F (q (φ k))).1 - (chainPair F p).1‖ ≤
        F.bound * ‖(q (φ k)).1 - p.1‖ + 0 * ‖(q (φ k)).1 - p.1‖ := fun k => by
      refine Lp2_norm_le_add _ _ _ hC le_rfl ?_
      filter_upwards [Lp.coeFn_sub (chainPair F (q (φ k))).1 (chainPair F p).1,
        Lp.coeFn_sub (q (φ k)).1 p.1, chainPair_fst_ae F (q (φ k)), chainPair_fst_ae F p]
        with x a b c d
      rw [a, Pi.sub_apply, c, d, b, Pi.sub_apply, zero_mul, add_zero, Real.norm_eq_abs,
        Real.norm_eq_abs]
      exact F.lipschitz _ _
    refine squeeze_zero (fun k => norm_nonneg _) hb ?_
    have := (tendsto_iff_norm_sub_tendsto_zero.mp (h1.comp hφ.tendsto_atTop)).const_mul F.bound
    simpa using this
  have hs : Tendsto (fun k => (chainPair F (q (φ k))).2) atTop (𝓝 (chainPair F p).2) := by
    refine L2v_mul_tendsto (a := fun k x => F.derivFun (((q (φ k)).1 : RN N → ℝ) x))
      (b := fun x => F.derivFun ((p.1 : RN N → ℝ) x)) hC
      (fun k => (F.deriv_continuous).comp_aestronglyMeasurable (Lp.aestronglyMeasurable _))
      ((F.deriv_continuous).comp_aestronglyMeasurable (Lp.aestronglyMeasurable _))
      (fun k x => F.deriv_bound _) (fun x => F.deriv_bound _) (h2.comp hφ.tendsto_atTop)
      (fun k => chainPair_snd_ae F _) (chainPair_snd_ae F p) ?_
    filter_upwards [hae] with x hx
    exact (((F.deriv_continuous).tendsto _).comp hx).smul_const _
  exact hf.prodMk_nhds hs

lemma chainPair_mem_H (F : SmoothScalarChain) {D : Set (RN N)} {p : Amb N} (hp : p ∈ H D) : chainPair F p ∈ H D := by
  obtain ⟨q, hqT, hq⟩ := exists_seq_testGraph hp
  obtain ⟨φ, -, hφ⟩ := exists_subseq_chainPair_tendsto F hq
  exact mem_H_of_tendsto (fun k => testGraph_subset_H D (chainPair_mem_testGraph F (hqT (φ k)))) hφ


end FourthRatio
end
