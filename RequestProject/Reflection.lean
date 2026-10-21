module

public import RequestProject.TestPair

/-!
# Orthogonal changes of variables acting on `H₀¹`

For a linear isometry `R` of `ℝ^N` and a centre `y`, the affine isometry
`σ x = y + R (x - y)` acts on pairs `(v, g)` by `(v ∘ σ, R⁻¹ ∘ g ∘ σ)` (the chain rule for the
weak gradient).  This action preserves the forms `q` and `⟨·,·⟩`, maps `H₀¹(B_r(y))` to itself
and hence maps weak eigenfunctions of a ball centred at `y` to weak eigenfunctions.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Function Set
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

variable {N : ℕ}

/-- The affine isometry `σ x = y + R (x - y)`. -/
def isoMap (R : RN N ≃ₗᵢ[ℝ] RN N) (y x : RN N) : RN N := y + R (x - y)

lemma isoMap_apply (R : RN N ≃ₗᵢ[ℝ] RN N) (y x : RN N) : isoMap R y x = y + R (x - y) := rfl

lemma isoMap_self (R : RN N ≃ₗᵢ[ℝ] RN N) (y : RN N) : isoMap R y y = y := by
  simp [isoMap]

lemma isoMap_sub (R : RN N ≃ₗᵢ[ℝ] RN N) (y x : RN N) : isoMap R y x - y = R (x - y) := by
  simp [isoMap]

lemma norm_isoMap_sub (R : RN N ≃ₗᵢ[ℝ] RN N) (y x : RN N) :
    ‖isoMap R y x - y‖ = ‖x - y‖ := by
  rw [isoMap_sub, LinearIsometryEquiv.norm_map]

/-- `σ` as a homeomorphism. -/
def isoHomeo (R : RN N ≃ₗᵢ[ℝ] RN N) (y : RN N) : RN N ≃ₜ RN N :=
  ((Homeomorph.subRight y).trans R.toHomeomorph).trans (Homeomorph.addLeft y)

lemma isoHomeo_apply (R : RN N ≃ₗᵢ[ℝ] RN N) (y x : RN N) : isoHomeo R y x = isoMap R y x := rfl

lemma continuous_isoMap (R : RN N ≃ₗᵢ[ℝ] RN N) (y : RN N) : Continuous (isoMap R y) :=
  (isoHomeo R y).continuous

lemma measurePreserving_isoMap (R : RN N ≃ₗᵢ[ℝ] RN N) (y : RN N) :
    MeasurePreserving (isoMap R y) volume volume := by
  have h1 : MeasurePreserving (fun x : RN N => x - y) volume volume :=
    measurePreserving_sub_right volume y
  have h2 : MeasurePreserving R volume volume := R.measurePreserving
  have h3 : MeasurePreserving (fun x : RN N => y + x) volume volume :=
    measurePreserving_add_left volume y
  exact (h3.comp h2).comp h1

lemma measurableEmbedding_isoMap (R : RN N ≃ₗᵢ[ℝ] RN N) (y : RN N) :
    MeasurableEmbedding (isoMap R y) :=
  (isoHomeo R y).measurableEmbedding

lemma isoMap_mem_ball_iff (R : RN N ≃ₗᵢ[ℝ] RN N) (y x : RN N) (r : ℝ) :
    isoMap R y x ∈ ball y r ↔ x ∈ ball y r := by
  simp only [mem_ball, dist_eq_norm, norm_isoMap_sub]

/-- The action of `σ` on pairs `(v, g) ↦ (v ∘ σ, R⁻¹ ∘ g ∘ σ)`. -/
def isoOp (R : RN N ≃ₗᵢ[ℝ] RN N) (y : RN N) : Amb N →L[ℝ] Amb N :=
  ((Lp.compMeasurePreservingₗᵢ ℝ (isoMap R y)
      (measurePreserving_isoMap R y)).toContinuousLinearMap).prodMap
    ((ContinuousLinearMap.compLpL 2 volume
        (R.symm.toContinuousLinearEquiv : RN N →L[ℝ] RN N)).comp
      (Lp.compMeasurePreservingₗᵢ ℝ (isoMap R y)
        (measurePreserving_isoMap R y)).toContinuousLinearMap)

lemma isoOp_fst_ae (R : RN N ≃ₗᵢ[ℝ] RN N) (y : RN N) (u : Amb N) :
    ((isoOp R y u).1 : RN N → ℝ) =ᵐ[volume] fun x => (u.1 : RN N → ℝ) (isoMap R y x) :=
  Lp.coeFn_compMeasurePreserving _ _

lemma isoOp_snd_ae (R : RN N ≃ₗᵢ[ℝ] RN N) (y : RN N) (u : Amb N) :
    ((isoOp R y u).2 : RN N → RN N) =ᵐ[volume]
      fun x => R.symm ((u.2 : RN N → RN N) (isoMap R y x)) := by
  have h1 := ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := (volume : Measure (RN N)))
    (R.symm.toContinuousLinearEquiv : RN N →L[ℝ] RN N)
    (Lp.compMeasurePreserving (isoMap R y) (measurePreserving_isoMap R y) u.2)
  have h2 := Lp.coeFn_compMeasurePreserving u.2 (measurePreserving_isoMap R y)
  have hdef : (isoOp R y u).2 = ContinuousLinearMap.compLpL 2 volume
      (R.symm.toContinuousLinearEquiv : RN N →L[ℝ] RN N)
      (Lp.compMeasurePreserving (isoMap R y) (measurePreserving_isoMap R y) u.2) := rfl
  filter_upwards [h1, h2] with x e1 e2
  rw [hdef, e1, e2]
  rfl

/-- `σ` preserves the `L²` product. -/
lemma l2_isoOp (R : RN N ≃ₗᵢ[ℝ] RN N) (y : RN N) (u v : Amb N) :
    l2 (isoOp R y u) (isoOp R y v) = l2 u v := by
  simp only [l2, MeasureTheory.L2.inner_def]
  have hmp := measurePreserving_isoMap R y
  conv_rhs => rw [← hmp.integral_comp (measurableEmbedding_isoMap R y)]
  refine integral_congr_ae ?_
  filter_upwards [isoOp_fst_ae R y u, isoOp_fst_ae R y v] with x e1 e2
  rw [e1, e2]

/-- `σ` preserves the Dirichlet form. -/
lemma qf_isoOp (R : RN N ≃ₗᵢ[ℝ] RN N) (y : RN N) (u v : Amb N) :
    qf (isoOp R y u) (isoOp R y v) = qf u v := by
  simp only [qf, MeasureTheory.L2.inner_def]
  have hmp := measurePreserving_isoMap R y
  conv_rhs => rw [← hmp.integral_comp (measurableEmbedding_isoMap R y)]
  refine integral_congr_ae ?_
  filter_upwards [isoOp_snd_ae R y u, isoOp_snd_ae R y v] with x e1 e2
  rw [e1, e2, LinearIsometryEquiv.inner_map_map]

/-- Gradient of `φ ∘ σ`. -/
lemma gradient_comp_isoMap (R : RN N ≃ₗᵢ[ℝ] RN N) (y : RN N) {φ : RN N → ℝ}
    (hφ : Differentiable ℝ φ) (x : RN N) :
    gradient (fun z => φ (isoMap R y z)) x = R.symm (gradient φ (isoMap R y x)) := by
  have hσ : HasFDerivAt (isoMap R y) (R.toContinuousLinearEquiv : RN N →L[ℝ] RN N) x := by
    have := ((R.toContinuousLinearEquiv : RN N →L[ℝ] RN N).hasFDerivAt (x := x - y)).comp x
      ((hasFDerivAt_id x).sub_const y)
    have := this.const_add y
    convert this using 1
    · rfl
    · simp
  have hφ' : HasGradientAt φ (gradient φ (isoMap R y x)) (isoMap R y x) :=
    (hφ _).hasGradientAt
  rw [hasGradientAt_iff_hasFDerivAt] at hφ'
  have hc := hφ'.comp x hσ
  have hg : HasGradientAt (fun z => φ (isoMap R y z)) (R.symm (gradient φ (isoMap R y x))) x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    convert hc using 1
    · rfl
    · ext v
      change inner ℝ (R.symm (gradient φ (isoMap R y x))) v =
        inner ℝ (gradient φ (isoMap R y x)) (R v)
      rw [← LinearIsometryEquiv.inner_map_map R, LinearIsometryEquiv.apply_symm_apply]
  exact hg.gradient

/-- `σ` maps test pairs of a ball centred at `y` to test pairs of the same ball. -/
lemma isoOp_mem_testGraph (R : RN N ≃ₗᵢ[ℝ] RN N) (y : RN N) (r : ℝ) {p : Amb N}
    (hp : p ∈ testGraph (ball y r)) : isoOp R y p ∈ testGraph (ball y r) := by
  obtain ⟨φ, hφ, hc, hs, h1, h2⟩ := hp
  have hσs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (isoMap R y) :=
    contDiff_const.add ((R.toContinuousLinearEquiv : RN N →L[ℝ] RN N).contDiff.comp
      (contDiff_id.sub contDiff_const))
  refine ⟨fun z => φ (isoMap R y z), hφ.comp hσs, hc.comp_homeomorph (isoHomeo R y), ?_, ?_, ?_⟩
  · intro x hx
    have : x ∈ isoHomeo R y ⁻¹' tsupport φ := by
      rw [← tsupport_comp_eq_preimage]; exact hx
    rw [← isoMap_mem_ball_iff R y x r]
    exact hs this
  · have hq := (measurePreserving_isoMap R y).quasiMeasurePreserving.ae_eq_comp h1
    filter_upwards [isoOp_fst_ae R y p, hq] with x e1 e2
    rw [e1]; exact e2
  · have hq := (measurePreserving_isoMap R y).quasiMeasurePreserving.ae_eq_comp h2
    have hd : Differentiable ℝ φ := hφ.differentiable (by simp)
    filter_upwards [isoOp_snd_ae R y p, hq] with x e1 e2
    rw [e1, gradient_comp_isoMap R y hd]
    simp only [Function.comp_apply] at e2
    rw [e2]

/-- `σ` maps `H₀¹(B_r(y))` to itself. -/
lemma isoOp_mem_H (R : RN N ≃ₗᵢ[ℝ] RN N) (y : RN N) (r : ℝ) {p : Amb N}
    (hp : p ∈ H (ball y r)) : isoOp R y p ∈ H (ball y r) := by
  obtain ⟨q, hqT, hq⟩ := exists_seq_testGraph hp
  exact mem_H_of_tendsto (fun n => testGraph_subset_H _ (isoOp_mem_testGraph R y r (hqT n)))
    (((isoOp R y).continuous.tendsto p).comp hq)

/-- For an involutive `R`, the action is an involution. -/
lemma isoOp_isoOp (R : RN N ≃ₗᵢ[ℝ] RN N) (hR : ∀ v, R (R v) = v) (y : RN N) (u : Amb N) :
    isoOp R y (isoOp R y u) = u := by
  have hσσ : ∀ x, isoMap R y (isoMap R y x) = x := fun x => by
    simp [isoMap, hR]
  have hRs : ∀ v, R.symm v = R v := fun v => by
    exact R.injective (by rw [R.apply_symm_apply, hR])
  have hq := (measurePreserving_isoMap R y).quasiMeasurePreserving
  refine Prod.ext (Lp.ext ?_) (Lp.ext ?_)
  · have h2 := hq.ae_eq_comp (isoOp_fst_ae R y u)
    filter_upwards [isoOp_fst_ae R y (isoOp R y u), h2] with x e1 e2
    rw [e1]; simp only [Function.comp_apply] at e2; rw [e2, hσσ]
  · have h2 := hq.ae_eq_comp (isoOp_snd_ae R y u)
    filter_upwards [isoOp_snd_ae R y (isoOp R y u), h2] with x e1 e2
    rw [e1]; simp only [Function.comp_apply] at e2; rw [e2, hσσ, hRs, hRs, hR]

/-- For an involutive `R`, `σ` maps weak eigenfunctions of `B_r(y)` to weak eigenfunctions. -/
lemma isoOp_weak (R : RN N ≃ₗᵢ[ℝ] RN N) (hR : ∀ v, R (R v) = v) (y : RN N) (r : ℝ)
    {u : Amb N} {μ : ℝ} (hu : ∀ φ ∈ H (ball y r), qf u φ = μ * l2 u φ) :
    ∀ φ ∈ H (ball y r), qf (isoOp R y u) φ = μ * l2 (isoOp R y u) φ := by
  intro φ hφ
  have e := hu _ (isoOp_mem_H R y r hφ)
  rw [← qf_isoOp R y u, ← l2_isoOp R y u, isoOp_isoOp R hR] at e
  exact e

end FourthRatio

end
