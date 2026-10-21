module

public import RequestProject.Closability

/-!
# Basic facts about the model of `H₀¹(D)`

Elementary consequences of the definitions and closability used
throughout: monotonicity of `H_D` in `D`, vanishing of elements of `H_D` outside `D`,
orthogonality of form domains of disjoint sets, algebraic identities for `q` and `⟨·,·⟩`.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Function
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

variable {N : ℕ}

lemma testGraph_mono {D₁ D₂ : Set (RN N)} (h : D₁ ⊆ D₂) : testGraph D₁ ⊆ testGraph D₂ := by
  rintro p ⟨φ, h1, h2, h3, h4, h5⟩
  exact ⟨φ, h1, h2, h3.trans h, h4, h5⟩

lemma H_mono {D₁ D₂ : Set (RN N)} (h : D₁ ⊆ D₂) : H D₁ ≤ H D₂ :=
  Submodule.topologicalClosure_mono (Submodule.span_mono (testGraph_mono h))

lemma testGraph_subset_H (D : Set (RN N)) : testGraph D ⊆ H D :=
  Submodule.subset_span.trans (Submodule.le_topologicalClosure _)

/-- The closed subspace of pairs vanishing (both components) almost everywhere on `s`. -/
def vanishOn (s : Set (RN N)) : Submodule ℝ (Amb N) :=
  (LinearMap.ker (LpToLpRestrictCLM (RN N) ℝ ℝ volume 2 s).toLinearMap).comap
      (LinearMap.fst ℝ (L2 N) (L2v N)) ⊓
    (LinearMap.ker (LpToLpRestrictCLM (RN N) (RN N) ℝ volume 2 s).toLinearMap).comap
      (LinearMap.snd ℝ (L2 N) (L2v N))

lemma mem_vanishOn {s : Set (RN N)} {p : Amb N} :
    p ∈ vanishOn s ↔ (p.1 : RN N → ℝ) =ᵐ[volume.restrict s] 0 ∧
      (p.2 : RN N → RN N) =ᵐ[volume.restrict s] 0 := by
  simp only [vanishOn, Submodule.mem_inf, Submodule.mem_comap, LinearMap.mem_ker,
    LinearMap.coe_fst, LinearMap.coe_snd, ContinuousLinearMap.coe_coe,
    Lp.eq_zero_iff_ae_eq_zero]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(LpToLpRestrictCLM_coeFn ℝ s p.1).symm.trans h1,
      (LpToLpRestrictCLM_coeFn ℝ s p.2).symm.trans h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(LpToLpRestrictCLM_coeFn ℝ s p.1).trans h1,
      (LpToLpRestrictCLM_coeFn ℝ s p.2).trans h2⟩

lemma isClosed_vanishOn (s : Set (RN N)) : IsClosed (vanishOn s : Set (Amb N)) := by
  simp only [vanishOn, Submodule.coe_inf, Submodule.comap_coe, LinearMap.coe_fst,
    LinearMap.coe_snd]
  refine IsClosed.inter ?_ ?_
  · exact (ContinuousLinearMap.isClosed_ker _).preimage continuous_fst
  · exact (ContinuousLinearMap.isClosed_ker _).preimage continuous_snd

lemma testGraph_subset_vanishOn (D : Set (RN N)) : testGraph D ⊆ vanishOn Dᶜ := by
  rintro p ⟨φ, -, -, h3, h4, h5⟩
  rw [SetLike.mem_coe, mem_vanishOn]
  have hsub : Dᶜ ⊆ (tsupport φ)ᶜ := Set.compl_subset_compl.mpr h3
  have hmeas : MeasurableSet (tsupport φ)ᶜ := (isClosed_tsupport φ).isOpen_compl.measurableSet
  refine ⟨?_, ?_⟩
  · refine Filter.EventuallyEq.trans (ae_restrict_of_ae h4) ?_
    refine ae_restrict_of_ae_restrict_of_subset hsub ?_
    refine ae_restrict_of_forall_mem hmeas fun x hx => ?_
    exact image_eq_zero_of_notMem_tsupport hx
  · refine Filter.EventuallyEq.trans (ae_restrict_of_ae h5) ?_
    refine ae_restrict_of_ae_restrict_of_subset hsub ?_
    refine ae_restrict_of_forall_mem hmeas fun x hx => ?_
    simp [gradient, fderiv_of_notMem_tsupport (𝕜 := ℝ) hx]

/-- Elements of `H_D` vanish almost everywhere outside `D`. -/
lemma H_le_vanishOn (D : Set (RN N)) : H D ≤ vanishOn Dᶜ := by
  apply Submodule.topologicalClosure_minimal
  · exact Submodule.span_le.mpr (testGraph_subset_vanishOn D)
  · exact isClosed_vanishOn _

/-! ### Algebra of the forms -/

lemma qf_comm (v w : Amb N) : qf v w = qf w v := real_inner_comm _ _
lemma l2_comm (v w : Amb N) : l2 v w = l2 w v := real_inner_comm _ _

@[simp] lemma qf_add_left (u v w : Amb N) : qf (u + v) w = qf u w + qf v w := inner_add_left _ _ _
@[simp] lemma qf_add_right (u v w : Amb N) : qf u (v + w) = qf u v + qf u w :=
  inner_add_right _ _ _
@[simp] lemma l2_add_left (u v w : Amb N) : l2 (u + v) w = l2 u w + l2 v w := inner_add_left _ _ _
@[simp] lemma l2_add_right (u v w : Amb N) : l2 u (v + w) = l2 u v + l2 u w :=
  inner_add_right _ _ _
@[simp] lemma qf_smul_left (c : ℝ) (v w : Amb N) : qf (c • v) w = c * qf v w :=
  real_inner_smul_left _ _ _
@[simp] lemma qf_smul_right (c : ℝ) (v w : Amb N) : qf v (c • w) = c * qf v w :=
  real_inner_smul_right _ _ _
@[simp] lemma l2_smul_left (c : ℝ) (v w : Amb N) : l2 (c • v) w = c * l2 v w :=
  real_inner_smul_left _ _ _
@[simp] lemma l2_smul_right (c : ℝ) (v w : Amb N) : l2 v (c • w) = c * l2 v w :=
  real_inner_smul_right _ _ _
@[simp] lemma qf_neg_left (v w : Amb N) : qf (-v) w = -qf v w := inner_neg_left _ _
@[simp] lemma qf_neg_right (v w : Amb N) : qf v (-w) = -qf v w := inner_neg_right _ _
@[simp] lemma l2_neg_left (v w : Amb N) : l2 (-v) w = -l2 v w := inner_neg_left _ _
@[simp] lemma l2_neg_right (v w : Amb N) : l2 v (-w) = -l2 v w := inner_neg_right _ _
@[simp] lemma qf_sub_left (u v w : Amb N) : qf (u - v) w = qf u w - qf v w := inner_sub_left _ _ _
@[simp] lemma qf_sub_right (u v w : Amb N) : qf u (v - w) = qf u v - qf u w :=
  inner_sub_right _ _ _
@[simp] lemma l2_sub_left (u v w : Amb N) : l2 (u - v) w = l2 u w - l2 v w := inner_sub_left _ _ _
@[simp] lemma l2_sub_right (u v w : Amb N) : l2 u (v - w) = l2 u v - l2 u w :=
  inner_sub_right _ _ _
@[simp] lemma qf_zero_left (w : Amb N) : qf 0 w = 0 := inner_zero_left _
@[simp] lemma qf_zero_right (w : Amb N) : qf w 0 = 0 := inner_zero_right _
@[simp] lemma l2_zero_left (w : Amb N) : l2 0 w = 0 := inner_zero_left _
@[simp] lemma l2_zero_right (w : Amb N) : l2 w 0 = 0 := inner_zero_right _

lemma qf_sum_left {ι : Type*} (s : Finset ι) (f : ι → Amb N) (w : Amb N) :
    qf (∑ i ∈ s, f i) w = ∑ i ∈ s, qf (f i) w := by
  simp only [qf, Prod.snd_sum, sum_inner]

lemma qf_sum_right {ι : Type*} (s : Finset ι) (f : ι → Amb N) (w : Amb N) :
    qf w (∑ i ∈ s, f i) = ∑ i ∈ s, qf w (f i) := by
  simp only [qf, Prod.snd_sum, inner_sum]

lemma l2_sum_left {ι : Type*} (s : Finset ι) (f : ι → Amb N) (w : Amb N) :
    l2 (∑ i ∈ s, f i) w = ∑ i ∈ s, l2 (f i) w := by
  simp only [l2, Prod.fst_sum, sum_inner]

lemma l2_sum_right {ι : Type*} (s : Finset ι) (f : ι → Amb N) (w : Amb N) :
    l2 w (∑ i ∈ s, f i) = ∑ i ∈ s, l2 w (f i) := by
  simp only [l2, Prod.fst_sum, inner_sum]

lemma qf_self_nonneg (v : Amb N) : 0 ≤ qf v v := real_inner_self_nonneg
lemma l2_self_nonneg (v : Amb N) : 0 ≤ l2 v v := real_inner_self_nonneg

lemma rayleigh_nonneg (v : Amb N) : 0 ≤ rayleigh v :=
  div_nonneg (qf_self_nonneg v) (l2_self_nonneg v)

lemma bshift_eq (γ : ℝ) (v : Amb N) : bshift γ v v = Qshift γ v := rfl

lemma bshift_comm (γ : ℝ) (v w : Amb N) : bshift γ v w = bshift γ w v := by
  simp [bshift, qf_comm v w, l2_comm v w]

lemma continuous_qf : Continuous (fun p : Amb N × Amb N => qf p.1 p.2) :=
  continuous_inner.comp ((continuous_snd.comp continuous_fst).prodMk
    (continuous_snd.comp continuous_snd))

lemma continuous_l2 : Continuous (fun p : Amb N × Amb N => l2 p.1 p.2) :=
  continuous_inner.comp ((continuous_fst.comp continuous_fst).prodMk
    (continuous_fst.comp continuous_snd))

lemma continuous_bshift (γ : ℝ) : Continuous (fun p : Amb N × Amb N => bshift γ p.1 p.2) :=
  continuous_qf.sub (continuous_const.mul continuous_l2)

/-! ### Orthogonality of form domains of disjoint sets -/

lemma orthogonal_of_disjoint {D₁ D₂ : Set (RN N)} (h₁ : MeasurableSet D₁)
    (h₂ : MeasurableSet D₂) (hd : Disjoint D₁ D₂) {v w : Amb N} (hv : v ∈ H D₁)
    (hw : w ∈ H D₂) : qf v w = 0 ∧ l2 v w = 0 := by
  obtain ⟨hv1, hv2⟩ := mem_vanishOn.mp (H_le_vanishOn D₁ hv)
  obtain ⟨hw1, hw2⟩ := mem_vanishOn.mp (H_le_vanishOn D₂ hw)
  rw [EventuallyEq, ae_restrict_iff' h₁.compl] at hv1 hv2
  rw [EventuallyEq, ae_restrict_iff' h₂.compl] at hw1 hw2
  constructor
  · rw [qf, L2.inner_def]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hv2, hw2] with x hx1 hx2
    by_cases hx : x ∈ D₁
    · simp [hx2 (fun h => Set.disjoint_left.mp hd hx h)]
    · simp [hx1 hx]
  · rw [l2, L2.inner_def]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hv1, hw1] with x hx1 hx2
    by_cases hx : x ∈ D₁
    · simp [hx2 (fun h => Set.disjoint_left.mp hd hx h)]
    · simp [hx1 hx]

/-! ### Min–max upper bounds and dependence on the form domain only -/

lemma eigenvalue_congr {D₁ D₂ : Set (RN N)} (h : H D₁ = H D₂) (j : ℕ) :
    eigenvalue D₁ j = eigenvalue D₂ j := by
  simp [eigenvalue, h]

lemma sSup_rayleigh_nonneg (V : Submodule ℝ (Amb N)) :
    0 ≤ sSup (rayleigh '' {v | v ∈ V ∧ v ≠ 0}) :=
  Real.sSup_nonneg (by rintro _ ⟨v, -, rfl⟩; exact rayleigh_nonneg v)

lemma eigenvalue_nonneg (D : Set (RN N)) (j : ℕ) : 0 ≤ eigenvalue D j :=
  Real.sInf_nonneg (by rintro _ ⟨V, -, rfl⟩; exact sSup_rayleigh_nonneg V)

/-- Min–max upper bound: a `j`-dimensional subspace of `H_D` on which `q ≤ t ‖·‖²` gives
`λ_j(D) ≤ t`. -/
lemma eigenvalue_le_of_subspace {D : Set (RN N)} {V : Submodule ℝ (Amb N)} (hV : V ≤ H D)
    {j : ℕ} (hj : Module.finrank ℝ V = j) {t : ℝ} (ht : 0 ≤ t)
    (hq : ∀ v ∈ V, qf v v ≤ t * l2 v v) : eigenvalue D j ≤ t := by
  have hbdd : BddBelow ((fun V : Submodule ℝ (Amb N) =>
      sSup (rayleigh '' {v | v ∈ V ∧ v ≠ 0})) '' {V | V ≤ H D ∧ Module.finrank ℝ V = j}) :=
    ⟨0, by rintro _ ⟨W, -, rfl⟩; exact sSup_rayleigh_nonneg W⟩
  refine (csInf_le hbdd ⟨V, ⟨hV, hj⟩, rfl⟩).trans ?_
  refine Real.sSup_le ?_ ht
  rintro _ ⟨v, ⟨hv, -⟩, rfl⟩
  rcases (l2_self_nonneg v).eq_or_lt with h | h
  · simp [rayleigh, ← h, ht]
  · rw [rayleigh, div_le_iff₀ h]
    exact hq v hv

/-- Closability of the gradient: an element of `H_D` with vanishing `L²` norm is zero (proved
directly by integration by parts, `snd_eq_zero_of_mem_H`). -/
lemma eq_zero_of_l2_self_eq_zero {D : Set (RN N)} {v : Amb N} (hv : v ∈ H D) (h : l2 v v = 0) :
    v = 0 := by
  have h1 : v.1 = 0 := inner_self_eq_zero.mp h
  exact Prod.ext h1 (snd_eq_zero_of_mem_H hv h1)

lemma l2_self_pos {D : Set (RN N)} {v : Amb N} (hv : v ∈ H D) (h0 : v ≠ 0) : 0 < l2 v v :=
  (l2_self_nonneg v).lt_of_ne (fun h => h0 (eq_zero_of_l2_self_eq_zero hv h.symm))

/-- The first eigenvalue is at most the Rayleigh quotient of any nonzero element. -/
lemma eigenvalue_one_le_rayleigh {D : Set (RN N)}
    {v : Amb N} (hv : v ∈ H D) (hv0 : v ≠ 0) :
    eigenvalue D 1 ≤ rayleigh v := by
  have h := l2_self_pos hv hv0
  refine eigenvalue_le_of_subspace (V := Submodule.span ℝ {v}) ?_ (finrank_span_singleton hv0)
    (rayleigh_nonneg v) ?_
  · exact (Submodule.span_le).mpr (Set.singleton_subset_iff.mpr hv)
  · intro w hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    simp only [qf_smul_left, qf_smul_right, l2_smul_left, l2_smul_right]
    rw [rayleigh, div_mul_eq_mul_div, le_div_iff₀ h]
    nlinarith [sq_nonneg c]

end FourthRatio

end
