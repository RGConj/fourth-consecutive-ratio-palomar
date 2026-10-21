module

public import RequestProject.MainProjection

/-!
# Local negative sections (proof of Lemma 5.5, local part)

For `u` near `u₀` and a fixed test-function combination `η` supported in `D₊(u₀)`,
`φ(u) = η - (𝔟(η,u₊)/𝔟(u₊,u₊)) u₊` is a negative vector of
`W(u) = {v ∈ H₀¹(D₊(u)) : 𝔟(v,u₊) = 0}`; this space has negative index one.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Function
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

variable {N : ℕ}

/-- Extracting a witness from a lower bound on the negative index. -/
lemma exists_of_le_negIndex {M : Type*} [AddCommGroup M] [Module ℝ M] {b : M → M → ℝ}
    {X : Submodule ℝ M} {k : ℕ} (h : (k : ℕ∞) ≤ negIndex b X) :
    ∃ W : Submodule ℝ M, W ≤ X ∧ FiniteDimensional ℝ W ∧ (∀ v ∈ W, v ≠ 0 → b v v < 0) ∧
      k ≤ Module.finrank ℝ W := by
  by_contra hne
  push_neg at hne
  have : negIndex b X ≤ ((k - 1 : ℕ) : ℕ∞) := by
    refine iSup_le fun W => iSup_le fun hW => iSup_le fun hfin => iSup_le fun hneg => ?_
    have := hne W hW hfin hneg
    exact_mod_cast (by omega : Module.finrank ℝ W ≤ k - 1)
  have h2 := h.trans this
  have hk : 0 < k := by
    by_contra h0
    push_neg at h0
    obtain ⟨W, hW, hfin, hneg, -⟩ : ∃ W : Submodule ℝ M, W ≤ X ∧ FiniteDimensional ℝ W ∧
        (∀ v ∈ W, v ≠ 0 → b v v < 0) ∧ k ≤ Module.finrank ℝ W :=
      ⟨⊥, bot_le, inferInstance, fun v hv hv0 => absurd ((Submodule.mem_bot ℝ).mp hv) hv0,
        by omega⟩
    exact absurd (hne W hW hfin hneg) (by omega)
  have : k ≤ k - 1 := by exact_mod_cast h2
  omega

namespace Setup

variable (S : Setup N)

lemma posSign_negSign_disjoint (u : E4) :
    Disjoint (posSign S.Ω (S.fU u)) (negSign S.Ω (S.fU u)) := by
  rw [Set.disjoint_left]
  intro x hx1 hx2
  have h1 : 0 < S.fU u x := hx1.2
  have h2 : S.fU u x < 0 := hx2.2
  linarith

lemma orth_pos_neg (u : E4) {η ζ : Amb N} (hη : η ∈ H (posSign S.Ω (S.fU u)))
    (hζ : ζ ∈ H (negSign S.Ω (S.fU u))) : qf η ζ = 0 ∧ l2 η ζ = 0 :=
  orthogonal_of_disjoint (isOpen_posSign S.hΩadm.1 (S.fU_rep u).1).measurableSet
    (isOpen_negSign S.hΩadm.1 (S.fU_rep u).1).measurableSet (S.posSign_negSign_disjoint u) hη hζ

lemma posPart_mem_posSign (u : E4) : posPart (S.U u) ∈ H (posSign S.Ω (S.fU u)) :=
  (parts_mem S.hΩadm (S.U_mem u) (S.fU_rep u)).1

lemma negPart_mem_negSign (u : E4) : negPart (S.U u) ∈ H (negSign S.Ω (S.fU u)) :=
  (parts_mem S.hΩadm (S.U_mem u) (S.fU_rep u)).2

/-- A globally continuous expression for `𝔟(η, u₊)`, valid whenever `η ∈ H₀¹(D₊(u))`. -/
def gq (η : Amb N) (u : E4) : ℝ :=
  ∑ i : Fin 4, u i * (eigenvalue S.Ω ((i : ℕ) + 1) * l2 (S.e i) η) -
    S.b * l2 η (posPart (S.U u))

lemma bshift_eq_gq {u : E4} {η : Amb N} (hη : η ∈ H (posSign S.Ω (S.fU u))) :
    bshift S.b η (posPart (S.U u)) = S.gq η u := by
  have hηΩ : η ∈ H S.Ω := H_mono (posSign_subset _ _) hη
  have hqn : qf η (negPart (S.U u)) = 0 := (S.orth_pos_neg u hη (S.negPart_mem_negSign u)).1
  have hpp : posPart (S.U u) = S.U u + negPart (S.U u) :=
    sub_eq_iff_eq_add.mp (S.posPart_sub_negPart_U u)
  have hq : qf η (posPart (S.U u)) =
      ∑ i : Fin 4, u i * (eigenvalue S.Ω ((i : ℕ) + 1) * l2 (S.e i) η) := by
    rw [hpp, qf_add_right, hqn, add_zero, U, qf_sum_right]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [qf_smul_right, qf_comm, (S.he.1 i).2.2 _ hηΩ]
  rw [bshift, hq, gq]

lemma continuous_gq (η : Amb N) : Continuous (S.gq η) := by
  refine Continuous.sub (continuous_finsetSum _ fun i _ => ?_) (continuous_const.mul ?_)
  · exact ((continuous_apply i).comp (PiLp.continuous_ofLp 2 _)).mul continuous_const
  · exact continuous_inner.comp (continuous_const.prodMk S.continuous_posPart_U_fst)

/-- `𝔟(u₊, u₊)` as a function of `u`. -/
def bpp (u : E4) : ℝ := bshift S.b (posPart (S.U u)) (posPart (S.U u))

lemma continuous_bpp : Continuous S.bpp := S.continuous_bshift_posPart

/-- The local negative section `φ(u) = η - (𝔟(η,u₊)/𝔟(u₊,u₊)) u₊`. -/
def phi (η : Amb N) (u : E4) : Amb N := η - (S.gq η u / S.bpp u) • posPart (S.U u)

/-- The Gram entry `𝔟(φ_η(u), φ_ζ(u))` written through continuous scalars. -/
def Bf (η ζ : Amb N) (u : E4) : ℝ :=
  bshift S.b η ζ - (S.gq ζ u / S.bpp u) * S.gq η u - (S.gq η u / S.bpp u) * S.gq ζ u +
    (S.gq η u / S.bpp u) * (S.gq ζ u / S.bpp u) * S.bpp u

lemma phi_mem {η : Amb N} {u : E4} (hη : η ∈ H (posSign S.Ω (S.fU u))) :
    S.phi η u ∈ H (posSign S.Ω (S.fU u)) :=
  Submodule.sub_mem _ hη (Submodule.smul_mem _ _ (S.posPart_mem_posSign u))

lemma bshift_phi_pp {η : Amb N} {u : E4} (hη : η ∈ H (posSign S.Ω (S.fU u)))
    (hb : S.bpp u ≠ 0) : bshift S.b (S.phi η u) (posPart (S.U u)) = 0 := by
  have h := S.bshift_eq_gq hη
  simp only [phi, bshift, qf_sub_left, qf_smul_left, l2_sub_left, l2_smul_left] at h ⊢
  have hb' : qf (posPart (S.U u)) (posPart (S.U u)) - S.b * l2 (posPart (S.U u))
      (posPart (S.U u)) = S.bpp u := rfl
  field_simp
  linear_combination h * S.bpp u - S.gq η u * hb'

lemma bshift_phi_phi {η ζ : Amb N} {u : E4} (hη : η ∈ H (posSign S.Ω (S.fU u)))
    (hζ : ζ ∈ H (posSign S.Ω (S.fU u))) :
    bshift S.b (S.phi η u) (S.phi ζ u) = S.Bf η ζ u := by
  have h1 := S.bshift_eq_gq hη
  have h2 := S.bshift_eq_gq hζ
  rw [bshift_comm] at h2
  simp only [phi, Bf]
  set t := S.gq η u / S.bpp u
  set s := S.gq ζ u / S.bpp u
  set p := posPart (S.U u)
  have : bshift S.b (η - t • p) (ζ - s • p) =
      bshift S.b η ζ - s * bshift S.b η p - t * bshift S.b p ζ + t * s * bshift S.b p p := by
    simp only [bshift, qf_sub_left, qf_sub_right, qf_smul_left, qf_smul_right, l2_sub_left,
      l2_sub_right, l2_smul_left, l2_smul_right]
    ring
  rw [this, h1, h2]
  rfl

lemma bshift_phi_self_neg {η : Amb N} {u : E4} (hη : η ∈ H (posSign S.Ω (S.fU u)))
    (hb : S.bpp u < 0) (hg : S.gq η u ^ 2 < S.bpp u * bshift S.b η η) :
    bshift S.b (S.phi η u) (S.phi η u) < 0 := by
  rw [S.bshift_phi_phi hη hη, Bf]
  have hb0 := hb.ne
  have : bshift S.b η η - S.gq η u / S.bpp u * S.gq η u - S.gq η u / S.bpp u * S.gq η u +
      S.gq η u / S.bpp u * (S.gq η u / S.bpp u) * S.bpp u =
      bshift S.b η η - S.gq η u ^ 2 / S.bpp u := by
    field_simp
    ring
  rw [this, sub_neg, lt_div_iff_of_neg hb]
  linarith

lemma continuousAt_Bf (η ζ : Amb N) {u : E4} (hb : S.bpp u ≠ 0) :
    ContinuousAt (S.Bf η ζ) u := by
  have hg1 := (S.continuous_gq η).continuousAt (x := u)
  have hg2 := (S.continuous_gq ζ).continuousAt (x := u)
  have hb' := S.continuous_bpp.continuousAt (x := u)
  have ht1 := hg1.div hb' hb
  have ht2 := hg2.div hb' hb
  exact ((continuousAt_const.sub (ht2.mul hg1)).sub (ht1.mul hg2)).add ((ht1.mul ht2).mul hb')

/-! ### The space `W(u)` has negative index one -/

/-- `W(u) = {v ∈ H₀¹(D₊(u)) : 𝔟(v, u₊) = 0}`. -/
def Wsub (u : E4) : Submodule ℝ (Amb N) where
  carrier := {v | v ∈ H (posSign S.Ω (S.fU u)) ∧ bshift S.b v (posPart (S.U u)) = 0}
  add_mem' {x y} hx hy := ⟨Submodule.add_mem _ hx.1 hy.1, by
    simp only [Set.mem_setOf_eq, bshift, qf_add_left, l2_add_left] at hx hy ⊢
    linarith [hx.2, hy.2]⟩
  zero_mem' := ⟨Submodule.zero_mem _, by simp [bshift]⟩
  smul_mem' c x hx := ⟨Submodule.smul_mem _ c hx.1, by
    simp only [Set.mem_setOf_eq, bshift, qf_smul_left, l2_smul_left] at hx ⊢
    have := hx.2
    linear_combination c * this⟩

lemma mem_Wsub {u : E4} {v : Amb N} :
    v ∈ S.Wsub u ↔ v ∈ H (posSign S.Ω (S.fU u)) ∧ bshift S.b v (posPart (S.U u)) = 0 :=
  Iff.rfl

lemma one_le_negIndex_Wsub {u : E4} {φ : Amb N} (hφ : φ ∈ S.Wsub u)
    (hφφ : bshift S.b φ φ < 0) : 1 ≤ negIndex (bshift S.b) (S.Wsub u) := by
  have hφ0 : φ ≠ 0 := by rintro rfl; simp [bshift] at hφφ
  have hle : Submodule.span ℝ {φ} ≤ S.Wsub u := by
    rw [Submodule.span_le, Set.singleton_subset_iff]; exact hφ
  have hfr : Module.finrank ℝ (Submodule.span ℝ {φ}) = 1 :=
    finrank_span_singleton (K := ℝ) hφ0
  have hfinφ : FiniteDimensional ℝ (Submodule.span ℝ {φ}) :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_singleton φ)
  have hneg1 : ∀ x ∈ Submodule.span ℝ {φ}, x ≠ 0 → bshift S.b x x < 0 := by
    intro x hx hx0
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hx
    have ht0 : t ≠ 0 := by
      rintro rfl
      exact hx0 (zero_smul ℝ φ)
    have hexp : bshift S.b (t • φ) (t • φ) = t ^ 2 * bshift S.b φ φ := by
      simp only [bshift, qf_smul_left, qf_smul_right, l2_smul_left, l2_smul_right]
      ring
    rw [hexp]
    exact mul_neg_of_pos_of_neg (pow_pos (abs_pos.mpr ht0) 2 |>.trans_eq (sq_abs t)) hφφ
  have : ((Module.finrank ℝ (Submodule.span ℝ {φ}) : ℕ) : ℕ∞) ≤
      negIndex (bshift S.b) (S.Wsub u) :=
    le_iSup_of_le (Submodule.span ℝ {φ}) (le_iSup_of_le hle (le_iSup_of_le hfinφ
      (le_iSup_of_le hneg1 le_rfl)))
  rw [hfr] at this
  exact this

lemma negIndex_Wsub {u : E4} (hg : S.Good u) {φ : Amb N} (hφ : φ ∈ S.Wsub u)
    (hφφ : bshift S.b φ φ < 0) : negIndex (bshift S.b) (S.Wsub u) = 1 := by
  obtain ⟨-, -, hpb, -, h2, -⟩ := hg
  set pp := posPart (S.U u)
  refine le_antisymm ?_ ?_
  · refine iSup_le fun W => iSup_le fun hW => iSup_le fun hfin => iSup_le fun hneg => ?_
    set L := Submodule.span ℝ {pp}
    have hW' : ∀ y ∈ W, bshift S.b y pp = 0 := fun y hy => (S.mem_Wsub.mp (hW hy)).2
    have hinf : W ⊓ L = ⊥ := by
      rw [eq_bot_iff]
      intro x ⟨hxW, hxL⟩
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hxL
      have := hW' _ hxW
      simp only [bshift, qf_smul_left, l2_smul_left] at this
      have ht : t * bshift S.b pp pp = 0 := by simp only [bshift]; linarith
      rcases mul_eq_zero.mp ht with h | h
      · simp [h]
      · exact absurd h hpb.ne
    have hsupneg : ∀ x ∈ W ⊔ L, x ≠ 0 → bshift S.b x x < 0 := by
      intro x hx hx0
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hz
      have hyp := hW' y hy
      have hexp : bshift S.b (y + t • pp) (y + t • pp) =
          bshift S.b y y + 2 * t * bshift S.b y pp + t ^ 2 * bshift S.b pp pp := by
        simp only [bshift, qf_add_left, qf_add_right, qf_smul_left, qf_smul_right,
          l2_add_left, l2_add_right, l2_smul_left, l2_smul_right, qf_comm pp y, l2_comm pp y]
        ring
      rw [hexp, hyp]
      have htt : t ^ 2 * bshift S.b pp pp ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (sq_nonneg t) hpb.le
      by_cases hy0 : y = 0
      · subst hy0
        have ht0 : t ≠ 0 := by rintro rfl; simp at hx0
        have := mul_neg_of_pos_of_neg (pow_pos (abs_pos.mpr ht0) 2) hpb
        rw [sq_abs] at this
        simp [bshift] at this ⊢
        linarith
      · linarith [hneg y hy hy0]
    have hLle : L ≤ H (posSign S.Ω (S.fU u)) := by
      rw [Submodule.span_le, Set.singleton_subset_iff]
      exact S.posPart_mem_posSign u
    have hWle : W ≤ H (posSign S.Ω (S.fU u)) := fun x hx => (S.mem_Wsub.mp (hW hx)).1
    have hle := finrank_le_negIndex (b := bshift S.b) (sup_le hWle hLle) hsupneg
    rw [h2] at hle
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq W L
    rw [hinf, finrank_bot, add_zero, finrank_span_singleton (fun h => by
      rw [h] at hpb; simp [bshift] at hpb)] at hdim
    rw [hdim] at hle
    have : Module.finrank ℝ W + 1 ≤ 2 := by exact_mod_cast hle
    exact_mod_cast (by omega : Module.finrank ℝ W ≤ 1)
  · exact S.one_le_negIndex_Wsub hφ hφφ

/-! ### Existence of local sections -/

lemma isOpen_gram (b : ℝ) (p : Amb N) :
    IsOpen {η : Amb N | bshift b η p ^ 2 < bshift b p p * bshift b η η} := by
  have c1 : Continuous fun η : Amb N => bshift b η p :=
    (continuous_bshift b).comp (continuous_id.prodMk continuous_const)
  have c2 : Continuous fun η : Amb N => bshift b η η :=
    (continuous_bshift b).comp (continuous_id.prodMk continuous_id)
  exact isOpen_lt (c1.pow 2) (continuous_const.mul c2)

/-- A nonzero vector of a negative plane which is `𝔟`-orthogonal to a given vector. -/
lemma exists_orth_neg {X : Submodule ℝ (Amb N)} (h2 : negIndex (bshift S.b) X = 2)
    (p : Amb N) : ∃ ψ ∈ X, bshift S.b ψ p = 0 ∧ bshift S.b ψ ψ < 0 := by
  obtain ⟨W0, hW0, hfin, hneg, hdim⟩ := exists_of_le_negIndex (k := 2) (b := bshift S.b)
    (X := X) (by rw [h2]; simp)
  let f : W0 →ₗ[ℝ] ℝ :=
    { toFun := fun z => bshift S.b (z : Amb N) p
      map_add' := fun x y => by
        simp only [Submodule.coe_add, bshift, qf_add_left, l2_add_left]; ring
      map_smul' := fun c x => by
        simp only [SetLike.val_smul, bshift, qf_smul_left, l2_smul_left, RingHom.id_apply,
          smul_eq_mul]; ring }
  have hrk := LinearMap.finrank_range_add_finrank_ker f
  have hr : Module.finrank ℝ (LinearMap.range f) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range f)
    simpa using this
  have hker : LinearMap.ker f ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hrk
    omega
  obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hψ0 : (z : Amb N) ≠ 0 := fun h => hz0 (Subtype.ext h)
  exact ⟨z, hW0 z.2, hz, hneg _ z.2 hψ0⟩

/-- **Local negative sections.** Near every good point `u₀` there is a fixed `η` such that
`η ∈ H₀¹(D₊(u))` and the Gram matrix of `(u₊, η)` is negative definite. -/
lemma exists_local_section {u0 : E4} (hg : S.Good u0) :
    ∃ η : Amb N, ∃ V : Set E4, IsOpen V ∧ u0 ∈ V ∧ ∀ u ∈ V,
      η ∈ H (posSign S.Ω (S.fU u)) ∧ S.bpp u < 0 ∧
        S.gq η u ^ 2 < S.bpp u * bshift S.b η η := by
  obtain ⟨-, -, hpb, -, h2, -⟩ := hg
  obtain ⟨ψ, hψH, hψp, hψψ⟩ := S.exists_orth_neg h2 (posPart (S.U u0))
  have hψG : ψ ∈ {η : Amb N | bshift S.b η (posPart (S.U u0)) ^ 2 <
      bshift S.b (posPart (S.U u0)) (posPart (S.U u0)) * bshift S.b η η} := by
    simp only [Set.mem_setOf_eq, hψp]
    nlinarith [mul_pos (neg_pos.mpr hpb) (neg_pos.mpr hψψ)]
  have hcl : ψ ∈ closure (Submodule.span ℝ (testGraph (posSign S.Ω (S.fU u0))) :
      Set (Amb N)) := by
    rw [← Submodule.topologicalClosure_coe]; exact hψH
  obtain ⟨η, hηG, hηs⟩ := mem_closure_iff.mp hcl _ (isOpen_gram S.b _) hψG
  obtain ⟨Kc, hKc, hKcD, hKcs⟩ := span_testGraph_compact hηs
  have hev1 : ∀ᶠ u in 𝓝 u0, η ∈ H (posSign S.Ω (S.fU u)) := by
    filter_upwards [S.eventually_compact_subset_posSign hKc hKcD] with u hu
    exact Submodule.le_topologicalClosure _ (hKcs _ hu)
  have hη0 : η ∈ H (posSign S.Ω (S.fU u0)) := Submodule.le_topologicalClosure _ hηs
  have hev2 : ∀ᶠ u in 𝓝 u0, S.bpp u < 0 :=
    S.continuous_bpp.continuousAt.eventually (gt_mem_nhds hpb)
  have hev3 : ∀ᶠ u in 𝓝 u0, S.gq η u ^ 2 < S.bpp u * bshift S.b η η := by
    refine ContinuousAt.eventually_lt ((S.continuous_gq η).pow 2).continuousAt
      (S.continuous_bpp.mul continuous_const).continuousAt ?_
    rw [← S.bshift_eq_gq hη0]
    exact hηG
  obtain ⟨V, hV, hVo, hu0⟩ := _root_.eventually_nhds_iff.mp (hev1.and (hev2.and hev3))
  exact ⟨η, V, hVo, hu0, fun u hu => ⟨(hV u hu).1, (hV u hu).2.1, (hV u hu).2.2⟩⟩

end Setup

end FourthRatio

end
