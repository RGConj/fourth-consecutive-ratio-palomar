module

public import RequestProject.Nodal

/-!
# Eigenvalues of a disjoint union

The eigenvalue-counting clause of the disjoint-union part of the spectral package is derived
here from the spectral package of the pieces and of the union (`ext_spectral`) and the form
domain of a disjoint union (`H_iUnion_of_disjoint`, through `restrictTo_mem_H_piece`):

* *lower bound*: for finitely many pairs `(i, k)` with `λ_k(Dᵢ) ≤ t`, the corresponding
  eigenfunctions of the pieces are `L²`- and `q`-orthogonal elements of `H(⋃ Dᵢ)` spanning a
  subspace on which `q ≤ t ‖·‖²`, so the min–max definition gives enough eigenvalues `≤ t` of the
  union;
* *upper bound*: a nonzero `v ∈ H(⋃ Dᵢ)` that is `L²`-orthogonal to all eigenfunctions of the
  pieces with eigenvalue `≤ t` satisfies `q(v,v) > t ‖v‖²`, because `q(v,v)` and `‖v‖²` are the sums
  of the corresponding quantities of the restrictions `1_{Dᵢ} v ∈ H(Dᵢ)`; a dimension count in the
  span of the first eigenfunctions of the union then bounds the number of its eigenvalues `≤ t`.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Function
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

variable {N : ℕ}

/-- `m ≤ #{j : λ_j(D) ≤ s}` iff `λ_m(D) ≤ s`. -/
lemma le_eigCount_iff (hN : 2 ≤ N) {D : Set (RN N)} (hD : IsAdmissible D) {m : ℕ}
    (hm : 1 ≤ m) (s : ℝ) : (m : ℕ∞) ≤ eigCount D s ↔ eigenvalue D m ≤ s := by
  constructor
  · intro h
    by_contra hlt
    push_neg at hlt
    have hsub : {j : ℕ | 1 ≤ j ∧ eigenvalue D j ≤ s} ⊆ ↑(Finset.Icc 1 (m - 1)) := by
      intro j ⟨hj1, hj⟩
      simp only [Finset.coe_Icc, Set.mem_Icc]
      refine ⟨hj1, ?_⟩
      by_contra hjm
      have := eigenvalue_mono hN hD hm (by omega : m ≤ j)
      linarith
    have := (h.trans (Set.encard_le_encard hsub))
    rw [Set.encard_coe_eq_coe_finsetCard] at this
    simp only [Nat.card_Icc] at this
    have : m ≤ m - 1 + 1 - 1 := by exact_mod_cast this
    omega
  · intro h
    have hsub : (↑(Finset.Icc 1 m) : Set ℕ) ⊆ {j : ℕ | 1 ≤ j ∧ eigenvalue D j ≤ s} := by
      intro j hj
      simp only [Finset.coe_Icc, Set.mem_Icc] at hj
      exact ⟨hj.1, (eigenvalue_mono hN hD hj.1 hj.2).trans h⟩
    have := Set.encard_le_encard hsub
    rw [Set.encard_coe_eq_coe_finsetCard] at this
    simp only [Nat.card_Icc, add_tsub_cancel_right] at this
    exact this

/-! ### Splitting the forms over a disjoint union -/

/-- The `L²` norm square of a function vanishing off a countable disjoint union is the sum of the
`L²` norm squares of its restrictions to the pieces. -/
lemma hasSum_inner_pieces {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Countable ι] {s : ι → Set (RN N)} (hs : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (Disjoint on s)) (f : Lp E 2 (volume : Measure (RN N)))
    (hf : (f : RN N → E) =ᵐ[volume.restrict (⋃ i, s i)ᶜ] 0)
    (r : ι → Lp E 2 (volume : Measure (RN N)))
    (hr : ∀ i, (r i : RN N → E) =ᵐ[volume] (s i).indicator f) :
    HasSum (fun i => ⟪r i, r i⟫) ⟪f, f⟫ := by
  have h1 : ∀ i, ⟪r i, r i⟫ = ∫ x in s i, ⟪f x, f x⟫ := by
    intro i
    rw [L2.inner_def, ← integral_indicator (hs i)]
    refine integral_congr_ae ?_
    filter_upwards [hr i] with x hx
    rw [hx]
    by_cases hxs : x ∈ s i <;> simp [hxs]
  have h2 : ⟪f, f⟫ = ∫ x in ⋃ i, s i, ⟪f x, f x⟫ := by
    rw [L2.inner_def, setIntegral_eq_integral_of_ae_compl_eq_zero]
    rw [EventuallyEq, ae_restrict_iff' (MeasurableSet.iUnion hs).compl] at hf
    filter_upwards [hf] with x hx hxs
    simp [hx hxs]
  simp only [h1, h2]
  exact hasSum_integral_iUnion hs hd (L2.integrable_inner f f).integrableOn

/-- For `v ∈ H(⋃ Dᵢ)` (pairwise disjoint open `Dᵢ`), both forms split over the restrictions. -/
lemma hasSum_forms_pieces {ι : Type*} [Countable ι] (D : ι → Set (RN N))
    (hD : ∀ i, IsOpen (D i)) (hdisj : Pairwise (Disjoint on D)) {v : Amb N}
    (hv : v ∈ H (⋃ i, D i)) :
    HasSum (fun i => qf (restrictTo (D i) v) (restrictTo (D i) v)) (qf v v) ∧
      HasSum (fun i => l2 (restrictTo (D i) v) (restrictTo (D i) v)) (l2 v v) := by
  obtain ⟨h1, h2⟩ := mem_vanishOn.mp (H_le_vanishOn _ hv)
  have hm : ∀ i, MeasurableSet (D i) := fun i => (hD i).measurableSet
  have e : ∀ i, restrictTo (D i) v = (indL2 (D i) (hm i) v.1, indL2v (D i) (hm i) v.2) :=
    fun i => by simp [restrictTo, dif_pos (hm i)]
  constructor
  · simp only [qf, e]
    exact hasSum_inner_pieces hm hdisj v.2 h2 _ (fun i => indL2v_ae _ _ _)
  · simp only [l2, e]
    exact hasSum_inner_pieces hm hdisj v.1 h1 _ (fun i => indL2_ae _ _ _)

/-! ### Lower bound -/

/-- A finite family which is orthonormal for `⟨·,·⟩` and diagonal for `q` with diagonal
entries `≤ t` spans a subspace of dimension the number of vectors on which `q ≤ t ‖·‖²`. -/
lemma span_orth_family {κ : Type*} [Fintype κ] [DecidableEq κ] (f : κ → Amb N) (μ : κ → ℝ) {t : ℝ}
    (hl : ∀ a b, l2 (f a) (f b) = if a = b then 1 else 0)
    (hq : ∀ a b, qf (f a) (f b) = if a = b then μ a else 0) (hμ : ∀ a, μ a ≤ t) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range f)) = Fintype.card κ ∧
      ∀ v ∈ Submodule.span ℝ (Set.range f), qf v v ≤ t * l2 v v := by
  have hl_sum : ∀ (c : κ → ℝ) b, l2 (f b) (∑ a, c a • f a) = c b := by
    intro c b
    rw [l2_sum_right]
    simp only [l2_smul_right, hl, mul_ite, mul_one, mul_zero]
    simp
  have hq_sum : ∀ (c : κ → ℝ) b, qf (f b) (∑ a, c a • f a) = μ b * c b := by
    intro c b
    rw [qf_sum_right]
    simp only [qf_smul_right, hq, mul_ite, mul_zero]
    simp [mul_comm]
  refine ⟨?_, ?_⟩
  · have hli : LinearIndependent ℝ f := by
      rw [Fintype.linearIndependent_iff]
      intro g hg b
      have := hl_sum g b
      rw [hg, l2_zero_right] at this
      exact this.symm
    rw [finrank_span_eq_card hli]
  · intro v hv
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hv
    rw [qf_sum_left, l2_sum_left, Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [qf_smul_left, l2_smul_left, hq_sum, hl_sum]
    nlinarith [hμ a, sq_nonneg (c a)]

/-- An `ℕ∞`-valued bound on the sizes of finite subsets bounds the cardinality. -/
lemma encard_le_of_forall_finset {α : Type*} {P : Set α} {x : ℕ∞}
    (h : ∀ F : Finset α, (F : Set α) ⊆ P → (F.card : ℕ∞) ≤ x) : P.encard ≤ x := by
  classical
  rcases P.finite_or_infinite with hP | hP
  · rw [hP.encard_eq_coe_toFinset_card]
    exact h _ (by simp)
  · have : x = ⊤ := by
      refine ENat.eq_top_iff_forall_ge.mpr fun n => ?_
      obtain ⟨F, hFP, hFn⟩ := hP.exists_subset_card_eq n
      rw [← hFn]; exact h F hFP
    simp [this]

/-! ### Upper bound -/

/-- A nonzero element of `H(⋃ Dᵢ)` that is orthogonal to all eigenfunctions of the pieces with
eigenvalue `≤ t` has Rayleigh quotient `> t`. -/
lemma lt_qf_of_orth {ι : Type*} [Countable ι] (D : ι → Set (RN N))
    (hD : ∀ i, IsOpen (D i)) (hdisj : Pairwise (Disjoint on D))
    (e : ι → ℕ → Amb N) (he : ∀ i, IsSpectralBasis (D i) (e i))
    {t : ℝ} {v : Amb N} (hv : v ∈ H (⋃ i, D i)) (hv0 : v ≠ 0)
    (horth : ∀ i j, eigenvalue (D i) (j + 1) ≤ t → l2 v (e i j) = 0) :
    t * l2 v v < qf v v := by
  classical
  set w : ι → Amb N := fun i => restrictTo (D i) v with hw
  have hwH : ∀ i, w i ∈ H (D i) := fun i => restrictTo_mem_H_piece D hD hdisj i hv
  obtain ⟨hqs, hls⟩ := hasSum_forms_pieces D hD hdisj hv
  have hcoef : ∀ i j, l2 (w i) (e i j) = l2 v (e i j) := fun i j =>
    (forms_eq_of_agree (hD i).measurableSet (H_le_vanishOn _ ((he i).mem_H j))
      (restrictTo_agree (hD i).measurableSet v).1 (restrictTo_agree (hD i).measurableSet v).2).2
  have hbs : HasSum (fun i => bshift t (w i) (w i)) (bshift t v v) := by
    simpa [bshift] using hqs.sub (hls.mul_left t)
  have hterm : ∀ i j, 0 ≤ (eigenvalue (D i) (j + 1) - t) * l2 (w i) (e i j) ^ 2 := by
    intro i j
    by_cases hj : eigenvalue (D i) (j + 1) ≤ t
    · simp [hcoef, horth i j hj]
    · exact mul_nonneg (by linarith [not_le.mp hj]) (sq_nonneg _)
  have hnonneg : ∀ i, 0 ≤ bshift t (w i) (w i) := fun i =>
    ((he i).hasSum_bshift t (hwH i)).nonneg fun j => hterm i j
  obtain ⟨i0, hi0⟩ : ∃ i, w i ≠ 0 := by
    by_contra h
    push_neg at h
    apply hv0
    apply eq_zero_of_l2_self_eq_zero hv
    have h' : ∀ i, restrictTo (D i) v = 0 := h
    refine hls.unique ?_
    simp only [h', l2_zero_left]
    exact hasSum_zero
  have hpos : 0 < bshift t (w i0) (w i0) := by
    obtain ⟨j, hj⟩ : ∃ j, l2 (w i0) (e i0 j) ≠ 0 := by
      by_contra h
      push_neg at h
      apply hi0
      apply eq_zero_of_l2_self_eq_zero (hwH i0)
      refine ((he i0).2.2 _ (hwH i0)).2.unique ?_
      simp only [h]
      simp
    have hgt : t < eigenvalue (D i0) (j + 1) := by
      by_contra hle
      push_neg at hle
      exact hj (by rw [hcoef]; exact horth _ _ hle)
    refine hasSum_lt (f := fun _ => (0 : ℝ)) (i := j) (fun k => hterm i0 k) ?_ hasSum_zero
      ((he i0).hasSum_bshift t (hwH i0))
    exact mul_pos (by linarith) (by positivity)
  have : 0 < bshift t v v :=
    hasSum_lt (f := fun _ => (0 : ℝ)) (i := i0) (fun i => hnonneg i) hpos hasSum_zero hbs
  rw [bshift] at this
  linarith

/-! ### The counting identity -/

/-- **Spectral package, disjoint unions: eigenvalues.** For pairwise disjoint nonempty open sets
the eigenvalues of the union are the combined multiset of the eigenvalues of the pieces
(expressed through the counting functions). -/
theorem eigCount_iUnion (hN : 2 ≤ N) {ι : Type} [Countable ι] (D : ι → Set (RN N))
    (hD : ∀ i, IsOpen (D i)) (hne : ∀ i, (D i).Nonempty) (hdisj : Pairwise (Disjoint on D))
    (hU : IsAdmissible (⋃ i, D i)) :
    ∀ t : ℝ, eigCount (⋃ i, D i) t =
      {p : ι × ℕ | 1 ≤ p.2 ∧ eigenvalue (D p.1) p.2 ≤ t}.encard := by
  intro t
  classical
  have hDa : ∀ i, IsAdmissible (D i) := fun i =>
    ⟨hD i, hne i, hU.2.2.subset (Set.subset_iUnion D i)⟩
  choose e he using fun i => exists_spectralBasis hN (hDa i)
  set P := {p : ι × ℕ | 1 ≤ p.2 ∧ eigenvalue (D p.1) p.2 ≤ t} with hP
  apply le_antisymm
  · by_contra hlt
    push_neg at hlt
    have hPfin : P.Finite := Set.encard_ne_top_iff.mp (hlt.trans_le le_top).ne
    set n := hPfin.toFinset.card with hn
    have hPn : P.encard = n := hPfin.encard_eq_coe_toFinset_card
    rw [hPn] at hlt
    have hle : ((n + 1 : ℕ) : ℕ∞) ≤ eigCount (⋃ i, D i) t := by
      push_cast; exact Order.add_one_le_of_lt hlt
    have hlam := (le_eigCount_iff hN hU (by omega) t).mp hle
    obtain ⟨E, hE⟩ := exists_spectralBasis hN hU
    set V := eigSpan E (n + 1)
    have hVq : ∀ v ∈ V, qf v v ≤ t * l2 v v := by
      intro v hv
      obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hv
      have h := hE.bshift_sum a t
      have : ∑ i : Fin (n + 1), (eigenvalue (⋃ i, D i) ((i : ℕ) + 1) - t) * a i ^ 2 ≤ 0 := by
        refine Finset.sum_nonpos fun i _ => mul_nonpos_of_nonpos_of_nonneg ?_ (sq_nonneg _)
        have := eigenvalue_mono hN hU (Nat.le_add_left 1 i) (by omega : (i : ℕ) + 1 ≤ n + 1)
        linarith
      rw [bshift] at h
      linarith
    let T : V →ₗ[ℝ] (hPfin.toFinset → ℝ) :=
      { toFun := fun w p => l2 (w : Amb N) (e p.1.1 (p.1.2 - 1))
        map_add' := fun x y => by ext p; simp
        map_smul' := fun c x => by ext p; simp }
    have hnotinj : ¬ Function.Injective T := by
      intro hT
      have := LinearMap.finrank_le_finrank_of_injective hT
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe, hE.finrank_eigSpan] at this
      omega
    obtain ⟨w, hw, hw0⟩ : ∃ w : V, T w = 0 ∧ w ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      apply hnotinj
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      exact hcon
    have hwH : (w : Amb N) ∈ H (⋃ i, D i) := hE.eigSpan_le _ w.2
    have hw0' : (w : Amb N) ≠ 0 := fun h => hw0 (Subtype.ext h)
    have hlt' := lt_qf_of_orth D hD hdisj e he hwH hw0' (t := t) (by
      intro i j hij
      have hmem : (i, j + 1) ∈ hPfin.toFinset := by
        rw [Set.Finite.mem_toFinset]; exact ⟨by omega, hij⟩
      have := congrFun hw ⟨(i, j + 1), hmem⟩
      simpa [T] using this)
    exact absurd (hVq w w.2) (not_le.mpr hlt')
  · apply encard_le_of_forall_finset
    intro F hF
    rcases F.eq_empty_or_nonempty with rfl | hFne
    · simp
    have hF1 : ∀ p ∈ F, 1 ≤ p.2 := fun p hp => (hF hp).1
    let f : F → Amb N := fun p => e p.1.1 (p.1.2 - 1)
    let μ : F → ℝ := fun p => eigenvalue (D p.1.1) p.1.2
    have hl : ∀ a b, l2 (f a) (f b) = if a = b then 1 else 0 := by
      intro a b
      by_cases hab : a.1.1 = b.1.1
      · have h := (he a.1.1).2.1 (a.1.2 - 1) (b.1.2 - 1)
        have ha := hF1 a.1 a.2
        have hb := hF1 b.1 b.2
        simp only [f]
        rw [show e b.1.1 = e a.1.1 by rw [hab], h]
        by_cases h2 : a.1.2 = b.1.2
        · have : a = b := Subtype.ext (Prod.ext hab h2)
          simp [this]
        · have h3 : a.1.2 - 1 ≠ b.1.2 - 1 := by omega
          have : a ≠ b := fun h => h2 (by rw [h])
          simp [h3, this]
      · have : a ≠ b := fun h => hab (by rw [h])
        rw [if_neg this]
        exact (orthogonal_of_disjoint (hD _).measurableSet (hD _).measurableSet (hdisj hab)
          ((he a.1.1).mem_H _) ((he b.1.1).mem_H _)).2
    have hq : ∀ a b, qf (f a) (f b) = if a = b then μ a else 0 := by
      intro a b
      by_cases hab : a.1.1 = b.1.1
      · have hb : f b ∈ H (D a.1.1) := by
          simp only [f]; rw [← hab]; exact (he a.1.1).mem_H _
        rw [((he a.1.1).1 (a.1.2 - 1)).2.2 _ hb, hl, Nat.sub_add_cancel (hF1 a.1 a.2)]
        split_ifs <;> simp [μ]
      · have : a ≠ b := fun h => hab (by rw [h])
        rw [if_neg this]
        exact (orthogonal_of_disjoint (hD _).measurableSet (hD _).measurableSet (hdisj hab)
          ((he a.1.1).mem_H _) ((he b.1.1).mem_H _)).1
    obtain ⟨hdim, hVq⟩ := span_orth_family f μ hl hq (fun a => (hF a.2).2)
    rw [Fintype.card_coe] at hdim
    obtain ⟨p0, hp0⟩ := hFne
    have ht : 0 ≤ t := (eigenvalue_nonneg _ _).trans (hF hp0).2
    have hVH : Submodule.span ℝ (Set.range f) ≤ H (⋃ i, D i) := by
      rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      exact H_mono (Set.subset_iUnion D a.1.1) ((he a.1.1).mem_H _)
    have hlam := eigenvalue_le_of_subspace hVH hdim ht hVq
    exact (le_eigCount_iff hN hU (Finset.card_pos.mpr ⟨p0, hp0⟩) t).mpr hlam

/-- **Spectral package, disjoint unions** (full statement of the paper): for pairwise disjoint
nonempty open sets the form domain of the union is the orthogonal sum of the form domains, and
the eigenvalues of the union are the combined multiset of the eigenvalues of the pieces. -/
theorem disjoint_union (hN : 2 ≤ N) {ι : Type} [Countable ι] (D : ι → Set (RN N))
    (hD : ∀ i, IsOpen (D i)) (hne : ∀ i, (D i).Nonempty) (hdisj : Pairwise (Disjoint on D))
    (hU : IsAdmissible (⋃ i, D i)) :
    H (⋃ i, D i) = (⨆ i, H (D i)).topologicalClosure ∧
    ∀ t : ℝ, eigCount (⋃ i, D i) t =
      {p : ι × ℕ | 1 ≤ p.2 ∧ eigenvalue (D p.1) p.2 ≤ t}.encard :=
  ⟨H_iUnion_of_disjoint D hD hdisj, eigCount_iUnion hN D hD hne hdisj hU⟩

end FourthRatio

end
