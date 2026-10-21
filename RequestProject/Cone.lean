module

public import RequestProject.Defs

/-!
# The negative cone of a form of negative index one (Lemma 5.4 of the paper)

Pure linear algebra.  For a symmetric bilinear form `B` whose restriction to a subspace `X` has
negative index one, the negative cone `{v ∈ X : B(v,v) < 0}` splits into two convex halves
`C₁` and `C₂ = -C₁`; two negative vectors always pair nontrivially, and they lie in the same half
iff their pairing is negative.

(In the paper `X` is a subspace of `H¹` and the two halves are its two connected components; we
formalize the algebraic content, which is what is used in the gluing argument.)
-/

@[expose] public section

noncomputable section

namespace FourthRatio

variable {M : Type*} [AddCommGroup M] [Module ℝ M]

section Cone

variable (B : LinearMap.BilinForm ℝ M) (hB : ∀ v w, B v w = B w v) (X : Submodule ℝ M)

include hB in
/-- Two `B`-orthogonal negative vectors span a negative plane. -/
lemma two_le_negIndex_of_orth {v w : M} (hv : v ∈ X) (hw : w ∈ X) (hvv : B v v < 0)
    (hww : B w w < 0) (hvw : B v w = 0) : 2 ≤ negIndex (fun x y => B x y) X := by
  have hli : LinearIndependent ℝ ![v, w] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 : B (s • v + t • w) v = 0 := by rw [hst]; simp
    have h2 : B (s • v + t • w) w = 0 := by rw [hst]; simp
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hB w v, hvw] at h1 h2
    constructor
    · nlinarith
    · nlinarith
  let W := Submodule.span ℝ (Set.range ![v, w])
  have hW : W ≤ X := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i <;> simpa
  have hfin : Module.finrank ℝ W = 2 := by
    rw [finrank_span_eq_card hli]; simp
  have hneg : ∀ x ∈ W, x ≠ 0 → B x x < 0 := by
    intro x hx hx0
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hx
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] at hx0 ⊢
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hB w v, hvw]
    have : c 0 ≠ 0 ∨ c 1 ≠ 0 := by
      by_contra h
      push_neg at h
      exact hx0 (by simp [h])
    rcases this with h | h
    · have := mul_pos (mul_self_pos.mpr h) (neg_pos.mpr hvv)
      nlinarith [mul_self_nonneg (c 1)]
    · have := mul_pos (mul_self_pos.mpr h) (neg_pos.mpr hww)
      nlinarith [mul_self_nonneg (c 0)]
  have : ((Module.finrank ℝ W : ℕ) : ℕ∞) ≤ negIndex (fun x y => B x y) X :=
    le_iSup_of_le W (le_iSup_of_le hW
      (le_iSup_of_le (FiniteDimensional.span_of_finite ℝ (Set.finite_range _))
        (le_iSup_of_le hneg le_rfl)))
  rw [hfin] at this
  exact_mod_cast this

variable {B X}

include hB in
/-- Negative vectors pair nontrivially. -/
lemma cone_pair_ne_zero (hX : negIndex (fun x y => B x y) X = 1) {v w : M} (hv : v ∈ X)
    (hw : w ∈ X) (hvv : B v v < 0) (hww : B w w < 0) : B v w ≠ 0 := by
  intro h
  have := two_le_negIndex_of_orth B hB X hv hw hvv hww h
  rw [hX] at this
  exact absurd this (by decide)

include hB in
/-- The relation "negative pairing" is transitive on negative vectors. -/
lemma cone_trans (hX : negIndex (fun x y => B x y) X = 1) {u v w : M} (hu : u ∈ X)
    (hv : v ∈ X) (hw : w ∈ X) (huu : B u u < 0) (hvv : B v v < 0) (hww : B w w < 0)
    (huv : B u v < 0) (hvw : B v w < 0) : B u w < 0 := by
  set r := B u v / B w v with hr
  have hwv : B w v < 0 := by rw [hB]; exact hvw
  have hrpos : 0 < r := div_pos_of_neg_of_neg huv hwv
  set y := u - r • w
  have hy : y ∈ X := X.sub_mem hu (X.smul_mem r hw)
  have hyv : B y v = 0 := by
    simp only [y, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [hr, div_mul_cancel₀ _ hwv.ne]; ring
  have hyy : 0 ≤ B y y := by
    by_contra hlt
    push_neg at hlt
    exact cone_pair_ne_zero hB hX hy hv hlt hvv hyv
  simp only [y, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
    hB w u] at hyy
  nlinarith [mul_pos hrpos hrpos]

include hB in
/-- **Lemma 5.4 (Negative cone of index one).** Let `B` be a symmetric bilinear form whose
restriction to `X` has negative index one.  Then the negative cone
`𝒞 = {v ∈ X : B(v,v) < 0}` is the disjoint union of two nonempty convex sets `C₁` and
`C₂ = -C₁`; for `v, w ∈ 𝒞` one has `B(v,w) ≠ 0`, and `v, w` lie in the same half iff
`B(v,w) < 0`. -/
theorem lemma_cone (hX : negIndex (fun x y => B x y) X = 1) :
    ∃ C₁ C₂ : Set M, Convex ℝ C₁ ∧ Convex ℝ C₂ ∧ C₁.Nonempty ∧ C₂.Nonempty ∧
      Disjoint C₁ C₂ ∧ C₁ ∪ C₂ = {v | v ∈ X ∧ B v v < 0} ∧ C₂ = -C₁ ∧
      ∀ v w, v ∈ X → w ∈ X → B v v < 0 → B w w < 0 →
        B v w ≠ 0 ∧ ((v ∈ C₁ ↔ w ∈ C₁) ↔ B v w < 0) := by
  -- a negative vector exists since the index is one
  have hex : ∃ v0 ∈ X, B v0 v0 < 0 := by
    by_contra h
    push_neg at h
    have : negIndex (fun x y => B x y) X = 0 := by
      refine le_antisymm (iSup_le fun W => iSup_le fun hW => iSup_le fun _ => iSup_le
        fun hneg => ?_) bot_le
      have : W = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        by_contra hx0
        exact absurd (h x (hW hx)) (not_le.mpr (hneg x hx hx0))
      subst this
      simp
    rw [hX] at this
    exact absurd this (by decide)
  obtain ⟨v0, hv0X, hv0⟩ := hex
  refine ⟨{v | v ∈ X ∧ B v v < 0 ∧ B v v0 < 0}, {v | v ∈ X ∧ B v v < 0 ∧ 0 < B v v0},
    ?_, ?_, ⟨v0, hv0X, hv0, hv0⟩, ⟨-v0, X.neg_mem hv0X, by simpa using hv0, by simpa using hv0⟩,
    ?_, ?_, ?_, ?_⟩
  · -- convexity of the first half
    intro x ⟨hxX, hxx, hx0⟩ y ⟨hyX, hyy, hy0⟩ s t hs ht hst
    have hxy : B x y < 0 := cone_trans hB hX hxX hv0X hyX hxx hv0 hyy hx0 (by rw [hB]; exact hy0)
    refine ⟨X.add_mem (X.smul_mem s hxX) (X.smul_mem t hyX), ?_, ?_⟩
    · simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        hB y x]
      rcases hs.eq_or_lt with rfl | hs'
      · simp only [zero_add] at hst; subst hst; simpa using hyy
      · nlinarith [mul_pos hs' hs', mul_nonneg hs'.le ht, mul_nonneg ht ht]
    · simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
      rcases hs.eq_or_lt with rfl | hs'
      · simp only [zero_add] at hst; subst hst; simpa using hy0
      · nlinarith
  · -- convexity of the second half
    intro x ⟨hxX, hxx, hx0⟩ y ⟨hyX, hyy, hy0⟩ s t hs ht hst
    have hxy : B x y < 0 := by
      have h2 := cone_trans hB hX hxX (X.neg_mem hv0X) hyX hxx (by simpa using hv0) hyy
        (by simpa using hx0) (by rw [hB]; simpa using hy0)
      exact h2
    refine ⟨X.add_mem (X.smul_mem s hxX) (X.smul_mem t hyX), ?_, ?_⟩
    · simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        hB y x]
      rcases hs.eq_or_lt with rfl | hs'
      · simp only [zero_add] at hst; subst hst; simpa using hyy
      · nlinarith [mul_pos hs' hs', mul_nonneg hs'.le ht, mul_nonneg ht ht]
    · simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
      rcases hs.eq_or_lt with rfl | hs'
      · simp only [zero_add] at hst; subst hst; simpa using hy0
      · nlinarith
  · rw [Set.disjoint_left]
    rintro x ⟨-, -, h1⟩ ⟨-, -, h2⟩
    linarith
  · ext x
    simp only [Set.mem_union, Set.mem_setOf_eq]
    constructor
    · rintro (⟨h1, h2, -⟩ | ⟨h1, h2, -⟩) <;> exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      rcases lt_or_gt_of_ne (cone_pair_ne_zero hB hX h1 hv0X h2 hv0) with h | h
      · exact Or.inl ⟨h1, h2, h⟩
      · exact Or.inr ⟨h1, h2, h⟩
  · ext x
    simp only [Set.mem_setOf_eq, Set.mem_neg, map_neg, LinearMap.neg_apply, neg_neg,
      neg_mem_iff, neg_lt_zero]
  · intro v w hv hw hvv hww
    refine ⟨cone_pair_ne_zero hB hX hv hw hvv hww, ?_⟩
    have hv' := cone_pair_ne_zero hB hX hv hv0X hvv hv0
    have hw' := cone_pair_ne_zero hB hX hw hv0X hww hv0
    simp only [Set.mem_setOf_eq, hv, hvv, hw, hww, true_and]
    constructor
    · intro hiff
      rcases lt_or_gt_of_ne hv' with h1 | h1
      · exact cone_trans hB hX hv hv0X hw hvv hv0 hww h1 (by rw [hB]; exact hiff.mp h1)
      · have h2 : 0 < B w v0 := by
          rcases lt_or_gt_of_ne hw' with h | h
          · exact absurd (hiff.mpr h) (not_lt.mpr h1.le)
          · exact h
        have := cone_trans hB hX (X.neg_mem hv) hv0X (X.neg_mem hw) (by simpa using hvv) hv0
          (by simpa using hww) (by simpa using h1) (by rw [hB]; simpa using h2)
        simpa using this
    · intro hvw
      constructor
      · intro h1
        have := cone_trans hB hX hw hv hv0X hww hvv hv0 (by rw [hB]; exact hvw) h1
        exact this
      · intro h1
        exact cone_trans hB hX hv hw hv0X hvv hww hv0 hvw h1

end Cone

end FourthRatio

end
