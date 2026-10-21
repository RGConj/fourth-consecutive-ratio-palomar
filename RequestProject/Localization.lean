module

public import RequestProject.SobolevLocal

/-!
# Localization lemmas (Section 3 of the paper)

* `lemma_parts` — Sobolev localization of sign truncations (Lemma 3.1).
* `lemma_index` — spectral index of a shifted form (Lemma 3.2).
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Function
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

variable {N : ℕ}

lemma posPart_fst_ae (v : Amb N) :
    ((posPart v).1 : RN N → ℝ) =ᵐ[volume] fun x => max ((v.1 : RN N → ℝ) x) 0 :=
  Lp.coeFn_posPart v.1

lemma posPart_snd_ae (v : Amb N) :
    ((posPart v).2 : RN N → RN N) =ᵐ[volume] (posSetL2 v.1).indicator (v.2 : RN N → RN N) :=
  indL2v_ae _ (measurableSet_posSetL2 v.1) _

lemma negPart_fst_ae (v : Amb N) :
    ((negPart v).1 : RN N → ℝ) =ᵐ[volume] fun x => max (-(v.1 : RN N → ℝ) x) 0 := by
  filter_upwards [posPart_fst_ae (-v), Lp.coeFn_neg v.1] with x h1 h2
  simp only [negPart, h1, Prod.fst_neg, h2, Pi.neg_apply]

/-- Orthogonality part of Lemma 3.1: the sign truncations are orthogonal for both `q` and the
`L²` inner product (this holds for every pair). -/
theorem parts_orthogonal (v : Amb N) :
    qf (posPart v) (negPart v) = 0 ∧ l2 (posPart v) (negPart v) = 0 := by
  constructor
  · rw [qf, L2.inner_def]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [posPart_snd_ae v, posPart_snd_ae (-v), Lp.coeFn_neg v.1] with x h1 h2 h3
    simp only [negPart, h1, h2, Pi.zero_apply, Prod.fst_neg]
    by_cases hx : x ∈ posSetL2 v.1
    · have : x ∉ posSetL2 (-v.1) := by
        simp only [posSetL2, Set.mem_setOf_eq, h3, Pi.neg_apply] at hx ⊢
        linarith
      simp [this]
    · simp [hx]
  · rw [l2, L2.inner_def]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [posPart_fst_ae v, negPart_fst_ae v] with x h1 h2
    simp only [h1, h2, Pi.zero_apply, RCLike.inner_apply, conj_trivial]
    rcases le_total ((v.1 : RN N → ℝ) x) 0 with h | h
    · simp [max_eq_right h]
    · simp [max_eq_right (neg_nonpos.mpr h)]

/-- Membership part of Lemma 3.1 (Sobolev localization of sign truncations): for
`v ∈ H_D ∩ C(D)`, `v₊ ∈ H₀¹(D₊(v))` and `v₋ ∈ H₀¹(D₋(v))`.  (In our model this includes the
Sobolev chain rule `∇v₊ = 1_{v>0} ∇v`.)  The proof follows the paper: the truncations
`w = min{G(v), (f_k)₊}` (with a smooth truncation `G` vanishing near `0` and test functions
`f_k → v`) have compact support in `D₊(v)`, see `RequestProject/SobolevLocal.lean`. -/
theorem parts_mem {D : Set (RN N)} (hD : IsAdmissible D) {v : Amb N}
    (hv : v ∈ H D) {f : RN N → ℝ} (hf : IsContRep D v f) :
    posPart v ∈ H (posSign D f) ∧ negPart v ∈ H (negSign D f) :=
  parts_mem' hD hv hf

/-- **Lemma 3.1 (Sobolev localization of sign truncations).** -/
theorem lemma_parts {D : Set (RN N)} (hD : IsAdmissible D) {v : Amb N}
    (hv : v ∈ H D) {f : RN N → ℝ} (hf : IsContRep D v f) :
    posPart v ∈ H (posSign D f) ∧ negPart v ∈ H (negSign D f) ∧
      qf (posPart v) (negPart v) = 0 ∧ l2 (posPart v) (negPart v) = 0 :=
  ⟨(parts_mem hD hv hf).1, (parts_mem hD hv hf).2, (parts_orthogonal v).1,
    (parts_orthogonal v).2⟩

/-! ### Lemma 3.2: spectral index of a shifted form -/

/-- A complete orthonormal sequence of eigenfunctions (`e j` has eigenvalue `λ_{j+1}(D)`) with
the spectral expansions, as provided by the external spectral package. -/
def IsSpectralBasis (D : Set (RN N)) (e : ℕ → Amb N) : Prop :=
  (∀ j, IsEigenfunction D (e j) (eigenvalue D (j + 1))) ∧
  (∀ i j, l2 (e i) (e j) = if i = j then 1 else 0) ∧
  ∀ v ∈ H D, HasSum (fun j => eigenvalue D (j + 1) * l2 v (e j) ^ 2) (qf v v) ∧
    HasSum (fun j => l2 v (e j) ^ 2) (l2 v v)

lemma exists_spectralBasis (hN : 2 ≤ N) {D : Set (RN N)} (hD : IsAdmissible D) :
    ∃ e, IsSpectralBasis D e := by
  obtain ⟨e, h1, h2, -, -, -, h3⟩ := ext_spectral hN hD
  exact ⟨e, h1, h2, h3⟩

lemma eigenvalue_mono (hN : 2 ≤ N) {D : Set (RN N)} (hD : IsAdmissible D) {i j : ℕ}
    (hi : 1 ≤ i) (hij : i ≤ j) : eigenvalue D i ≤ eigenvalue D j := by
  obtain ⟨-, -, -, -, hmono, -, -⟩ := ext_spectral hN hD
  have := hmono (Nat.sub_le_sub_right hij 1)
  simp only at this
  rwa [Nat.sub_add_cancel hi, Nat.sub_add_cancel (hi.trans hij)] at this

lemma eigenvalue_one_pos (hN : 2 ≤ N) {D : Set (RN N)} (hD : IsAdmissible D) :
    0 < eigenvalue D 1 := by
  obtain ⟨-, -, -, h, -, -, -⟩ := ext_spectral hN hD
  exact h

lemma IsSpectralBasis.hasSum_bshift {D : Set (RN N)} {e : ℕ → Amb N}
    (he : IsSpectralBasis D e) (b : ℝ) {v : Amb N} (hv : v ∈ H D) :
    HasSum (fun j => (eigenvalue D (j + 1) - b) * l2 v (e j) ^ 2) (bshift b v v) := by
  obtain ⟨hq, hl⟩ := he.2.2 v hv
  have := hq.sub (hl.mul_left b)
  convert this using 1
  · ext j; ring
  · rfl

lemma IsSpectralBasis.bshift_nonneg (hN : 2 ≤ N) {D : Set (RN N)} (hD : IsAdmissible D)
    {e : ℕ → Amb N} (he : IsSpectralBasis D e) {k : ℕ} {b : ℝ}
    (hk : b ≤ eigenvalue D (k + 1)) {v : Amb N} (hv : v ∈ H D)
    (h0 : ∀ j < k, l2 v (e j) = 0) : 0 ≤ bshift b v v := by
  refine (he.hasSum_bshift b hv).nonneg fun j => ?_
  by_cases hj : j < k
  · simp [h0 j hj]
  · refine mul_nonneg ?_ (sq_nonneg _)
    have := eigenvalue_mono hN hD (Nat.le_add_left 1 k) (by omega : k + 1 ≤ j + 1)
    linarith

lemma IsSpectralBasis.l2_sum_e {D : Set (RN N)} {e : ℕ → Amb N}
    (he : IsSpectralBasis D e) {k : ℕ} (a : Fin k → ℝ) (j : Fin k) :
    l2 (e j) (∑ i, a i • e i) = a j := by
  rw [l2_sum_right]
  simp only [l2_smul_right, he.2.1, Fin.val_inj, mul_ite, mul_one, mul_zero]
  simp

lemma IsSpectralBasis.linearIndependent {D : Set (RN N)} {e : ℕ → Amb N}
    (he : IsSpectralBasis D e) (k : ℕ) :
    LinearIndependent ℝ (fun i : Fin k => e i) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have := he.l2_sum_e g j
  rw [hg, l2_zero_right] at this
  exact this.symm

lemma IsSpectralBasis.mem_H {D : Set (RN N)} {e : ℕ → Amb N}
    (he : IsSpectralBasis D e) (j : ℕ) : e j ∈ H D := (he.1 j).1

/-- The span of the first `k` eigenfunctions. -/
def eigSpan (e : ℕ → Amb N) (k : ℕ) : Submodule ℝ (Amb N) :=
  Submodule.span ℝ (Set.range fun i : Fin k => e i)

lemma IsSpectralBasis.eigSpan_le {D : Set (RN N)} {e : ℕ → Amb N}
    (he : IsSpectralBasis D e) (k : ℕ) : eigSpan e k ≤ H D := by
  rw [eigSpan, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact he.mem_H i

lemma IsSpectralBasis.finrank_eigSpan {D : Set (RN N)} {e : ℕ → Amb N}
    (he : IsSpectralBasis D e) (k : ℕ) : Module.finrank ℝ (eigSpan e k) = k := by
  rw [eigSpan, finrank_span_eq_card (he.linearIndependent k), Fintype.card_fin]

/-- The shifted form on the span of the first `k` eigenfunctions. -/
lemma IsSpectralBasis.bshift_sum {D : Set (RN N)} {e : ℕ → Amb N}
    (he : IsSpectralBasis D e) {k : ℕ} (a : Fin k → ℝ) (b : ℝ) :
    bshift b (∑ i, a i • e i) (∑ i, a i • e i) =
      ∑ i : Fin k, (eigenvalue D ((i : ℕ) + 1) - b) * a i ^ 2 := by
  have hmem : (∑ i, a i • e i) ∈ H D :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (he.mem_H i)
  simp only [bshift, qf_sum_left, l2_sum_left, qf_smul_left, l2_smul_left]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(he.1 i).2.2 _ hmem, he.l2_sum_e]
  ring

lemma IsSpectralBasis.eigSpan_negative (hN : 2 ≤ N) {D : Set (RN N)} (hD : IsAdmissible D)
    {e : ℕ → Amb N} (he : IsSpectralBasis D e) {k : ℕ} {b : ℝ}
    (hk : eigenvalue D k < b) : ∀ v ∈ eigSpan e k, v ≠ 0 → bshift b v v < 0 := by
  intro v hv hv0
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hv
  rw [he.bshift_sum]
  have hneg : ∀ i : Fin k, eigenvalue D (i + 1) - b < 0 := fun i => by
    have := eigenvalue_mono hN hD (Nat.le_add_left 1 i) (by omega : (i : ℕ) + 1 ≤ k)
    linarith
  have : ∃ i, a i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv0 (by simp [h])
  obtain ⟨i0, hi0⟩ := this
  calc ∑ i : Fin k, (eigenvalue D ((i : ℕ) + 1) - b) * a i ^ 2
        < ∑ _i : Fin k, (0 : ℝ) := by
        refine Finset.sum_lt_sum (fun i _ => ?_) ⟨i0, Finset.mem_univ _, ?_⟩
        · exact mul_nonpos_of_nonpos_of_nonneg (hneg i).le (sq_nonneg _)
        · exact mul_neg_of_neg_of_pos (hneg i0) (by positivity)
    _ = 0 := by simp

/-- **Lemma 3.2 (Spectral index of a shifted form).** If `λ_k(D) < b ≤ λ_{k+1}(D)` then
`ind₋(𝔟_{D,b}) = k`, and the `L²`-projection onto the span of the first `k` eigenfunctions is
injective on every negative subspace for `𝔟_{D,b}` (stated as: a vector of a negative subspace
orthogonal to `e₁,…,e_k` vanishes). -/
theorem lemma_index (hN : 2 ≤ N) {D : Set (RN N)} (hD : IsAdmissible D) {e : ℕ → Amb N}
    (he : IsSpectralBasis D e) {k : ℕ} {b : ℝ} (hk1 : eigenvalue D k < b)
    (hk2 : b ≤ eigenvalue D (k + 1)) :
    negIndex (bshift b) (H D) = k ∧
      ∀ W : Submodule ℝ (Amb N), W ≤ H D → (∀ v ∈ W, v ≠ 0 → bshift b v v < 0) →
        ∀ v ∈ W, (∀ j < k, l2 v (e j) = 0) → v = 0 := by
  have hinj : ∀ W : Submodule ℝ (Amb N), W ≤ H D → (∀ v ∈ W, v ≠ 0 → bshift b v v < 0) →
      ∀ v ∈ W, (∀ j < k, l2 v (e j) = 0) → v = 0 := by
    intro W hW hneg v hv h0
    by_contra hv0
    exact absurd (he.bshift_nonneg hN hD hk2 (hW hv) h0) (not_le.mpr (hneg v hv hv0))
  refine ⟨le_antisymm ?_ ?_, hinj⟩
  · refine iSup_le fun W => iSup_le fun hW => iSup_le fun hfin => iSup_le fun hneg => ?_
    let T : W →ₗ[ℝ] (Fin k → ℝ) :=
      { toFun := fun w j => l2 (w : Amb N) (e j)
        map_add' := fun x y => by ext j; simp
        map_smul' := fun c x => by ext j; simp }
    have hT : Function.Injective T := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro w hw
      have h0 : ∀ j < k, l2 (w : Amb N) (e j) = 0 := fun j hj => congrFun hw ⟨j, hj⟩
      exact Subtype.ext (hinj W hW hneg w w.2 h0)
    have := LinearMap.finrank_le_finrank_of_injective hT
    rw [Module.finrank_fin_fun] at this
    exact_mod_cast this
  · refine le_iSup_of_le (eigSpan e k) (le_iSup_of_le (he.eigSpan_le k)
      (le_iSup_of_le (FiniteDimensional.span_of_finite ℝ (Set.finite_range _)) (le_iSup_of_le (he.eigSpan_negative hN hD hk1) ?_)))
    rw [he.finrank_eigSpan]

end FourthRatio

end
