module

public import RequestProject.GroundState

/-!
# Further elementary facts on truncations and positivity
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Function
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

variable {N : ℕ}

/-- On a domain the first eigenvalue is simple, hence `λ₁ < λ₂`. -/
lemma lam1_lt_lam2 (hN : 2 ≤ N) {D : Set (RN N)} (hD : IsDomain D) {e : ℕ → Amb N}
    (he : IsSpectralBasis D e) : eigenvalue D 1 < eigenvalue D 2 := by
  rcases (eigenvalue_mono hN hD.1 le_rfl (by norm_num : 1 ≤ 2)).lt_or_eq with h | h
  · exact h
  · exfalso
    obtain ⟨hsimp, -⟩ := ground_state hN hD
    have h0 : IsEigenfunction D (e 0) (eigenvalue D 1) := by simpa using he.1 0
    have h1 : IsEigenfunction D (e 1) (eigenvalue D 1) := by
      have := he.1 1
      rwa [show (1 : ℕ) + 1 = 2 from rfl, ← h] at this
    obtain ⟨c, hc⟩ := hsimp (e 0) (e 1) h0 h1
    have h10 := he.2.1 1 0
    have h00 := he.2.1 0 0
    rw [hc, l2_smul_left, h00] at h10
    simp only [if_true, mul_one, one_ne_zero, if_false] at h10
    exact h1.2.1 (by rw [hc, h10, zero_smul])

/-- Two continuous representatives on an open set agree there. -/
lemma eqOn_of_contRep {D : Set (RN N)} (hD : IsOpen D) {v : Amb N} {f g : RN N → ℝ}
    (hf : IsContRep D v f) (hg : IsContRep D v g) : Set.EqOn f g D :=
  Measure.eqOn_of_ae_eq (hf.2.symm.trans hg.2) hf.1 hg.1
    (by rw [hD.interior_eq]; exact subset_closure)

lemma connectedComponentIn_disjoint_of_ne {D : Set (RN N)} {x y : RN N}
    (h : connectedComponentIn D x ≠ connectedComponentIn D y) :
    Disjoint (connectedComponentIn D x) (connectedComponentIn D y) := by
  rw [Set.disjoint_left]
  intro z hzx hzy
  exact h ((connectedComponentIn_eq hzx).trans (connectedComponentIn_eq hzy).symm)

lemma eq_connectedComponentIn_of_forall {D : Set (RN N)} {x0 : RN N}
    (h : ∀ y ∈ D, connectedComponentIn D y = connectedComponentIn D x0) :
    connectedComponentIn D x0 = D := by
  refine Set.Subset.antisymm (connectedComponentIn_subset D x0) fun y hy => ?_
  rw [← h y hy]
  exact mem_connectedComponentIn hy

lemma isDomain_ball (y : RN N) {R : ℝ} (hR : 0 < R) : IsDomain (ball y R) :=
  ⟨⟨isOpen_ball, nonempty_ball.mpr hR, isBounded_ball⟩,
    (convex_ball y R).isConnected (nonempty_ball.mpr hR)⟩

/-- Two disjoint open pieces carrying functions with Rayleigh quotient `t` give `λ₂ ≤ t`. -/
lemma eigenvalue_two_le_of_disjoint {D C₁ C₂ : Set (RN N)}
    (h₁ : IsOpen C₁) (h₂ : IsOpen C₂) (h₁D : C₁ ⊆ D) (h₂D : C₂ ⊆ D) (hd : Disjoint C₁ C₂)
    {w₁ w₂ : Amb N} (hw₁ : w₁ ∈ H C₁) (hw₂ : w₂ ∈ H C₂) (hw₁0 : w₁ ≠ 0) (hw₂0 : w₂ ≠ 0)
    {t : ℝ} (ht : 0 ≤ t) (hq₁ : qf w₁ w₁ = t * l2 w₁ w₁) (hq₂ : qf w₂ w₂ = t * l2 w₂ w₂) :
    eigenvalue D 2 ≤ t := by
  obtain ⟨hq12, hl12⟩ := orthogonal_of_disjoint h₁.measurableSet h₂.measurableSet hd hw₁ hw₂
  have hw₁D := H_mono h₁D hw₁
  have hw₂D := H_mono h₂D hw₂
  have hp₁ := l2_self_pos hw₁D hw₁0
  have hp₂ := l2_self_pos hw₂D hw₂0
  have hli : LinearIndependent ℝ ![w₁, w₂] := by
    rw [LinearIndependent.pair_iff]
    intro s r hsr
    have e1 : l2 (s • w₁ + r • w₂) w₁ = 0 := by rw [hsr, l2_zero_left]
    have e2 : l2 (s • w₁ + r • w₂) w₂ = 0 := by rw [hsr, l2_zero_left]
    simp only [l2_add_left, l2_smul_left, l2_comm w₂ w₁, hl12] at e1 e2
    constructor
    · nlinarith
    · nlinarith
  refine eigenvalue_le_of_subspace (V := Submodule.span ℝ (Set.range ![w₁, w₂])) ?_ ?_ ht ?_
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hw₁D
    · exact hw₂D
  · rw [finrank_span_eq_card hli]; simp
  · intro v hv
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hv
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, qf_add_left, qf_add_right, qf_smul_left, qf_smul_right,
      l2_add_left, l2_add_right, l2_smul_left, l2_smul_right, qf_comm w₂ w₁, l2_comm w₂ w₁,
      hq12, hl12, hq₁, hq₂]
    nlinarith [le_refl (0:ℝ)]

/-- The restriction of `v₊` to a subset `G` of the positive set agrees a.e. with the zero
extension of `v|_G`. -/
lemma indicator_eq_restrictTo_posPart {D G : Set (RN N)} (hDm : MeasurableSet D)
    (hGm : MeasurableSet G) {v : Amb N} {f : RN N → ℝ} (hf : IsContRep D v f)
    (hG : G ⊆ posSign D f) :
    G.indicator (v.1 : RN N → ℝ) =ᵐ[volume] ((restrictTo G (posPart v)).1 : RN N → ℝ) := by
  have hf2 := hf.2
  rw [EventuallyEq, ae_restrict_iff' hDm] at hf2
  simp only [restrictTo, dif_pos hGm]
  filter_upwards [indL2_ae G hGm (posPart v).1, posPart_fst_ae v, hf2] with x h1 h2 h3
  rw [h1]
  by_cases hx : x ∈ G
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, h2]
    have hxD := (hG hx).1
    have hpos : 0 < f x := (hG hx).2
    rw [h3 hxD, max_eq_left hpos.le]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]

end FourthRatio

end
