module

public import RequestProject.BallSteps
public import RequestProject.Localization
public import RequestProject.Derived

/-!
# The spectral conclusion of the ball–annulus lemma

`ball_annulus_spectral`: if two disjoint pieces `A`, `B` of a domain `Ω` (with `H_A, H_B ⊆ H_Ω`,
`A ∩ Ω ≠ ∅`) carry subspaces `V_A ⊆ H_A`, `V_B ⊆ H_B` of total dimension `k + 1` with
`q ≤ t_A ‖·‖²` on `V_A` and `q ≤ t ‖·‖²` on `V_B`, where `t_A < t`, then `λ_{k+1}(Ω) < t`.
(If `t ≤ λ_{k+1}(Ω)`, a vector of `V_A ⊕ V_B` orthogonal to `e₁,…,e_k` is forced to lie in `V_B`
and to be an eigenfunction of `Ω` vanishing on `A ∩ Ω`, contradicting unique continuation.)
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Function
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

variable {N : ℕ}

/-- The finite-codimension subspace `{φ ∈ H_D : ⟨φ, e_j⟩ = 0, j < k}`. -/
def perpSub (D : Set (RN N)) (e : ℕ → Amb N) (k : ℕ) : Submodule ℝ (Amb N) where
  carrier := {φ | φ ∈ H D ∧ ∀ j < k, l2 φ (e j) = 0}
  zero_mem' := ⟨(H D).zero_mem, fun j _ => by simp⟩
  add_mem' := fun ha hb => ⟨(H D).add_mem ha.1 hb.1, fun j hj => by
    simp [ha.2 j hj, hb.2 j hj]⟩
  smul_mem' := fun c x hx => ⟨(H D).smul_mem c hx.1, fun j hj => by simp [hx.2 j hj]⟩

/-- The coordinate map `v ↦ (⟨v, e_j⟩)_{j < k}`. -/
def coordMap (e : ℕ → Amb N) (k : ℕ) (V : Submodule ℝ (Amb N)) : V →ₗ[ℝ] (Fin k → ℝ) where
  toFun v := fun j => l2 (v : Amb N) (e j)
  map_add' v w := by funext j; simp
  map_smul' c v := by funext j; simp

lemma exists_ne_zero_coordMap_eq_zero (e : ℕ → Amb N) (k : ℕ) (V : Submodule ℝ (Amb N))
    [FiniteDimensional ℝ V] (hV : k < Module.finrank ℝ V) :
    ∃ v : V, v ≠ 0 ∧ coordMap e k V v = 0 := by
  have : LinearMap.ker (coordMap e k V) ≠ ⊥ := by
    intro hk
    have := LinearMap.finrank_le_finrank_of_injective (LinearMap.ker_eq_bot.mp hk)
    simp at this
    omega
  obtain ⟨v, hv, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot this
  exact ⟨v, h0, hv⟩

/-- A vector orthogonal to `e_0, …, e_{k-1}` with vanishing shifted form, where
`b ≤ λ_{k+1}(D)`, is an eigenfunction with eigenvalue `b` (if nonzero). -/
lemma eigen_of_perp_bshift_zero (hN : 2 ≤ N) {D : Set (RN N)} (hD : IsAdmissible D)
    {e : ℕ → Amb N} (he : IsSpectralBasis D e) {k : ℕ} {b : ℝ}
    (hk : b ≤ eigenvalue D (k + 1)) {v : Amb N} (hv : v ∈ H D) (hv0 : v ≠ 0)
    (hperp : ∀ j < k, l2 v (e j) = 0) (h0 : bshift b v v = 0) : IsEigenfunction D v b := by
  have hvW : v ∈ perpSub D e k := ⟨hv, hperp⟩
  have hpos : ∀ w ∈ perpSub D e k, 0 ≤ bshift b w w := fun w hw =>
    he.bshift_nonneg hN hD hk hw.1 hw.2
  have hW := bshift_eq_zero_of_min hpos hvW h0
  refine ⟨hv, hv0, fun φ hφ => ?_⟩
  set s : Amb N := ∑ i : Fin k, l2 φ (e i) • e i with hs
  have hsW : φ - s ∈ perpSub D e k := by
    refine ⟨(H D).sub_mem hφ (Submodule.sum_mem _ fun i _ => (H D).smul_mem _ (he.mem_H i)),
      fun j hj => ?_⟩
    have := he.l2_sum_e (fun i : Fin k => l2 φ (e i)) ⟨j, hj⟩
    simp only at this
    rw [l2_sub_left, l2_comm s, hs, this]
    ring
  have h1 := hW _ hsW
  have h2 : bshift b v s = 0 := by
    simp only [hs, bshift, qf_sum_right, l2_sum_right, qf_smul_right, l2_smul_right]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hq := (he.1 i).2.2 v hv
    rw [qf_comm, hq, l2_comm (e i) v, hperp i i.2]
    ring
  simp only [bshift, qf_sub_right, l2_sub_right] at h1 h2
  linarith

/-- **Spectral conclusion of the ball–annulus lemma.** -/
theorem ball_annulus_spectral (hN : 2 ≤ N) {Ω A B : Set (RN N)} (hΩ : IsDomain Ω)
    (hA : IsAdmissible A) (hB : IsAdmissible B) (hAB : Disjoint A B)
    (hAΩ : H A ≤ H Ω) (hBΩ : H B ≤ H Ω) (hAne : (A ∩ Ω).Nonempty)
    {t tA : ℝ} (htA : tA < t) {k : ℕ} {VA VB : Submodule ℝ (Amb N)}
    [FiniteDimensional ℝ VA] [FiniteDimensional ℝ VB]
    (hVA : VA ≤ H A) (hVB : VB ≤ H B)
    (hdim : Module.finrank ℝ VA + Module.finrank ℝ VB = k + 1)
    (hqA : ∀ v ∈ VA, qf v v ≤ tA * l2 v v) (hqB : ∀ v ∈ VB, qf v v ≤ t * l2 v v) :
    eigenvalue Ω (k + 1) < t := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨e, he⟩ := exists_spectralBasis hN hΩ.1
  have hAm := hA.1.measurableSet
  have hBm := hB.1.measurableSet
  have horth : ∀ v ∈ VA, ∀ w ∈ VB, qf v w = 0 ∧ l2 v w = 0 := fun v hv w hw =>
    orthogonal_of_disjoint hAm hBm hAB (hVA hv) (hVB hw)
  have hinf : VA ⊓ VB = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_bot]
    exact eq_zero_of_l2_self_eq_zero (hVA hv.1) (horth v hv.1 v hv.2).2
  have hfin : Module.finrank ℝ (VA ⊔ VB : Submodule ℝ (Amb N)) = k + 1 := by
    have := Submodule.finrank_sup_add_finrank_inf_eq VA VB
    rw [hinf, finrank_bot] at this
    omega
  obtain ⟨⟨v, hvV⟩, hv0, hker⟩ :=
    exists_ne_zero_coordMap_eq_zero e k (VA ⊔ VB) (by rw [hfin]; omega)
  have hv0' : v ≠ 0 := fun h => hv0 (Subtype.ext h)
  have hperp : ∀ j < k, l2 v (e j) = 0 := fun j hj => congrFun hker ⟨j, hj⟩
  obtain ⟨vA, hvA, vB, hvB, rfl⟩ := Submodule.mem_sup.mp hvV
  have hvH : vA + vB ∈ H Ω := (H Ω).add_mem (hAΩ (hVA hvA)) (hBΩ (hVB hvB))
  have hnn := he.bshift_nonneg hN hΩ.1 hcon hvH hperp
  obtain ⟨hq1, hl1⟩ := horth vA hvA vB hvB
  have hsplit : bshift t (vA + vB) (vA + vB) = bshift t vA vA + bshift t vB vB := by
    simp only [bshift, qf_add_left, qf_add_right, l2_add_left, l2_add_right]
    rw [qf_comm vB vA, l2_comm vB vA, hq1, hl1]
    ring
  have hA1 := hqA vA hvA
  have hB1 := hqB vB hvB
  have hlA := l2_self_nonneg vA
  have hlA0 : l2 vA vA = 0 := by
    rw [hsplit] at hnn
    simp only [bshift] at hnn
    nlinarith
  have hvA0 : vA = 0 := eq_zero_of_l2_self_eq_zero (hVA hvA) hlA0
  subst hvA0
  rw [zero_add] at hv0' hvH hperp hnn
  have hb0 : bshift t vB vB = 0 := le_antisymm (by simp only [bshift]; linarith) (by
    simpa using hnn)
  have heig := eigen_of_perp_bshift_zero hN hΩ.1 he hcon hvH hv0' hperp hb0
  refine ucp_nonvanishing hΩ heig (hA.1.inter hΩ.1.1) hAne Set.inter_subset_right ?_
  have h1 := (mem_vanishOn.mp (H_le_vanishOn B (hVB hvB))).1
  refine ae_restrict_of_ae_restrict_of_subset ?_ h1
  intro x hx hxB
  exact Set.disjoint_left.mp hAB hx.1 hxB

/-- The ball subspace `span{φ_B} ⊕ E₂(B)`: dimension `N + 1` and `q ≤ C a ‖·‖²` on it. -/
lemma ball_subspace (hN : 2 ≤ N) {B : Set (RN N)} {a C : ℝ} (ha : 0 < a)
    (hC : 1 < C) {φB : Amb N} (hφ : IsEigenfunction B φB a) {V2 : Submodule ℝ (Amb N)}
    (hV2dim : Module.finrank ℝ V2 = N)
    (hV2 : ∀ u ∈ V2, u ∈ H B ∧ ∀ φ ∈ H B, qf u φ = C * a * l2 u φ) :
    ∃ V : Submodule ℝ (Amb N), FiniteDimensional ℝ V ∧ V ≤ H B ∧
      Module.finrank ℝ V = N + 1 ∧ ∀ v ∈ V, qf v v ≤ C * a * l2 v v := by
  haveI : FiniteDimensional ℝ V2 := FiniteDimensional.of_finrank_pos (by omega)
  have hS : ∀ v1 ∈ Submodule.span ℝ {φB}, v1 ∈ H B ∧ ∀ x ∈ H B, qf v1 x = a * l2 v1 x := by
    intro v1 hv1
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hv1
    refine ⟨(H B).smul_mem s hφ.1, fun x hx => ?_⟩
    rw [qf_smul_left, l2_smul_left, hφ.2.2 x hx]
    ring
  have hcross : ∀ v1 ∈ Submodule.span ℝ {φB}, ∀ w ∈ V2, qf v1 w = 0 ∧ l2 v1 w = 0 := by
    intro v1 hv1 w hw
    obtain ⟨hv1H, hv1q⟩ := hS v1 hv1
    obtain ⟨hwH, hwq⟩ := hV2 w hw
    have e1 := hv1q w hwH
    have e2 := hwq v1 hv1H
    rw [qf_comm, l2_comm] at e2
    have hl : l2 v1 w = 0 := by
      have : (C - 1) * a * l2 v1 w = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · rcases mul_eq_zero.mp h with h | h
        · linarith
        · linarith
      · exact h
    exact ⟨by rw [e1, hl, mul_zero], hl⟩
  have hinf : Submodule.span ℝ {φB} ⊓ V2 = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_bot]
    have := hcross v hv.1 v hv.2
    exact eq_zero_of_l2_self_eq_zero (hS v hv.1).1 this.2
  have hφ0 : φB ≠ 0 := hφ.2.1
  refine ⟨Submodule.span ℝ {φB} ⊔ V2, inferInstance, sup_le ?_ ?_, ?_, ?_⟩
  · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hφ.1)
  · exact fun w hw => (hV2 w hw).1
  · have := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span ℝ {φB}) V2
    rw [hinf, finrank_bot, finrank_span_singleton hφ0, hV2dim] at this
    omega
  · intro v hv
    obtain ⟨v1, hv1, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
    obtain ⟨hq, hl⟩ := hcross v1 hv1 w hw
    obtain ⟨hv1H, hv1q⟩ := hS v1 hv1
    obtain ⟨hwH, hwq⟩ := hV2 w hw
    have e1 := hv1q v1 hv1H
    have e2 := hwq w hwH
    have hl1 := l2_self_nonneg v1
    simp only [qf_add_left, qf_add_right, l2_add_left, l2_add_right]
    rw [qf_comm w v1, l2_comm w v1, hq, hl, e1, e2]
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ C - 1) ha.le) hl1]

/-- The annulus Rayleigh bound `a + d J_A / K_A` is strictly below `C a`, by the radial integral
inequality on the annulus and the gap `d / R² < C a - a` (which comes from the Bessel zero
inequality `besselZero_sq_gap`). -/
lemma annulus_bound_lt {a C R R' d : ℝ} (hR : 0 < R) (hRR : R < R') (hd : 0 < d)
    {ρ : ℝ → ℝ} (hρ : ContinuousOn ρ (Set.Icc R R')) (hρ0 : ∀ r ∈ Set.Ioo R R', ρ r ≠ 0)
    (hgap : d / R ^ 2 < C * a - a) :
    a + d * (∫ r in R..R', ρ r ^ 2 * r ^ (d - 2)) / (∫ r in R..R', ρ r ^ 2 * r ^ d) < C * a := by
  obtain ⟨hK, hJK⟩ := annulus_integral_ineq (d := d) hR hRR hρ hρ0
  set K := ∫ r in R..R', ρ r ^ 2 * r ^ d
  set J := ∫ r in R..R', ρ r ^ 2 * r ^ (d - 2)
  have hR2 : 0 < R ^ 2 := by positivity
  have hA : d * J / K < d / R ^ 2 := by
    rw [div_lt_div_iff₀ hK hR2]
    nlinarith
  rw [mul_div_assoc] at hA ⊢
  linarith

end FourthRatio

end
