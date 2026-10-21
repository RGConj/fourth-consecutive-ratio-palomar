module

public import RequestProject.MainBasic
public import RequestProject.Nodal
public import RequestProject.CompCount

/-!
# Strictness on both sign sets (Lemma 5.1)
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Function
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

variable {N : ℕ}

namespace Setup

variable (S : Setup N)

lemma Qa_term_nonpos (c : E4) (i : Fin 4) :
    (eigenvalue S.Ω ((i : ℕ) + 1) - S.a) * c i ^ 2 ≤ 0 := by
  refine mul_nonpos_of_nonpos_of_nonneg ?_ (sq_nonneg _)
  have := eigenvalue_mono S.hN S.hΩadm (Nat.le_add_left 1 i) (by omega : (i : ℕ) + 1 ≤ 4)
  simp only [a]; linarith

/-- If `Q_a(u) = 0` for `u ∈ S \ {0}`, then `u` is an eigenfunction with eigenvalue `a`. -/
lemma eig_of_Qa_zero {c : E4} (hc : c ≠ 0) (h : Qshift S.a (S.U c) = 0) :
    IsEigenfunction S.Ω (S.U c) S.a := by
  refine ⟨S.U_mem c, S.U_ne_zero hc, fun φ hφ => ?_⟩
  rw [S.Qa_U] at h
  have hz := (Finset.sum_eq_zero_iff_of_nonpos fun i _ => S.Qa_term_nonpos c i).mp h
  have hterm : ∀ i : Fin 4, c i * eigenvalue S.Ω ((i : ℕ) + 1) = c i * S.a := fun i => by
    rcases mul_eq_zero.mp (hz i (Finset.mem_univ _)) with h1 | h1
    · rw [sub_eq_zero.mp h1]
    · rw [pow_eq_zero_iff two_ne_zero |>.mp h1]; simp
  simp only [U, qf_sum_left, l2_sum_left, qf_smul_left, l2_smul_left]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(S.he.1 i).2.2 φ hφ, ← mul_assoc, hterm i]
  ring

/-- The positive half of Lemma 5.1. -/
theorem strict_pos {c : E4} (hc : c ∈ S.K) :
    eigenvalue (posSign S.Ω (S.fU c)) 2 < S.b := by
  obtain ⟨hQp, hQn, hp0, hn0⟩ := S.balance hc
  have hc0 : c ≠ 0 := ne_zero_of_mem_sphere one_ne_zero ⟨c, hc.1⟩
  have hF := hc.2
  simp only [Fbal, sub_eq_zero] at hF
  set u := S.U c with hu_def
  set f := S.fU c with hf_def
  set Dp := posSign S.Ω f with hDp
  have hΩo : IsOpen S.Ω := S.hΩadm.1
  have hrep : IsContRep S.Ω u f := S.fU_rep c
  have hpm : posPart u ∈ H Dp := (parts_mem S.hΩadm (S.U_mem c) hrep).1
  have hnm : negPart u ∈ H (negSign S.Ω f) := (parts_mem S.hΩadm (S.U_mem c) hrep).2
  have hDpo : IsOpen Dp := isOpen_posSign hΩo hrep.1
  have hDpadm : IsAdmissible Dp :=
    ⟨hDpo, nonempty_of_mem_H hpm hp0, S.hΩadm.2.2.subset (posSign_subset _ _)⟩
  have hl : 0 < l2 (posPart u) (posPart u) := l2_self_pos hpm hp0
  have hR : rayleigh (posPart u) ≤ S.a := by
    rw [rayleigh, div_le_iff₀ hl]; simp only [Qshift] at hQp; linarith
  have h1 := eigenvalue_one_le_rayleigh hpm hp0
  have hppw := S.ppw.admissible S.hN hDpadm
  have hC := one_lt_CN S.hN
  have hgap : CN N * S.a ≤ S.b := S.hgap
  have ha := S.a_pos
  by_contra hge
  push_neg at hge
  have hl1v : eigenvalue Dp 1 = S.a := by
    apply le_antisymm (h1.trans hR)
    by_contra hlt
    push_neg at hlt
    have : CN N * eigenvalue Dp 1 < CN N * S.a := mul_lt_mul_of_pos_left hlt (by linarith)
    linarith
  have hRa : rayleigh (posPart u) = S.a := le_antisymm hR (hl1v ▸ h1)
  have hQp0 : Qshift S.a (posPart u) = 0 := by
    rw [rayleigh, div_eq_iff hl.ne'] at hRa
    simp only [Qshift]; linarith
  have hl2v : eigenvalue Dp 2 = CN N * eigenvalue Dp 1 := by
    rw [hl1v]; linarith [hl1v ▸ hppw]
  have hQ0 : Qshift S.a u = 0 := by rw [S.Qa_U_split, hQp0, ← hF, hQp0, add_zero]
  have heig : IsEigenfunction S.Ω u S.a := S.eig_of_Qa_zero hc0 hQ0
  obtain ⟨f', hf's, hf'rep, -, -, hcompP, -⟩ := nodal S.hN S.hΩadm heig
  have heq : Set.EqOn f f' S.Ω := eqOn_of_contRep hΩo hrep hf'rep
  have hsign : posSign S.Ω f' = Dp := by
    ext x
    simp only [hDp, posSign, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hx, h⟩; exact ⟨hx, by rwa [heq hx]⟩
    · rintro ⟨hx, h⟩; exact ⟨hx, by rwa [← heq hx]⟩
  have hnsign : negSign S.Ω f' = negSign S.Ω f := by
    ext x
    simp only [negSign, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hx, h⟩; exact ⟨hx, by rwa [heq hx]⟩
    · rintro ⟨hx, h⟩; exact ⟨hx, by rwa [← heq hx]⟩
  rw [hsign] at hcompP
  -- `D₊(u)` has only one nodal component
  have hall : ∀ x ∈ Dp, ∀ y ∈ Dp, connectedComponentIn Dp y = connectedComponentIn Dp x := by
    intro x hx y hy
    by_contra hne
    obtain ⟨hex, hax⟩ := hcompP x hx
    obtain ⟨hey, hay⟩ := hcompP y hy
    have := eigenvalue_two_le_of_disjoint (hDpo.connectedComponentIn)
      (hDpo.connectedComponentIn) (connectedComponentIn_subset _ _)
      (connectedComponentIn_subset _ _) (connectedComponentIn_disjoint_of_ne hne) hey.1 hex.1
      hey.2.1 hex.2.1 ha.le (hey.2.2 _ hey.1) (hex.2.2 _ hex.1)
    linarith [S.a_lt_b]
  obtain ⟨x0, hx0⟩ := hDpadm.2.1
  have hCx0 : connectedComponentIn Dp x0 = Dp := eq_connectedComponentIn_of_forall (hall x0 hx0)
  have hDpconn : IsConnected Dp := by
    rw [← hCx0]
    exact ⟨⟨x0, mem_connectedComponentIn hx0⟩, isPreconnected_connectedComponentIn⟩
  have hDpdom : IsDomain Dp := ⟨hDpadm, hDpconn⟩
  obtain ⟨y, R, hR0, hlB, hHB⟩ := S.ppwEq hDpdom hl2v
  rw [hl1v] at hlB
  have hRval := ball_radius_eq S.hN hR0 ha hlB
  obtain ⟨Φ, _, hΦprof, _, _, _, _, _, _, hball⟩ := ext_ball_basic S.hN ha
  obtain ⟨_, ⟨φ, hφeig, hφae⟩, _⟩ := hball y
  rw [← hRval] at hφeig hφae
  obtain ⟨hweig, -⟩ := hcompP x0 hx0
  rw [hCx0] at hweig
  set w := restrictTo Dp (posPart u) with hw_def
  have hwB : IsEigenfunction (ball y R) w S.a := by
    simp only [IsEigenfunction] at hweig ⊢
    rw [← hHB]; exact hweig
  have hφ1 : IsEigenfunction (ball y R) φ (eigenvalue (ball y R) 1) := by rw [hlB]; exact hφeig
  have hw1 : IsEigenfunction (ball y R) w (eigenvalue (ball y R) 1) := by rw [hlB]; exact hwB
  obtain ⟨hsimpB, -⟩ := ground_state S.hN (isDomain_ball y hR0)
  obtain ⟨s, hs⟩ := hsimpB φ w hφ1 hw1
  have hs0 : s ≠ 0 := by rintro rfl; exact hwB.2.1 (by rw [hs, zero_smul])
  have hind : Dp.indicator (u.1 : RN N → ℝ) =ᵐ[volume] fun x =>
      s * (ball y R).indicator (fun x => besselProfile N S.a (x - y)) x := by
    have hne : ∀ᵐ x ∂(volume : Measure (RN N)), x ≠ y := by
      haveI : Nonempty (Fin N) := ⟨⟨0, by have := S.hN; omega⟩⟩
      haveI : Nontrivial (RN N) := inferInstance
      rw [ae_iff]; simp only [ne_eq, not_not, Set.setOf_eq_eq_singleton]; exact measure_singleton y
    refine (indicator_eq_restrictTo_posPart S.hΩadm.1.measurableSet hDpo.measurableSet hrep
      le_rfl).trans ?_
    rw [← hw_def, hs]
    filter_upwards [Lp.coeFn_smul s φ.1, hφae, hne] with x h1 h2 h3
    simp only [Prod.smul_fst, h1, Pi.smul_apply, smul_eq_mul, h2]
    congr 1
    by_cases hx : x ∈ ball y R
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, hΦprof _ (sub_ne_zero.mpr h3)]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
  have hnegne : (negSign S.Ω f').Nonempty := by rw [hnsign]; exact nonempty_of_mem_H hnm hn0
  have hposne : (posSign S.Ω f').Nonempty := by rw [hsign]; exact hDpadm.2.1
  have hlb := lemma_ball S.hN S.hΩ ha heig hf'rep hposne hnegne (G := Dp)
    (Or.inl ⟨x0, hsign ▸ hx0, by rw [hsign, hCx0]⟩) y s hs0 (by rw [← hRval]; exact hind)
  have h5 : eigenvalue S.Ω 5 ≤ eigenvalue S.Ω (2 * N + 2) :=
    eigenvalue_mono S.hN S.hΩadm (by norm_num) (by have := S.hN; omega)
  have hb : S.b = eigenvalue S.Ω 5 := rfl
  linarith

/-- **Lemma 5.1 (Strictness on both sign sets).** For every `u ∈ K`,
`λ₂(D₊(u)) < b` and `λ₂(D₋(u)) < b`. -/
theorem lemma_strict {c : E4} (hc : c ∈ S.K) :
    eigenvalue (posSign S.Ω (S.fU c)) 2 < S.b ∧ eigenvalue (negSign S.Ω (S.fU c)) 2 < S.b := by
  refine ⟨S.strict_pos hc, ?_⟩
  have := S.strict_pos (S.neg_mem_K hc)
  rwa [fU_neg, ← negSign_eq_posSign_neg] at this

end Setup

end FourthRatio

end
