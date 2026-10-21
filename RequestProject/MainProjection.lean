module

public import RequestProject.MainStable

/-!
# The projected tangent vector (proof of Lemma 5.6, algebraic part)

For `u ∈ 𝕊(S)` we use the coordinates `P ψ = (⟨ψ, eᵢ⟩)ᵢ ∈ ℝ⁴` of the `L²`-projection onto
`S`, the vectors `P|u|`, `v = P|u| - ⟨u,|u|⟩ u`, the number `d = ⟨v, e⟩` and the linear map
`y ↦ x - (⟨x,e⟩/d) v`, `x = y - ⟨y,u⟩u`, whose value on `y = Pφ` is the vector `w` of the paper.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Function
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

variable {N : ℕ}

lemma bshift_lin3 (γ a b c : ℝ) (x y z : Amb N) :
    bshift γ (a • x + b • y + c • z) (a • x + b • y + c • z) =
      a ^ 2 * bshift γ x x + b ^ 2 * bshift γ y y + c ^ 2 * bshift γ z z +
        2 * a * b * bshift γ x y + 2 * a * c * bshift γ x z + 2 * b * c * bshift γ y z := by
  simp only [bshift, qf_add_left, qf_add_right, qf_smul_left, qf_smul_right, l2_add_left,
    l2_add_right, l2_smul_left, l2_smul_right, qf_comm y x, qf_comm z x, qf_comm z y,
    l2_comm y x, l2_comm z x, l2_comm z y]
  ring

namespace Setup

variable (S : Setup N)

/-- Coordinates `P ψ = (⟨ψ, eᵢ⟩)ᵢ` of the `L²`-projection onto `S`. -/
def Pc : Amb N →ₗ[ℝ] E4 where
  toFun ψ := WithLp.toLp 2 (fun i : Fin 4 => l2 ψ (S.e i))
  map_add' x y := by ext i; simp
  map_smul' a x := by ext i; simp

@[simp] lemma Pc_apply (ψ : Amb N) (i : Fin 4) : S.Pc ψ i = l2 ψ (S.e i) := rfl

lemma Pc_U (c : E4) : S.Pc (S.U c) = c := by
  ext i; simp [S.l2_U_e]

lemma inner_Pc (y : E4) (ψ : Amb N) : ⟪y, S.Pc ψ⟫ = l2 (S.U y) ψ := by
  simp only [PiLp.inner_apply, Pc_apply, RCLike.inner_apply, conj_trivial, U, l2_sum_left,
    l2_smul_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [l2_comm]
  ring

/-- `P|u|`. -/
def absC (u : E4) : E4 := S.Pc (posPart (S.U u) + negPart (S.U u))

/-- `v = P|u| - ⟨u,|u|⟩ u`. -/
def vC (u : E4) : E4 := S.absC u - ⟪u, S.absC u⟫ • u

/-- `d = ⟨v, e⟩`. -/
def dC (u : E4) : ℝ := ⟪S.vC u, e4⟫

/-- The linear map `y ↦ x - (⟨x,e⟩/d) v` with `x = y - ⟨y,u⟩ u`. -/
def Amap (u y : E4) : E4 :=
  (y - ⟪y, u⟫ • u) - (⟪y - ⟪y, u⟫ • u, e4⟫ / S.dC u) • S.vC u

lemma Amap_add (u y z : E4) : S.Amap u (y + z) = S.Amap u y + S.Amap u z := by
  simp only [Amap, inner_add_left, inner_sub_left, inner_smul_left, add_smul,
    RCLike.conj_to_real]
  module

lemma Amap_smul (u y : E4) (a : ℝ) : S.Amap u (a • y) = a • S.Amap u y := by
  simp only [Amap, inner_smul_left, inner_sub_left, RCLike.conj_to_real, smul_sub, smul_smul]
  rw [show (a * ⟪y, e4⟫ - a * ⟪y, u⟫ * ⟪u, e4⟫) / S.dC u =
    a * ((⟪y, e4⟫ - ⟪y, u⟫ * ⟪u, e4⟫) / S.dC u) by ring]

lemma Amap_sub (u y z : E4) : S.Amap u (y - z) = S.Amap u y - S.Amap u z := by
  rw [sub_eq_add_neg, S.Amap_add, ← neg_one_smul ℝ z, S.Amap_smul]
  module

lemma Amap_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ) (y : ι → E4) (u : E4) :
    S.Amap u (∑ i ∈ s, a i • y i) = ∑ i ∈ s, a i • S.Amap u (y i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := S.Amap_smul u 0 0
    simpa using this
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, S.Amap_add, S.Amap_smul, ih]

lemma Amap_self {u : E4} (hu : ‖u‖ = 1) : S.Amap u u = 0 := by
  have : ⟪u, u⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  simp [Amap, hu]

lemma Amap_absC {u : E4} (hd : S.dC u ≠ 0) : S.Amap u (S.absC u) = 0 := by
  have hx : S.absC u - ⟪S.absC u, u⟫ • u = S.vC u := by
    rw [vC, real_inner_comm]
  rw [Amap, hx, ← dC, div_self hd, one_smul, sub_self]

lemma vC_inner_u {u : E4} (hu : ‖u‖ = 1) : ⟪S.vC u, u⟫ = 0 := by
  have : ⟪u, u⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  simp only [vC, inner_sub_left, inner_smul_left, RCLike.conj_to_real, this]
  rw [real_inner_comm u (S.absC u)]
  ring

lemma Amap_inner_u {u : E4} (hu : ‖u‖ = 1) (y : E4) : ⟪S.Amap u y, u⟫ = 0 := by
  have : ⟪u, u⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  simp only [Amap, inner_sub_left, inner_smul_left, RCLike.conj_to_real, this, S.vC_inner_u hu]
  ring

lemma Amap_inner_e {u : E4} (hd : S.dC u ≠ 0) (y : E4) : ⟪S.Amap u y, e4⟫ = 0 := by
  rw [Amap, inner_sub_left, inner_smul_left, RCLike.conj_to_real, ← dC]
  field_simp
  ring

lemma Amap_eq_zero {u : E4} {y : E4} (h : S.Amap u y = 0) :
    ∃ p q : ℝ, y = p • u + q • S.absC u := by
  set t := ⟪y - ⟪y, u⟫ • u, e4⟫ / S.dC u
  refine ⟨⟪y, u⟫ - t * ⟪u, S.absC u⟫, t, ?_⟩
  have h' : y - ⟪y, u⟫ • u = t • S.vC u := sub_eq_zero.mp h
  rw [vC] at h'
  rw [sub_smul, mul_smul]
  calc y = (y - ⟪y, u⟫ • u) + ⟪y, u⟫ • u := by abel
    _ = _ := by rw [h']; module

lemma Pc_posPart_sub (u : E4) :
    S.Pc (posPart (S.U u)) - S.Pc (negPart (S.U u)) = u := by
  rw [← map_sub, S.posPart_sub_negPart_U, Pc_U]

lemma Pc_posPart_add (u : E4) :
    S.Pc (posPart (S.U u)) + S.Pc (negPart (S.U u)) = S.absC u := by
  rw [absC, map_add]

lemma Amap_Pc_posPart {u : E4} (hu : ‖u‖ = 1) (hd : S.dC u ≠ 0) :
    S.Amap u (S.Pc (posPart (S.U u))) = 0 := by
  have : S.Pc (posPart (S.U u)) = (1 / 2 : ℝ) • u + (1 / 2 : ℝ) • S.absC u := by
    have h1 := S.Pc_posPart_sub u
    have h2 := S.Pc_posPart_add u
    have : S.Pc (posPart (S.U u)) = (1 / 2 : ℝ) • (S.Pc (posPart (S.U u)) -
      S.Pc (negPart (S.U u))) + (1 / 2 : ℝ) • (S.Pc (posPart (S.U u)) +
      S.Pc (negPart (S.U u))) := by module
    rwa [h1, h2] at this
  rw [this, S.Amap_add, S.Amap_smul, S.Amap_smul, S.Amap_self hu, S.Amap_absC hd]
  simp

/-! ### Continuity -/

lemma continuous_negPart_U_fst : Continuous fun c : E4 => (negPart (S.U c)).1 := by
  have : (fun c : E4 => (negPart (S.U c)).1) = fun c => (posPart (S.U (-c))).1 := by
    funext c; rw [U_neg, posPart_neg]
  rw [this]
  exact S.continuous_posPart_U_fst.comp continuous_neg

lemma continuous_l2_e_posPart (i : Fin 4) :
    Continuous fun c : E4 => l2 (posPart (S.U c)) (S.e i) :=
  continuous_inner.comp (S.continuous_posPart_U_fst.prodMk continuous_const)

lemma continuous_l2_e_negPart (i : Fin 4) :
    Continuous fun c : E4 => l2 (negPart (S.U c)) (S.e i) :=
  continuous_inner.comp (S.continuous_negPart_U_fst.prodMk continuous_const)

lemma continuous_absC : Continuous S.absC := by
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  simp only [l2_add_left]
  exact (S.continuous_l2_e_posPart i).add (S.continuous_l2_e_negPart i)

lemma continuous_vC : Continuous S.vC :=
  S.continuous_absC.sub ((continuous_id.inner (𝕜 := ℝ) S.continuous_absC).smul continuous_id)

lemma continuous_dC : Continuous S.dC :=
  S.continuous_vC.inner continuous_const

lemma continuousAt_Amap {u : E4} (hd : S.dC u ≠ 0) (y : E4) :
    ContinuousAt (fun p : E4 × E4 => S.Amap p.1 p.2) (u, y) := by
  simp only [Amap]
  have h1 : Continuous fun p : E4 × E4 => p.2 - ⟪p.2, p.1⟫ • p.1 :=
    continuous_snd.sub ((continuous_snd.inner (𝕜 := ℝ) continuous_fst).smul continuous_fst)
  have hnum : Continuous (fun p : E4 × E4 => ⟪p.2 - ⟪p.2, p.1⟫ • p.1, e4⟫) :=
    h1.inner (𝕜 := ℝ) continuous_const
  have hfrac : ContinuousAt (fun p : E4 × E4 =>
      ⟪p.2 - ⟪p.2, p.1⟫ • p.1, e4⟫ / S.dC p.1) (u, y) :=
    hnum.continuousAt.div (S.continuous_dC.comp continuous_fst).continuousAt hd
  exact h1.continuousAt.sub (hfrac.smul (S.continuous_vC.comp continuous_fst).continuousAt)

/-! ### Positivity of `d` and injectivity -/

lemma inner_e4 (y : E4) : ⟪y, e4⟫ = y 0 := by
  simp [e4, PiLp.inner_apply, PiLp.single_apply]

lemma dC_pos {u : E4} (hu : ‖u‖ = 1) (hg : S.Good u) : 0 < S.dC u := by
  obtain ⟨hp0, hn0, -⟩ := hg
  set p := posPart (S.U u)
  set n := negPart (S.U u)
  have hpm := S.posPart_U_mem u
  have hnm := S.negPart_U_mem u
  have hrp := l2_self_pos hpm hp0
  have hrn := l2_self_pos hnm hn0
  have hap := l2_pos_of_nonneg S.hΩadm hpm hp0 (posPart_fst_nonneg _) (S.he.mem_H 0)
    (S.hf 0) S.hf0
  have han := l2_pos_of_nonneg S.hΩadm hnm hn0 (negPart_fst_nonneg _) (S.he.mem_H 0)
    (S.hf 0) S.hf0
  have hpn : l2 p n = 0 := (parts_orthogonal (S.U u)).2
  have hU : S.U u = p - n := (S.posPart_sub_negPart_U u).symm
  have h1 : ⟪u, u⟫ = l2 (p - n) (p - n) := by rw [← hU, S.l2_U]
  have hu1 : ⟪u, u⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  have h2 : ⟪u, S.absC u⟫ = l2 (p - n) (p + n) := by rw [absC, inner_Pc, ← hU]
  have h3 : ⟪S.absC u, e4⟫ = l2 (p + n) (S.e 0) := by rw [inner_e4, absC, Pc_apply]; rfl
  have h4 : ⟪u, e4⟫ = l2 (p - n) (S.e 0) := by
    rw [inner_e4, ← hU]; exact (S.l2_U_e u 0).symm
  have hd : S.dC u = ⟪S.absC u, e4⟫ - ⟪u, S.absC u⟫ * ⟪u, e4⟫ := by
    simp only [dC, vC, inner_sub_left, inner_smul_left, RCLike.conj_to_real]
  rw [hd, h2, h3, h4]
  rw [h1] at hu1
  simp only [l2_add_left, l2_add_right, l2_sub_left, l2_sub_right, l2_comm n p, hpn] at hu1 ⊢
  have e1 : l2 p p = 1 - l2 n n := by linarith
  rw [e1]
  nlinarith [mul_pos hrn hap, mul_pos hrp han]

/-- **Lemma 5.6, injectivity part.** If `φ ∈ H₀¹(D₊(u))` is `𝔟`-orthogonal to `u₊` and
`𝔟`-negative, then the vector `w = A_u(Pφ)` is nonzero. -/
lemma Amap_Pc_ne_zero {u : E4} (hu : ‖u‖ = 1) (hg : S.Good u) {φ : Amb N}
    (hφ : φ ∈ H (posSign S.Ω (S.fU u))) (hφp : bshift S.b φ (posPart (S.U u)) = 0)
    (hφφ : bshift S.b φ φ < 0) : S.Amap u (S.Pc φ) ≠ 0 := by
  intro h
  have hd := (S.dC_pos hu hg).ne'
  obtain ⟨p, q, hy⟩ := S.Amap_eq_zero h
  obtain ⟨hp0, hn0, hpb, hnb, -⟩ := hg
  set pp := posPart (S.U u)
  set nn := negPart (S.U u)
  have hrep := S.fU_rep u
  have hparts := parts_mem S.hΩadm (S.U_mem u) hrep
  have hΩo := S.hΩadm.1
  have hpo : IsOpen (posSign S.Ω (S.fU u)) := isOpen_posSign hΩo hrep.1
  have hno : IsOpen (negSign S.Ω (S.fU u)) := isOpen_negSign hΩo hrep.1
  have hdisj : Disjoint (posSign S.Ω (S.fU u)) (negSign S.Ω (S.fU u)) := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    have h1 : 0 < S.fU u x := hx1.2
    have h2 : S.fU u x < 0 := hx2.2
    linarith
  have hφn : bshift S.b φ nn = 0 :=
    bshift_eq_zero_of_disjoint hpo.measurableSet hno.measurableSet hdisj hφ hparts.2 _
  have hpn : bshift S.b pp nn = 0 := by
    obtain ⟨h1, h2⟩ := parts_orthogonal (S.U u)
    simp [bshift, pp, nn, h1, h2]
  set W := Submodule.span ℝ (Set.range ![pp, nn, φ])
  have hφΩ : φ ∈ H S.Ω := H_mono (posSign_subset _ _) hφ
  have hWle : W ≤ H S.Ω := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · simpa using S.posPart_U_mem u
    · simpa using S.negPart_U_mem u
    · simpa using hφΩ
  have hWneg : ∀ x ∈ W, x ≠ 0 → bshift S.b x x < 0 := by
    intro x hx hx0
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hx
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at hx0 ⊢
    rw [bshift_lin3, bshift_comm S.b pp φ, hφp, hpn, bshift_comm S.b nn φ, hφn]
    have : c 0 ≠ 0 ∨ c 1 ≠ 0 ∨ c 2 ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hx0 (by simp [hc])
    have q0 := mul_nonneg (sq_nonneg (c 0)) (neg_nonneg.mpr hpb.le)
    have q1 := mul_nonneg (sq_nonneg (c 1)) (neg_nonneg.mpr hnb.le)
    have q2 := mul_nonneg (sq_nonneg (c 2)) (neg_nonneg.mpr hφφ.le)
    rcases this with h | h | h
    · have := mul_pos (pow_pos (abs_pos.mpr h) 2) (neg_pos.mpr hpb)
      rw [sq_abs] at this
      linarith
    · have := mul_pos (pow_pos (abs_pos.mpr h) 2) (neg_pos.mpr hnb)
      rw [sq_abs] at this
      linarith
    · have := mul_pos (pow_pos (abs_pos.mpr h) 2) (neg_pos.mpr hφφ)
      rw [sq_abs] at this
      linarith
  set ψ := φ - ((p + q) • pp + (q - p) • nn)
  have hψW : ψ ∈ W := by
    refine W.sub_mem (Submodule.subset_span ⟨2, rfl⟩) (W.add_mem ?_ ?_)
    · exact W.smul_mem _ (Submodule.subset_span ⟨0, rfl⟩)
    · exact W.smul_mem _ (Submodule.subset_span ⟨1, rfl⟩)
  have hPψ : S.Pc ψ = 0 := by
    have hsub := S.Pc_posPart_sub u
    have hadd := S.Pc_posPart_add u
    simp only [ψ, map_sub, map_add, map_smul]
    rw [hy]
    linear_combination (norm := module) (-p) • hsub + (-q) • hadd
  have hψ0 : ψ = 0 := by
    refine (lemma_index S.hN S.hΩadm S.he (k := 4) S.a_lt_b le_rfl).2 W hWle hWneg ψ hψW ?_
    intro j hj
    have := congrArg (fun z : E4 => z ⟨j, hj⟩) hPψ
    simpa using this
  have hφeq : φ = (p + q) • pp + (q - p) • nn := sub_eq_zero.mp hψ0
  have : bshift S.b φ φ = 0 := by
    calc bshift S.b φ φ = bshift S.b φ ((p + q) • pp + (q - p) • nn) := by rw [← hφeq]
      _ = (p + q) * bshift S.b φ pp + (q - p) * bshift S.b φ nn := by
        simp only [bshift, qf_add_right, qf_smul_right, l2_add_right, l2_smul_right]; ring
      _ = 0 := by rw [hφp, hφn]; ring
  linarith

end Setup

end FourthRatio

end
