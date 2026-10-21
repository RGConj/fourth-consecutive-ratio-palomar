module

public import RequestProject.MainStrict

/-!
# Stability of the two negative directions (Lemma 5.2)
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Function
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

variable {N : ℕ}

/-- The shifted form `𝔟_γ` as a bilinear form. -/
def bform (γ : ℝ) : LinearMap.BilinForm ℝ (Amb N) :=
  LinearMap.mk₂ ℝ (bshift γ)
    (fun v w u => by simp only [bshift, qf_add_left, l2_add_left]; ring)
    (fun c v w => by simp only [bshift, qf_smul_left, l2_smul_left, smul_eq_mul]; ring)
    (fun v w u => by simp only [bshift, qf_add_right, l2_add_right]; ring)
    (fun c v w => by simp only [bshift, qf_smul_right, l2_smul_right, smul_eq_mul]; ring)

@[simp] lemma bform_apply (γ : ℝ) (v w : Amb N) : bform γ v w = bshift γ v w := rfl

lemma finrank_le_negIndex {M : Type*} [AddCommGroup M] [Module ℝ M] {b : M → M → ℝ}
    {X W : Submodule ℝ M} (hW : W ≤ X) [FiniteDimensional ℝ W]
    (hneg : ∀ v ∈ W, v ≠ 0 → b v v < 0) : (Module.finrank ℝ W : ℕ∞) ≤ negIndex b X :=
  le_iSup_of_le W (le_iSup_of_le hW (le_iSup_of_le inferInstance (le_iSup_of_le hneg le_rfl)))

/-- Two `B`-orthogonal negative vectors span a negative plane. -/
lemma span_pair_negative {M : Type*} [AddCommGroup M] [Module ℝ M]
    (B : LinearMap.BilinForm ℝ M) (hB : ∀ v w, B v w = B w v) {v w : M}
    (hvv : B v v < 0) (hww : B w w < 0) (hvw : B v w = 0) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range ![v, w])) = 2 ∧
      ∀ x ∈ Submodule.span ℝ (Set.range ![v, w]), x ≠ 0 → B x x < 0 := by
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
  refine ⟨by rw [finrank_span_eq_card hli]; simp, ?_⟩
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

lemma bshift_eq_zero_of_disjoint {D₁ D₂ : Set (RN N)} (h₁ : MeasurableSet D₁)
    (h₂ : MeasurableSet D₂) (hd : Disjoint D₁ D₂) {v w : Amb N} (hv : v ∈ H D₁)
    (hw : w ∈ H D₂) (γ : ℝ) : bshift γ v w = 0 := by
  obtain ⟨h1, h2⟩ := orthogonal_of_disjoint h₁ h₂ hd hv hw
  simp [bshift, h1, h2]

/-- Upper bound for the negative index: if `D₂ ⊆ D` (disjoint from `D₁ ⊆ D`) carries a negative
plane and `λ₄(D) < γ ≤ λ₅(D)`, then the negative index on `H(D₁)` is at most two. -/
lemma negIndex_le_two_of_disjoint (hN : 2 ≤ N) {D D₁ D₂ : Set (RN N)} (hD : IsAdmissible D)
    {e : ℕ → Amb N} (he : IsSpectralBasis D e) {γ : ℝ} (h4 : eigenvalue D 4 < γ)
    (h5 : γ ≤ eigenvalue D 5) (hD₁ : D₁ ⊆ D) (hD₂ : D₂ ⊆ D) (hm₁ : MeasurableSet D₁)
    (hm₂ : MeasurableSet D₂) (hd : Disjoint D₁ D₂) {v w : Amb N} (hv : v ∈ H D₂)
    (hw : w ∈ H D₂) (hvv : bshift γ v v < 0) (hww : bshift γ w w < 0)
    (hvw : bshift γ v w = 0) : negIndex (bshift γ) (H D₁) ≤ 2 := by
  have hZ := (lemma_index hN hD he h4 h5).1
  obtain ⟨hP2, hPneg⟩ := span_pair_negative (bform γ) (fun x y => bshift_comm γ x y)
    (v := v) (w := w) hvv hww hvw
  set P := Submodule.span ℝ (Set.range ![v, w])
  have hPle : P ≤ H D₂ := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · simpa using hv
    · simpa using hw
  refine iSup_le fun W => iSup_le fun hW => iSup_le fun hfin => iSup_le fun hneg => ?_
  have horth : ∀ x ∈ W, ∀ y ∈ P, bshift γ x y = 0 := fun x hx y hy =>
    bshift_eq_zero_of_disjoint hm₁ hm₂ hd (hW hx) (hPle hy) γ
  have hinf : W ⊓ P = ⊥ := by
    rw [eq_bot_iff]
    intro x ⟨hxW, hxP⟩
    by_contra hx0
    have := hneg x hxW hx0
    rw [horth x hxW x hxP] at this
    exact lt_irrefl _ this
  have hsupneg : ∀ x ∈ W ⊔ P, x ≠ 0 → bshift γ x x < 0 := by
    intro x hx hx0
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    have hyz := horth y hy z hz
    have hzy : bshift γ z y = 0 := by rw [bshift_comm]; exact hyz
    have hsum : bshift γ (y + z) (y + z) = bshift γ y y + bshift γ z z := by
      simp only [bshift, qf_add_left, qf_add_right, l2_add_left, l2_add_right] at hyz hzy ⊢
      linarith
    rw [hsum]
    have hzle : bshift γ z z ≤ 0 := by
      by_cases hz0 : z = 0
      · simp [hz0, bshift]
      · exact (hPneg z hz hz0).le
    by_cases hy0 : y = 0
    · subst hy0
      have hz0 : z ≠ 0 := by simpa using hx0
      have := hPneg z hz hz0
      simp only [bform_apply] at this
      simp [bshift] at this ⊢
      linarith
    · linarith [hneg y hy hy0]
  haveI : FiniteDimensional ℝ P := FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
  have hle := finrank_le_negIndex (b := bshift γ)
    (sup_le (hW.trans (H_mono hD₁)) (hPle.trans (H_mono hD₂))) hsupneg
  rw [hZ] at hle
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq W P
  rw [hinf, finrank_bot, add_zero, hP2] at hdim
  rw [hdim] at hle
  have : Module.finrank ℝ W + 2 ≤ 4 := by exact_mod_cast hle
  exact_mod_cast (by omega : Module.finrank ℝ W ≤ 2)

lemma bshift_sub_smul_self (γ t : ℝ) (x y : Amb N) :
    bshift γ (y - t • x) (y - t • x) =
      bshift γ y y - 2 * t * bshift γ x y + t ^ 2 * bshift γ x x := by
  simp only [bshift, qf_sub_left, qf_sub_right, qf_smul_left, qf_smul_right, l2_sub_left,
    l2_sub_right, l2_smul_left, l2_smul_right, qf_comm y x, l2_comm y x]
  ring

lemma bshift_sub_smul_right (γ t : ℝ) (x y : Amb N) :
    bshift γ x (y - t • x) = bshift γ x y - t * bshift γ x x := by
  simp only [bshift, qf_sub_right, qf_smul_right, l2_sub_right, l2_smul_right]
  ring

/-- Elements of the span of test functions are supported in a compact subset. -/
lemma span_testGraph_compact {D : Set (RN N)} {z : Amb N}
    (hz : z ∈ Submodule.span ℝ (testGraph D)) :
    ∃ Kc : Set (RN N), IsCompact Kc ∧ Kc ⊆ D ∧
      ∀ D', Kc ⊆ D' → z ∈ Submodule.span ℝ (testGraph D') := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨φ, hφ, hcs, hts, h1, h2⟩ := hx
    exact ⟨tsupport φ, hcs.isCompact, hts,
      fun D' hD' => Submodule.subset_span ⟨φ, hφ, hcs, hD', h1, h2⟩⟩
  | zero => exact ⟨∅, isCompact_empty, Set.empty_subset _, fun _ _ => Submodule.zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨K1, hK1, hK1D, h1⟩ := hx
    obtain ⟨K2, hK2, hK2D, h2⟩ := hy
    exact ⟨K1 ∪ K2, hK1.union hK2, Set.union_subset hK1D hK2D, fun D' hD' =>
      Submodule.add_mem _ (h1 D' (Set.subset_union_left.trans hD'))
        (h2 D' (Set.subset_union_right.trans hD'))⟩
  | smul a x _ hx =>
    obtain ⟨K1, hK1, hK1D, h1⟩ := hx
    exact ⟨K1, hK1, hK1D, fun D' hD' => Submodule.smul_mem _ a (h1 D' hD')⟩

namespace Setup

variable (S : Setup N)

lemma continuousAt_fU {x : RN N} (hx : x ∈ S.Ω) (c0 : E4) :
    ContinuousAt (fun p : E4 × RN N => S.fU p.1 p.2) (c0, x) := by
  simp only [fU]
  refine tendsto_finsetSum _ fun i _ => ?_
  refine Tendsto.mul ?_ ?_
  · exact ((continuous_apply i).comp ((PiLp.continuous_ofLp 2 _).comp continuous_fst)).continuousAt
  · exact ((S.hf i).1.continuousAt (S.hΩadm.1.mem_nhds hx)).comp continuousAt_snd

lemma eventually_compact_subset_posSign {c0 : E4} {Kc : Set (RN N)} (hK : IsCompact Kc)
    (hKD : Kc ⊆ posSign S.Ω (S.fU c0)) : ∀ᶠ c in 𝓝 c0, Kc ⊆ posSign S.Ω (S.fU c) := by
  have := hK.eventually_forall_of_forall_eventually (x₀ := c0)
    (P := fun c x => 0 < S.fU c x)
    (fun x hx => (S.continuousAt_fU (hKD hx).1 c0).eventually (lt_mem_nhds (hKD hx).2))
  filter_upwards [this] with c hc x hx using ⟨(hKD hx).1, hc x hx⟩

lemma posSign_admissible {c : E4} (h0 : posPart (S.U c) ≠ 0) :
    IsAdmissible (posSign S.Ω (S.fU c)) :=
  ⟨isOpen_posSign S.hΩadm.1 (S.fU_rep c).1,
    nonempty_of_mem_H (parts_mem S.hΩadm (S.U_mem c) (S.fU_rep c)).1 h0,
    S.hΩadm.2.2.subset (posSign_subset _ _)⟩

/-- A negative orthogonal pair in the positive sign space, which stays in the positive sign
space for nearby `c` (approximation by test functions with compact support). -/
lemma exists_neg_pair {c0 : E4} (hc0 : c0 ∈ S.K) :
    ∃ v w : Amb N, bshift S.b v v < 0 ∧ bshift S.b w w < 0 ∧ bshift S.b v w = 0 ∧
      ∀ᶠ c in 𝓝 c0, v ∈ H (posSign S.Ω (S.fU c)) ∧ w ∈ H (posSign S.Ω (S.fU c)) := by
  set D0 := posSign S.Ω (S.fU c0) with hD0def
  have hD0 : IsAdmissible D0 := S.posSign_admissible (S.balance hc0).2.2.1
  obtain ⟨e', he'⟩ := exists_spectralBasis S.hN hD0
  have h2 := (S.lemma_strict hc0).1
  have h1 : eigenvalue D0 1 < S.b :=
    (eigenvalue_mono S.hN hD0 le_rfl (by norm_num)).trans_lt h2
  have hb : ∀ i j, bshift S.b (e' i) (e' j) =
      if i = j then eigenvalue D0 (i + 1) - S.b else 0 := by
    intro i j
    simp only [bshift]
    rw [(he'.1 i).2.2 _ (he'.mem_H j), he'.2.1]
    split_ifs <;> ring
  set G : Set (Amb N × Amb N) := {p | bshift S.b p.1 p.1 < 0 ∧ bshift S.b p.2 p.2 < 0 ∧
    bshift S.b p.1 p.2 ^ 2 < bshift S.b p.1 p.1 * bshift S.b p.2 p.2}
  have hGo : IsOpen G := by
    have c1 : Continuous fun p : Amb N × Amb N => bshift S.b p.1 p.1 :=
      (continuous_bshift S.b).comp (continuous_fst.prodMk continuous_fst)
    have c2 : Continuous fun p : Amb N × Amb N => bshift S.b p.2 p.2 :=
      (continuous_bshift S.b).comp (continuous_snd.prodMk continuous_snd)
    have c3 : Continuous fun p : Amb N × Amb N => bshift S.b p.1 p.2 := continuous_bshift S.b
    exact (isOpen_lt c1 continuous_const).inter ((isOpen_lt c2 continuous_const).inter
      (isOpen_lt (c3.pow 2) (c1.mul c2)))
  have hmem : (e' 0, e' 1) ∈ G := by
    simp only [G, Set.mem_setOf_eq, hb]
    norm_num
    refine ⟨by linarith, by linarith, ?_⟩
    have := mul_pos (sub_pos.mpr h1) (sub_pos.mpr h2)
    nlinarith
  set T := (Submodule.span ℝ (testGraph D0) : Set (Amb N))
  have hcl : (e' 0, e' 1) ∈ closure (T ×ˢ T) := by
    rw [closure_prod_eq]
    have hH : (H D0 : Set (Amb N)) = closure T := Submodule.topologicalClosure_coe _
    exact ⟨hH ▸ he'.mem_H 0, hH ▸ he'.mem_H 1⟩
  obtain ⟨⟨x, y⟩, ⟨hxx, hyy, hxy⟩, hx, hy⟩ := mem_closure_iff.mp hcl G hGo hmem
  simp only at hxx hyy hxy hx hy
  set w := y - (bshift S.b x y / bshift S.b x x) • x with hwdef
  have hw : w ∈ Submodule.span ℝ (testGraph D0) :=
    Submodule.sub_mem _ hy (Submodule.smul_mem _ _ hx)
  have hxx0 : bshift S.b x x ≠ 0 := hxx.ne
  have hyx : bshift S.b y x = bshift S.b x y := bshift_comm _ _ _
  refine ⟨x, w, hxx, ?_, ?_, ?_⟩
  · have : bshift S.b w w = bshift S.b y y - bshift S.b x y ^ 2 / bshift S.b x x := by
      rw [hwdef, bshift_sub_smul_self]
      field_simp
      ring
    rw [this, sub_neg, lt_div_iff_of_neg hxx]
    linarith
  · rw [hwdef, bshift_sub_smul_right]
    field_simp
    ring
  · obtain ⟨K1, hK1, hK1D, hK1s⟩ := span_testGraph_compact hx
    obtain ⟨K2, hK2, hK2D, hK2s⟩ := span_testGraph_compact hw
    filter_upwards [S.eventually_compact_subset_posSign (hK1.union hK2)
      (Set.union_subset hK1D hK2D)] with c hc
    exact ⟨Submodule.le_topologicalClosure _ (hK1s _ (Set.subset_union_left.trans hc)),
      Submodule.le_topologicalClosure _ (hK2s _ (Set.subset_union_right.trans hc))⟩

/-- The local "positive" stability properties at `c`. -/
def PosGood (c : E4) : Prop :=
  posPart (S.U c) ≠ 0 ∧ bshift S.b (posPart (S.U c)) (posPart (S.U c)) < 0 ∧
    ∃ v w : Amb N, v ∈ H (posSign S.Ω (S.fU c)) ∧ w ∈ H (posSign S.Ω (S.fU c)) ∧
      bshift S.b v v < 0 ∧ bshift S.b w w < 0 ∧ bshift S.b v w = 0

lemma bshift_posPart_neg {c0 : E4} (hc0 : c0 ∈ S.K) :
    bshift S.b (posPart (S.U c0)) (posPart (S.U c0)) < 0 := by
  obtain ⟨hQp, -, hp0, -⟩ := S.balance hc0
  have hl := l2_self_pos (S.posPart_U_mem c0) hp0
  have := S.a_lt_b
  simp only [bshift, Qshift] at hQp ⊢
  nlinarith

lemma continuous_bshift_posPart :
    Continuous fun c => bshift S.b (posPart (S.U c)) (posPart (S.U c)) := by
  have : (fun c => bshift S.b (posPart (S.U c)) (posPart (S.U c))) = fun c =>
      Qshift S.a (posPart (S.U c)) - (S.b - S.a) * l2 (posPart (S.U c)) (posPart (S.U c)) := by
    funext c; simp only [bshift, Qshift]; ring
  rw [this]
  exact S.continuous_Qa_posPart_U.sub (continuous_const.mul
    (continuous_inner.comp (S.continuous_posPart_U_fst.prodMk S.continuous_posPart_U_fst)))

lemma eventually_posGood {c0 : E4} (hc0 : c0 ∈ S.K) : ∀ᶠ c in 𝓝 c0, S.PosGood c := by
  obtain ⟨v, w, hvv, hww, hvw, hev⟩ := S.exists_neg_pair hc0
  filter_upwards [S.continuous_bshift_posPart.continuousAt.eventually
    (gt_mem_nhds (S.bshift_posPart_neg hc0)), hev] with c h1 hvw'
  refine ⟨fun h => ?_, h1, v, w, hvw'.1, hvw'.2, hvv, hww, hvw⟩
  rw [h] at h1
  simp [bshift] at h1

lemma good_of_posGood {c : E4} (hp : S.PosGood c) (hn : S.PosGood (-c)) : S.Good c := by
  simp only [PosGood, U_neg, posPart_neg, fU_neg, ← negSign_eq_posSign_neg] at hn
  obtain ⟨hp0, hpb, v, w, hv, hw, hvv, hww, hvw⟩ := hp
  obtain ⟨hn0, hnb, v', w', hv', hw', hvv', hww', hvw'⟩ := hn
  have hΩo := S.hΩadm.1
  have hpo : IsOpen (posSign S.Ω (S.fU c)) := isOpen_posSign hΩo (S.fU_rep c).1
  have hno : IsOpen (negSign S.Ω (S.fU c)) := isOpen_negSign hΩo (S.fU_rep c).1
  have hd : Disjoint (posSign S.Ω (S.fU c)) (negSign S.Ω (S.fU c)) := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    have h1 : 0 < S.fU c x := hx1.2
    have h2 : S.fU c x < 0 := hx2.2
    linarith
  have h4 : eigenvalue S.Ω 4 < S.b := S.a_lt_b
  have h5 : S.b ≤ eigenvalue S.Ω 5 := le_rfl
  refine ⟨hp0, hn0, hpb, hnb, le_antisymm ?_ ?_, le_antisymm ?_ ?_⟩
  · exact negIndex_le_two_of_disjoint S.hN S.hΩadm S.he h4 h5 (posSign_subset _ _)
      (negSign_subset _ _) hpo.measurableSet hno.measurableSet hd hv' hw' hvv' hww' hvw'
  · exact two_le_negIndex_of_orth (bform S.b) (fun x y => bshift_comm _ x y) _ hv hw hvv hww hvw
  · exact negIndex_le_two_of_disjoint S.hN S.hΩadm S.he h4 h5 (negSign_subset _ _)
      (posSign_subset _ _) hno.measurableSet hpo.measurableSet hd.symm hv hw hvv hww hvw
  · exact two_le_negIndex_of_orth (bform S.b) (fun x y => bshift_comm _ x y) _ hv' hw' hvv'
      hww' hvw'

lemma eventually_good {c0 : E4} (hc0 : c0 ∈ S.K) : ∀ᶠ c in 𝓝 c0, S.Good c := by
  have hn : ∀ᶠ c in 𝓝 c0, S.PosGood (-c) :=
    (continuous_neg.tendsto c0).eventually (S.eventually_posGood (S.neg_mem_K hc0))
  filter_upwards [S.eventually_posGood hc0, hn] with c h1 h2 using S.good_of_posGood h1 h2

/-- **Lemma 5.2 (Stability of the two negative directions).** There is an open neighbourhood
`𝒪` of `K` such that at every `u ∈ 𝒪 ∩ 𝕊(S)` both truncations are nonzero and `𝔟`-negative and
both sign spaces have negative index exactly two. -/
theorem lemma_stable : ∃ O : Set E4, IsOpen O ∧ S.K ⊆ O ∧ ∀ c ∈ O ∩ sphere 0 1, S.Good c :=
  ⟨interior {c | S.Good c}, isOpen_interior,
    fun _ hc => mem_interior_iff_mem_nhds.mpr (S.eventually_good hc),
    fun c hc => (interior_subset hc.1 : c ∈ {c | S.Good c})⟩

end Setup

end FourthRatio

end
