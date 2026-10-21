module

public import RequestProject.Antisym

/-!
# Reflection symmetry of low eigenfunctions of the ball

Let `B = B_R(y)`, `R = j_{ν,1}/√a`.  For a weak eigenfunction `u` of `B` with eigenvalue
`μ < C_N a`, `u ∘ σ_c = u` for every reflection `σ_c` through `y`.  For `μ = C_N a` the same
holds provided `u` is `L²`-orthogonal to the degree-one eigenfunction `Ψ_c`.

Proof: `v = u - u ∘ σ_c` is antisymmetric, so its restrictions to the two half balls lie in their
form domains, whose first eigenvalue is `C_N a`; hence `q(v) ≥ C_N a ‖v‖²`, while `q(v) = μ ‖v‖²`.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Function Set
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

variable {N : ℕ}

lemma opC_neg (y c : RN N) : opC y (-c) = opC y c := by
  simp only [opC, reflC_neg]

/-- Hyperplanes are null. -/
lemma ae_inner_ne_zero (y : RN N) {c : RN N} (hc : c ≠ 0) :
    ∀ᵐ x ∂(volume : Measure (RN N)), ⟪c, x - y⟫ ≠ 0 := by
  set s : AffineSubspace ℝ (RN N) := AffineSubspace.mk' y (ℝ ∙ c)ᗮ
  have hmem : ∀ x, x ∈ s ↔ ⟪c, x - y⟫ = 0 := fun x => by
    rw [AffineSubspace.mem_mk', vsub_eq_sub, Submodule.mem_orthogonal_singleton_iff_inner_right]
  have hs : s ≠ ⊤ := by
    intro h
    have : y + c ∈ s := h ▸ AffineSubspace.mem_top ℝ _ _
    rw [hmem, add_sub_cancel_left, real_inner_self_eq_norm_sq] at this
    exact hc (norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this))
  have h0 := Measure.addHaar_affineSubspace volume s hs
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp h0] with x hx
  exact fun h => hx ((hmem x).mpr h)

/-- Splitting an antisymmetric element of `H₀¹(B)` into its two half-ball parts. -/
lemma antisym_split (hN : 2 ≤ N) {a : ℝ} (ha : 0 < a) (y : RN N) {c : RN N} (hc : c ≠ 0)
    {v : Amb N} (hv : v ∈ H (ball y (annR N a))) (hanti : opC y c v = -v) :
    restrictTo (halfB y (annR N a) c) v ∈ H (halfB y (annR N a) c) ∧
      restrictTo (halfB y (annR N a) (-c)) v ∈ H (halfB y (annR N a) (-c)) ∧
      v = restrictTo (halfB y (annR N a) c) v + restrictTo (halfB y (annR N a) (-c)) v := by
  have hm1 : MeasurableSet (halfB y (annR N a) c) := (isOpen_halfB _ _ _).measurableSet
  have hm2 : MeasurableSet (halfB y (annR N a) (-c)) := (isOpen_halfB _ _ _).measurableSet
  have h2v : v - opC y c v = (2 : ℝ) • v := by rw [hanti, sub_neg_eq_add, two_smul]
  have hc' : -c ≠ 0 := neg_ne_zero.mpr hc
  refine ⟨?_, ?_, ?_⟩
  · have := restrict_antisym hN ha y hc hv
    rw [h2v, restrictTo_smul hm1] at this
    have h := (H _).smul_mem (1 / 2 : ℝ) this
    rwa [smul_smul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul] at h
  · have := restrict_antisym hN ha y hc' hv
    rw [opC_neg, h2v, restrictTo_smul hm2] at this
    have h := (H _).smul_mem (1 / 2 : ℝ) this
    rwa [smul_smul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul] at h
  · obtain ⟨hv1, hv2⟩ := vanish_off_of_mem_H isOpen_ball hv
    have hsplit : ∀ x, ⟪c, x - y⟫ ≠ 0 → x ∈ ball y (annR N a) →
        (x ∈ halfB y (annR N a) c ∧ x ∉ halfB y (annR N a) (-c)) ∨
        (x ∉ halfB y (annR N a) c ∧ x ∈ halfB y (annR N a) (-c)) := by
      intro x hx hxB
      simp only [halfB, mem_inter_iff, mem_setOf_eq, inner_neg_left, neg_pos]
      rcases hx.lt_or_gt with h | h
      · right; exact ⟨fun h' => by linarith [h'.2], hxB, h⟩
      · left; exact ⟨⟨hxB, h⟩, fun h' => by linarith [h'.2]⟩
    have hout : ∀ x, x ∉ ball y (annR N a) →
        x ∉ halfB y (annR N a) c ∧ x ∉ halfB y (annR N a) (-c) := fun x hx =>
      ⟨fun h => hx h.1, fun h => hx h.1⟩
    refine Prod.ext (Lp.ext ?_) (Lp.ext ?_)
    · filter_upwards [Lp.coeFn_add (restrictTo (halfB y (annR N a) c) v).1
        (restrictTo (halfB y (annR N a) (-c)) v).1, restrictTo_fst_ae hm1 v,
        restrictTo_fst_ae hm2 v, hv1, ae_inner_ne_zero y hc] with x e1 e2 e3 e4 e5
      rw [Prod.fst_add, e1, Pi.add_apply, e2, e3]
      by_cases hxB : x ∈ ball y (annR N a)
      · rcases hsplit x e5 hxB with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [indicator_of_mem h1, indicator_of_notMem h2, add_zero]
        · rw [indicator_of_notMem h1, indicator_of_mem h2, zero_add]
      · rw [indicator_of_notMem (hout x hxB).1, indicator_of_notMem (hout x hxB).2, e4 hxB]
        simp
    · filter_upwards [Lp.coeFn_add (restrictTo (halfB y (annR N a) c) v).2
        (restrictTo (halfB y (annR N a) (-c)) v).2, restrictTo_snd_ae hm1 v,
        restrictTo_snd_ae hm2 v, hv2, ae_inner_ne_zero y hc] with x e1 e2 e3 e4 e5
      rw [Prod.snd_add, e1, Pi.add_apply, e2, e3]
      by_cases hxB : x ∈ ball y (annR N a)
      · rcases hsplit x e5 hxB with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [indicator_of_mem h1, indicator_of_notMem h2, add_zero]
        · rw [indicator_of_notMem h1, indicator_of_mem h2, zero_add]
      · rw [indicator_of_notMem (hout x hxB).1, indicator_of_notMem (hout x hxB).2, e4 hxB]
        simp

lemma halfB_disjoint (y : RN N) (r : ℝ) (c : RN N) : Disjoint (halfB y r c) (halfB y r (-c)) := by
  rw [Set.disjoint_left]
  rintro x ⟨-, h1⟩ ⟨-, h2⟩
  simp only [mem_setOf_eq, inner_neg_left, neg_pos] at h1 h2
  linarith

/-- Basic data for an eigenfunction `u` and the antisymmetric part `v = u - u ∘ σ_c`. -/
lemma antisym_part_bound (hN : 2 ≤ N) {a : ℝ} (ha : 0 < a) (y : RN N) {c : RN N} (hc : c ≠ 0)
    {u : Amb N} {μ : ℝ} (hu : u ∈ H (ball y (annR N a)))
    (hw : ∀ φ ∈ H (ball y (annR N a)), qf u φ = μ * l2 u φ) :
    let v := u - opC y c u
    let r1 := restrictTo (halfB y (annR N a) c) v
    let r2 := restrictTo (halfB y (annR N a) (-c)) v
    r1 ∈ H (halfB y (annR N a) c) ∧ r2 ∈ H (halfB y (annR N a) (-c)) ∧
    v ∈ H (ball y (annR N a)) ∧
    μ * l2 v v = qf r1 r1 + qf r2 r2 ∧ l2 v v = l2 r1 r1 + l2 r2 r2 ∧
    CN N * a * l2 r1 r1 ≤ qf r1 r1 ∧ CN N * a * l2 r2 r2 ≤ qf r2 r2 := by
  intro v r1 r2
  have hvH : v ∈ H (ball y (annR N a)) := (H _).sub_mem hu (isoOp_mem_H _ y _ hu)
  have hvw : ∀ φ ∈ H (ball y (annR N a)), qf v φ = μ * l2 v φ := by
    intro φ hφ
    have e2 := isoOp_weak (reflC c) (reflC_reflC c) y (annR N a) hw φ hφ
    simp only [v, qf_sub_left, l2_sub_left, hw φ hφ, e2]
    ring
  have hanti : opC y c v = -v := by
    simp only [v, map_sub, opC_opC, neg_sub]
  obtain ⟨hr1, hr2, hsum⟩ := antisym_split hN ha y hc hvH hanti
  have hd := halfB_disjoint y (annR N a) c
  obtain ⟨hq12, hl12⟩ := orthogonal_of_disjoint (isOpen_halfB _ _ _).measurableSet
    (isOpen_halfB _ _ _).measurableSet hd hr1 hr2
  have hq21 : qf r2 r1 = 0 := by rw [qf_comm]; exact hq12
  have hl21 : l2 r2 r1 = 0 := by rw [l2_comm]; exact hl12
  have hc' : -c ≠ 0 := neg_ne_zero.mpr hc
  have e1 := (half_first_eigen hN ha y hc).1
  have e2 := (half_first_eigen hN ha y hc').1
  have hsum' : v = r1 + r2 := hsum
  refine ⟨hr1, hr2, hvH, ?_, ?_, ?_, ?_⟩
  · rw [← hvw v hvH]
    calc qf v v = qf (r1 + r2) (r1 + r2) := congrArg₂ _ hsum' hsum'
      _ = _ := by
        rw [qf_add_left, qf_add_right, qf_add_right, (hq12 : qf r1 r2 = 0),
          (hq21 : qf r2 r1 = 0)]; ring
  · calc l2 v v = l2 (r1 + r2) (r1 + r2) := congrArg₂ _ hsum' hsum'
      _ = _ := by
        rw [l2_add_left, l2_add_right, l2_add_right, (hl12 : l2 r1 r2 = 0),
          (hl21 : l2 r2 r1 = 0)]; ring
  · have := qf_ge_lam1 hr1; rwa [e1] at this
  · have := qf_ge_lam1 hr2; rwa [e2] at this

/-- **Low eigenfunctions are reflection symmetric.** -/
theorem eigen_sym_of_lt (hN : 2 ≤ N) {a : ℝ} (ha : 0 < a) (y : RN N) {c : RN N} (hc : c ≠ 0)
    {u : Amb N} {μ : ℝ} (hu : u ∈ H (ball y (annR N a)))
    (hw : ∀ φ ∈ H (ball y (annR N a)), qf u φ = μ * l2 u φ) (hμ : μ < CN N * a) :
    opC y c u = u := by
  obtain ⟨hr1, hr2, hvH, hq, hl, h1, h2⟩ := antisym_part_bound hN ha y hc hu hw
  have hnn := l2_self_nonneg (u - opC y c u)
  have : l2 (u - opC y c u) (u - opC y c u) = 0 := by
    by_contra hne
    have hpos : 0 < l2 (u - opC y c u) (u - opC y c u) := lt_of_le_of_ne hnn (Ne.symm hne)
    have : CN N * a * l2 (u - opC y c u) (u - opC y c u) ≤ μ * l2 (u - opC y c u) (u - opC y c u) := by
      rw [hq, hl]; linarith
    nlinarith
  exact (sub_eq_zero.mp (eq_zero_of_l2_self_eq_zero hvH this)).symm

/-- The `σ_c`-image of the half-ball eigenfunction: `(Ψ_c 1_{B⁺}) ∘ σ_c = Ψ_c 1_{B⁺} - Ψ_c 1_B`. -/
lemma indicator_half_sigC (y : RN N) (r : ℝ) (c : RN N) (F : RN N → ℝ)
    (hF : ∀ x, F (sigC y c x) = -F x) (hF0 : ∀ x, ⟪c, x - y⟫ = 0 → F x = 0) (x : RN N) :
    (halfB y r c).indicator F (sigC y c x) =
      (halfB y r c).indicator F x - (ball y r).indicator F x := by
  have hσB : sigC y c x ∈ ball y r ↔ x ∈ ball y r := isoMap_mem_ball_iff _ _ _ _
  by_cases hxB : x ∈ ball y r
  · rcases lt_trichotomy 0 ⟪c, x - y⟫ with h | h | h
    · have hx : x ∈ halfB y r c := ⟨hxB, h⟩
      have hσ : sigC y c x ∉ halfB y r c := fun h' => by
        have := h'.2; simp only [mem_setOf_eq, inner_sigC] at this; linarith
      rw [indicator_of_notMem hσ, indicator_of_mem hx, indicator_of_mem hxB, sub_self]
    · have hx : x ∉ halfB y r c := fun h' => by have := h'.2; simp only [mem_setOf_eq] at this; linarith
      have hσ : sigC y c x ∉ halfB y r c := fun h' => by
        have := h'.2; simp only [mem_setOf_eq, inner_sigC] at this; linarith
      rw [indicator_of_notMem hσ, indicator_of_notMem hx, indicator_of_mem hxB, hF0 x h.symm]
      ring
    · have hx : x ∉ halfB y r c := fun h' => by have := h'.2; simp only [mem_setOf_eq] at this; linarith
      have hσ : sigC y c x ∈ halfB y r c := ⟨hσB.mpr hxB, by simp only [mem_setOf_eq, inner_sigC]; linarith⟩
      rw [indicator_of_mem hσ, indicator_of_notMem hx, indicator_of_mem hxB, hF]
      ring
  · have hx : x ∉ halfB y r c := fun h' => hxB h'.1
    have hσ : sigC y c x ∉ halfB y r c := fun h' => hxB (hσB.mp h'.1)
    rw [indicator_of_notMem hσ, indicator_of_notMem hx, indicator_of_notMem hxB, sub_zero]

/-- In the borderline case `μ = C_N a`, orthogonality to `Ψ_c` kills the half-ball part. -/
lemma half_part_zero (hN : 2 ≤ N) {a : ℝ} (ha : 0 < a) (y : RN N) {c : RN N} (hc : c ≠ 0)
    {u : Amb N}
    {w : Amb N} (hw1 : (w.1 : RN N → ℝ) =ᵐ[volume] (ball y (annR N a)).indicator (deg1Fun N a y c))
    (horth : l2 u w = 0)
    (r1 : Amb N) (hr1 : r1 ∈ H (halfB y (annR N a) c))
    (hr1def : r1 = restrictTo (halfB y (annR N a) c) (u - opC y c u))
    (heq : qf r1 r1 = CN N * a * l2 r1 r1) : r1 = 0 := by
  have hR := annR_pos hN ha
  have hD := isDomain_halfB (y := y) hR hc
  obtain ⟨e1, wh, hwh, hwh1⟩ := half_first_eigen hN ha y hc
  by_cases h0 : r1 = 0
  · exact h0
  exfalso
  have hE : IsEigenfunction (halfB y (annR N a) c) r1 (eigenvalue (halfB y (annR N a) c) 1) :=
    isEigenfunction_of_rayleigh_min hr1 h0 (by rw [e1]; exact heq)
  have hE' : IsEigenfunction (halfB y (annR N a) c) wh (eigenvalue (halfB y (annR N a) c) 1) := by
    rw [e1]; exact hwh
  obtain ⟨k, hk⟩ := (ground_state hN hD).1 wh r1 hE' hE
  -- `l2 (u - σu) wh = l2 u w = 0`
  have hm := (isOpen_halfB y (annR N a) c).measurableSet
  have hlr : l2 r1 wh = l2 (u - opC y c u) wh := by
    rw [hr1def]
    obtain ⟨-, hl⟩ := forms_eq_of_agree hm (H_le_vanishOn _ hwh.1) (u := u - opC y c u)
      (w := restrictTo (halfB y (annR N a) c) (u - opC y c u))
      (by rw [EventuallyEq, ae_restrict_iff' hm]
          filter_upwards [restrictTo_fst_ae hm (u - opC y c u)] with x e hx
          rw [e, indicator_of_mem hx])
      (by rw [EventuallyEq, ae_restrict_iff' hm]
          filter_upwards [restrictTo_snd_ae hm (u - opC y c u)] with x e hx
          rw [e, indicator_of_mem hx])
    exact hl
  have hσ : l2 (opC y c u) wh = l2 u (opC y c wh) := by
    have h := l2_isoOp (reflC c) y (opC y c u) wh
    change l2 (opC y c (opC y c u)) (opC y c wh) = _ at h
    rw [opC_opC] at h
    exact h.symm
  have hfst : (opC y c wh).1 = (wh - w).1 := by
    refine Lp.ext ?_
    have hq := (measurePreserving_isoMap (reflC c) y).quasiMeasurePreserving.ae_eq_comp hwh1
    filter_upwards [isoOp_fst_ae (reflC c) y wh, hq, Lp.coeFn_sub wh.1 w.1, hwh1, hw1]
      with x e1 e2 e3 e4 e5
    rw [e1, Prod.fst_sub, e3, Pi.sub_apply, e4, e5]
    simp only [Function.comp_apply] at e2
    rw [e2]
    exact indicator_half_sigC y (annR N a) c _ (deg1Fun_sigC N a y c)
      (fun x hx => by simp [deg1Fun, hx]) x
  have hσ' : l2 u (opC y c wh) = l2 u wh - l2 u w := by
    rw [l2, hfst, ← l2_sub_right]; rfl
  have hkey : l2 r1 wh = 0 := by
    rw [hlr, l2_sub_left, hσ, hσ', horth]; ring
  rw [hk, l2_smul_left] at hkey
  have hpos := l2_self_pos hwh.1 hwh.2.1
  have hk0 : k = 0 := by
    rcases mul_eq_zero.mp hkey with h | h
    · exact h
    · exact absurd h hpos.ne'
  exact h0 (by rw [hk, hk0, zero_smul])

/-- **Eigenfunctions with eigenvalue `C_N a` orthogonal to `Ψ_c` are `σ_c`-symmetric.** -/
theorem eigen_sym_of_orth (hN : 2 ≤ N) {a : ℝ} (ha : 0 < a) (y : RN N) {c : RN N} (hc : c ≠ 0)
    {u : Amb N} (hu : u ∈ H (ball y (annR N a)))
    (hw : ∀ φ ∈ H (ball y (annR N a)), qf u φ = CN N * a * l2 u φ)
    {w : Amb N} (hw1 : (w.1 : RN N → ℝ) =ᵐ[volume] (ball y (annR N a)).indicator (deg1Fun N a y c))
    (horth : l2 u w = 0) : opC y c u = u := by
  obtain ⟨hr1, hr2, hvH, hq, hl, h1, h2⟩ := antisym_part_bound hN ha y hc hu hw
  set r1 := restrictTo (halfB y (annR N a) c) (u - opC y c u) with hr1def
  set r2 := restrictTo (halfB y (annR N a) (-c)) (u - opC y c u) with hr2def
  have heq1 : qf r1 r1 = CN N * a * l2 r1 r1 := by
    have : CN N * a * (l2 r1 r1 + l2 r2 r2) = qf r1 r1 + qf r2 r2 := by rw [← hl, hq]
    linarith
  have heq2 : qf r2 r2 = CN N * a * l2 r2 r2 := by
    have : CN N * a * (l2 r1 r1 + l2 r2 r2) = qf r1 r1 + qf r2 r2 := by rw [← hl, hq]
    linarith
  have hz1 := half_part_zero hN ha y hc hw1 horth r1 hr1 hr1def heq1
  have hc' : -c ≠ 0 := neg_ne_zero.mpr hc
  have hw1' : ((-w).1 : RN N → ℝ) =ᵐ[volume]
      (ball y (annR N a)).indicator (deg1Fun N a y (-c)) := by
    filter_upwards [Lp.coeFn_neg w.1, hw1] with x e1 e2
    rw [Prod.fst_neg, e1, Pi.neg_apply, e2]
    by_cases hx : x ∈ ball y (annR N a)
    · simp [indicator_of_mem hx, deg1Fun, inner_neg_left]
    · simp [indicator_of_notMem hx]
  have horth' : l2 u (-w) = 0 := by rw [l2_neg_right, horth, neg_zero]
  have hz2 : r2 = 0 := by
    refine half_part_zero hN ha y hc' hw1' horth' r2 (by simpa using hr2) ?_ heq2
    rw [hr2def, opC_neg]
  have : l2 (u - opC y c u) (u - opC y c u) = 0 := by
    rw [hl, hz1, hz2]; simp
  exact (sub_eq_zero.mp (eq_zero_of_l2_self_eq_zero hvH this)).symm

end FourthRatio

end
