module

public import RequestProject.MainSection

/-!
# Negative sections and the projected tangent line field (Lemmas 5.5–5.6)

The local negative sections `φᵢ` are glued with a partition of unity.  Instead of building the
two-sheeted cover explicitly we glue the rank-one projections: with the local sign functions
`sᵢⱼ = -sgn 𝔟(φᵢ, φⱼ)` (locally constant by the cone lemma) and `wᵢ = A_u(Pφᵢ)`,
`Π(u) x = (∑ᵢⱼ ρᵢρⱼ sᵢⱼ ⟨wⱼ,x⟩ wᵢ) / (∑ᵢⱼ ρᵢρⱼ sᵢⱼ ⟨wᵢ,wⱼ⟩)`
is the orthogonal projection onto the line spanned by `w = ∑ ρᵢσᵢ wᵢ`, where `σᵢ` is a choice of
signs over the point (a lift to the double cover).
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Function
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

variable {N : ℕ}

lemma bshift_sum_sum {ι : Type*} (s : Finset ι) (γ : ℝ) (a : ι → ℝ) (v : ι → Amb N) :
    bshift γ (∑ i ∈ s, a i • v i) (∑ j ∈ s, a j • v j) =
      ∑ i ∈ s, ∑ j ∈ s, a i * a j * bshift γ (v i) (v j) := by
  simp only [bshift, qf_sum_left, qf_sum_right, l2_sum_left, l2_sum_right, qf_smul_left,
    qf_smul_right, l2_smul_left, l2_smul_right, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [qf_comm (v j) (v i), l2_comm (v j) (v i)]
  ring

lemma bshift_sum_left {ι : Type*} (s : Finset ι) (γ : ℝ) (a : ι → ℝ) (v : ι → Amb N)
    (w : Amb N) : bshift γ (∑ i ∈ s, a i • v i) w = ∑ i ∈ s, a i * bshift γ (v i) w := by
  simp only [bshift, qf_sum_left, l2_sum_left, qf_smul_left, l2_smul_left, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

lemma sum_sum_smul_eq {ι : Type*} (s : Finset ι) (c : ι → ℝ) (w : ι → E4) (x : E4) :
    ∑ i ∈ s, ∑ j ∈ s, (c i * c j * ⟪w j, x⟫) • w i =
      ⟪∑ j ∈ s, c j • w j, x⟫ • ∑ i ∈ s, c i • w i := by
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_smul, smul_smul, sum_inner]
  congr 1
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_left, RCLike.conj_to_real]
  ring

lemma sum_sum_inner_eq {ι : Type*} (s : Finset ι) (c : ι → ℝ) (w : ι → E4) :
    ∑ i ∈ s, ∑ j ∈ s, c i * c j * ⟪w i, w j⟫ =
      ⟪∑ i ∈ s, c i • w i, ∑ j ∈ s, c j • w j⟫ := by
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, RCLike.conj_to_real]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [real_inner_comm]
  ring

namespace Setup

variable (S : Setup N)

/-- The local conditions satisfied by a local section datum `η` at `u`. -/
def Loc (η : Amb N) (u : E4) : Prop :=
  η ∈ H (posSign S.Ω (S.fU u)) ∧ S.bpp u < 0 ∧ S.gq η u ^ 2 < S.bpp u * bshift S.b η η

lemma loc_phi_mem {η : Amb N} {u : E4} (h : S.Loc η u) : S.phi η u ∈ S.Wsub u :=
  S.mem_Wsub.mpr ⟨S.phi_mem h.1, S.bshift_phi_pp h.1 h.2.1.ne⟩

lemma loc_phi_neg {η : Amb N} {u : E4} (h : S.Loc η u) :
    bshift S.b (S.phi η u) (S.phi η u) < 0 :=
  S.bshift_phi_self_neg h.1 h.2.1 h.2.2

lemma loc_Bf_ne_zero {η ζ : Amb N} {u : E4} (hg : S.Good u) (h1 : S.Loc η u)
    (h2 : S.Loc ζ u) : S.Bf η ζ u ≠ 0 := by
  have hX := S.negIndex_Wsub hg (S.loc_phi_mem h1) (S.loc_phi_neg h1)
  have := cone_pair_ne_zero (B := bform S.b) (fun x y => bshift_comm _ x y) hX (S.loc_phi_mem h1) (S.loc_phi_mem h2)
    (S.loc_phi_neg h1) (S.loc_phi_neg h2)
  rwa [bform_apply, S.bshift_phi_phi h1.1 h2.1] at this

lemma loc_Bf_trans {η ζ θ : Amb N} {u : E4} (hg : S.Good u) (h1 : S.Loc η u)
    (h2 : S.Loc ζ u) (h3 : S.Loc θ u) {s t : ℝ} (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1)
    (h12 : s * S.Bf ζ η u < 0) (h23 : t * S.Bf η θ u < 0) :
    s * t * S.Bf ζ θ u < 0 := by
  have hX := S.negIndex_Wsub hg (S.loc_phi_mem h1) (S.loc_phi_neg h1)
  have hsm : ∀ {r : ℝ} {φ : Amb N}, (r = 1 ∨ r = -1) → φ ∈ S.Wsub u →
      bshift S.b φ φ < 0 → r • φ ∈ S.Wsub u ∧ bshift S.b (r • φ) (r • φ) < 0 := by
    intro r φ hr hφ hφφ
    refine ⟨Submodule.smul_mem _ r hφ, ?_⟩
    simp only [bshift, qf_smul_left, qf_smul_right, l2_smul_left, l2_smul_right] at hφφ ⊢
    rcases hr with rfl | rfl <;> nlinarith
  obtain ⟨hA, hAA⟩ := hsm hs (S.loc_phi_mem h2) (S.loc_phi_neg h2)
  obtain ⟨hC, hCC⟩ := hsm ht (S.loc_phi_mem h3) (S.loc_phi_neg h3)
  have hAB : bform S.b (s • S.phi ζ u) (S.phi η u) < 0 := by
    rw [bform_apply]
    simp only [bshift, qf_smul_left, l2_smul_left]
    have := S.bshift_phi_phi h2.1 h1.1
    simp only [bshift] at this
    rw [← this] at h12
    linarith
  have hBC : bform S.b (S.phi η u) (t • S.phi θ u) < 0 := by
    rw [bform_apply]
    simp only [bshift, qf_smul_right, l2_smul_right]
    have := S.bshift_phi_phi h1.1 h3.1
    simp only [bshift] at this
    rw [← this] at h23
    linarith
  have := cone_trans (B := bform S.b) (fun x y => bshift_comm _ x y) hX hA (S.loc_phi_mem h1) hC hAA
    (S.loc_phi_neg h1) hCC hAB hBC
  rw [bform_apply] at this
  have e := S.bshift_phi_phi h2.1 h3.1
  simp only [bshift, qf_smul_left, qf_smul_right, l2_smul_left, l2_smul_right] at this e ⊢
  rw [← e]
  linarith

/-! ### The glued line field -/

variable {ι : Type*} [Fintype ι] (η : ι → Amb N)

/-- `wᵢ(u) = A_u(Pηᵢ) = A_u(Pφᵢ(u))`. -/
def wv (i : ι) (u : E4) : E4 := S.Amap u (S.Pc (η i))

/-- The sign `-sgn 𝔟(φᵢ, φⱼ)`. -/
def sg (i j : ι) (u : E4) : ℝ := -S.Bf (η i) (η j) u / |S.Bf (η i) (η j) u|

variable {M : Set E4} (ρ : PartitionOfUnity ι E4 M)

/-- The coefficients `ρᵢρⱼ sᵢⱼ`. -/
def coef (i j : ι) (u : E4) : ℝ := ρ i u * ρ j u * S.sg η i j u

/-- `∑ᵢⱼ ρᵢρⱼ sᵢⱼ ⟨wᵢ, wⱼ⟩ = |w|²`. -/
def tau (u : E4) : ℝ := ∑ i, ∑ j, S.coef η ρ i j u * ⟪S.wv η i u, S.wv η j u⟫

/-- The glued projection. -/
def PiF (u x : E4) : E4 :=
  (S.tau η ρ u)⁻¹ • ∑ i, ∑ j, (S.coef η ρ i j u * ⟪S.wv η j u, x⟫) • S.wv η i u

variable {V : ι → Set E4} (hloc : ∀ i, ∀ u ∈ V i, S.Loc (η i) u) (hsub : ρ.IsSubordinate V)
  (hMg : ∀ u ∈ M, ‖u‖ = 1 ∧ S.Good u)

omit [Fintype ι] in
include hloc hsub in
lemma loc_of_ne_zero {i : ι} {u : E4} (h : ρ i u ≠ 0) : S.Loc (η i) u :=
  hloc i u (hsub i (subset_tsupport _ h))

lemma sg_of_sign {x s : ℝ} (hs : s = 1 ∨ s = -1) (h : s * x < 0) : -x / |x| = s := by
  rcases hs with rfl | rfl
  · have hx : x < 0 := by linarith
    rw [abs_of_neg hx, neg_div_neg_eq, div_self hx.ne]
  · have hx : 0 < x := by linarith
    rw [abs_of_pos hx, neg_div, div_self hx.ne']

include hloc hsub hMg in
/-- **Pointwise structure (choice of a lift).** Over every `u ∈ M` there are signs `σᵢ` with
`ρᵢρⱼsᵢⱼ = ρᵢρⱼσᵢσⱼ`, and the glued vector `w = ∑ ρᵢσᵢwᵢ` is nonzero. -/
lemma pointwise {u : E4} (hu : u ∈ M) :
    ∃ σ : ι → ℝ, (∀ i j, S.coef η ρ i j u = (ρ i u * σ i) * (ρ j u * σ j)) ∧
      ∑ i, (ρ i u * σ i) • S.wv η i u ≠ 0 := by
  classical
  obtain ⟨hu1, hg⟩ := hMg u hu
  have hsum : ∑ i, ρ i u = 1 := by
    rw [← finsum_eq_sum_of_fintype]; exact ρ.sum_eq_one hu
  obtain ⟨i0, hi0⟩ : ∃ i0, ρ i0 u ≠ 0 := by
    by_contra h
    push_neg at h
    simp [h] at hsum
  have hL0 := S.loc_of_ne_zero η ρ hloc hsub hi0
  let σ : ι → ℝ := fun i => if ρ i u = 0 then 1 else S.sg η i0 i u
  have hσpm : ∀ i, σ i = 1 ∨ σ i = -1 := by
    intro i
    by_cases hi : ρ i u = 0
    · simp [σ, hi]
    · have hB := S.loc_Bf_ne_zero hg hL0 (S.loc_of_ne_zero η ρ hloc hsub hi)
      simp only [σ, hi, if_false, sg]
      rcases lt_or_gt_of_ne hB with h | h
      · left; rw [abs_of_neg h, neg_div_neg_eq, div_self h.ne]
      · right; rw [abs_of_pos h, neg_div, div_self h.ne']
  have hσB : ∀ i, ρ i u ≠ 0 → σ i * S.Bf (η i0) (η i) u < 0 := by
    intro i hi
    have hB := S.loc_Bf_ne_zero hg hL0 (S.loc_of_ne_zero η ρ hloc hsub hi)
    simp only [σ, hi, if_false, sg]
    rw [div_mul_eq_mul_div, neg_mul, neg_div, neg_neg_iff_pos, ← sq, ← sq_abs]
    exact div_pos (pow_pos (abs_pos.mpr hB) 2) (abs_pos.mpr hB)
  have hpair : ∀ i j, ρ i u ≠ 0 → ρ j u ≠ 0 → σ i * σ j * S.Bf (η i) (η j) u < 0 := by
    intro i j hi hj
    have hLi := S.loc_of_ne_zero η ρ hloc hsub hi
    have hLj := S.loc_of_ne_zero η ρ hloc hsub hj
    refine S.loc_Bf_trans hg hL0 hLi hLj (hσpm i) (hσpm j) ?_ (hσB j hj)
    have h1 := hσB i hi
    have hsym : S.Bf (η i) (η i0) u = S.Bf (η i0) (η i) u := by
      rw [← S.bshift_phi_phi hLi.1 hL0.1, ← S.bshift_phi_phi hL0.1 hLi.1, bshift_comm]
    rw [hsym]; exact h1
  refine ⟨σ, fun i j => ?_, ?_⟩
  · simp only [coef]
    by_cases hi : ρ i u = 0
    · simp [hi]
    by_cases hj : ρ j u = 0
    · simp [hj]
    rw [sg, sg_of_sign (by rcases hσpm i with h | h <;> rcases hσpm j with h' | h' <;>
      simp [h, h']) (hpair i j hi hj)]
    ring
  · -- the glued negative section
    set c : ι → ℝ := fun i => ρ i u * σ i
    set φ : Amb N := ∑ i, c i • S.phi (η i) u
    have hterm : ∀ i, c i = 0 ∨ S.Loc (η i) u := by
      intro i
      by_cases hi : ρ i u = 0
      · left; simp [c, hi]
      · right; exact S.loc_of_ne_zero η ρ hloc hsub hi
    have hφmem : φ ∈ H (posSign S.Ω (S.fU u)) := by
      refine Submodule.sum_mem _ fun i _ => ?_
      rcases hterm i with h | h
      · simp [h]
      · exact Submodule.smul_mem _ _ (S.phi_mem h.1)
    have hφp : bshift S.b φ (posPart (S.U u)) = 0 := by
      rw [bshift_sum_left]
      refine Finset.sum_eq_zero fun i _ => ?_
      rcases hterm i with h | h
      · simp [h]
      · rw [S.bshift_phi_pp h.1 h.2.1.ne, mul_zero]
    have hφφ : bshift S.b φ φ < 0 := by
      rw [bshift_sum_sum]
      have hle : ∀ i j, c i * c j * bshift S.b (S.phi (η i) u) (S.phi (η j) u) ≤ 0 := by
        intro i j
        by_cases hi : ρ i u = 0
        · simp [c, hi]
        by_cases hj : ρ j u = 0
        · simp [c, hj]
        have hLi := S.loc_of_ne_zero η ρ hloc hsub hi
        have hLj := S.loc_of_ne_zero η ρ hloc hsub hj
        rw [S.bshift_phi_phi hLi.1 hLj.1]
        have hpos : 0 ≤ ρ i u * ρ j u := mul_nonneg (ρ.nonneg i u) (ρ.nonneg j u)
        have := hpair i j hi hj
        have e : c i * c j * S.Bf (η i) (η j) u =
            (ρ i u * ρ j u) * (σ i * σ j * S.Bf (η i) (η j) u) := by simp only [c]; ring
        rw [e]
        exact mul_nonpos_of_nonneg_of_nonpos hpos this.le
      have hlt : c i0 * c i0 * bshift S.b (S.phi (η i0) u) (S.phi (η i0) u) < 0 := by
        have hc : c i0 ≠ 0 := by
          simp only [c]
          exact mul_ne_zero hi0 (by rcases hσpm i0 with h | h <;> simp [h])
        exact mul_neg_of_pos_of_neg (mul_self_pos.mpr hc) (S.loc_phi_neg hL0)
      calc ∑ i, ∑ j, c i * c j * bshift S.b (S.phi (η i) u) (S.phi (η j) u)
          < ∑ _i : ι, (0 : ℝ) := by
            refine Finset.sum_lt_sum (fun i _ => Finset.sum_nonpos fun j _ => hle i j)
              ⟨i0, Finset.mem_univ _, ?_⟩
            calc ∑ j, c i0 * c j * bshift S.b (S.phi (η i0) u) (S.phi (η j) u)
                < ∑ _j : ι, (0 : ℝ) :=
                  Finset.sum_lt_sum (fun j _ => hle i0 j) ⟨i0, Finset.mem_univ _, hlt⟩
              _ = 0 := by simp
        _ = 0 := by simp
    have hne := S.Amap_Pc_ne_zero hu1 hg hφmem hφp hφφ
    have hd := (S.dC_pos hu1 hg).ne'
    have : S.Amap u (S.Pc φ) = ∑ i, c i • S.wv η i u := by
      simp only [φ, map_sum, map_smul, S.Amap_sum, phi, map_sub]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [S.Amap_sub, S.Amap_smul, S.Amap_Pc_posPart hu1 hd, smul_zero, sub_zero, wv]
    rw [← this]
    exact hne

omit [Fintype ι] in
include hloc hsub hMg in
lemma continuousAt_coef {u : E4} (hu : u ∈ M) (i j : ι) :
    ContinuousAt (S.coef η ρ i j) u := by
  by_cases hi : u ∈ V i
  · by_cases hj : u ∈ V j
    · have hg := (hMg u hu).2
      have hLi := hloc i u hi
      have hLj := hloc j u hj
      have hB := S.loc_Bf_ne_zero hg hLi hLj
      have hBc := S.continuousAt_Bf (η i) (η j) hLi.2.1.ne
      exact ((ρ i).continuous.continuousAt.mul (ρ j).continuous.continuousAt).mul
        (hBc.neg.div hBc.abs (abs_ne_zero.mpr hB))
    · have h0 : ρ j =ᶠ[𝓝 u] 0 := notMem_tsupport_iff_eventuallyEq.mp (fun h => hj (hsub j h))
      refine (continuousAt_const (y := (0 : ℝ))).congr ?_
      filter_upwards [h0] with v hv
      simp [coef, hv]
  · have h0 : ρ i =ᶠ[𝓝 u] 0 := notMem_tsupport_iff_eventuallyEq.mp (fun h => hi (hsub i h))
    refine (continuousAt_const (y := (0 : ℝ))).congr ?_
    filter_upwards [h0] with v hv
    simp [coef, hv]

omit [Fintype ι] in
include hMg in
lemma continuousAt_wv {u : E4} (hu : u ∈ M) (i : ι) : ContinuousAt (S.wv η i) u := by
  obtain ⟨hu1, hg⟩ := hMg u hu
  have := S.continuousAt_Amap (S.dC_pos hu1 hg).ne' (S.Pc (η i))
  have hf : ContinuousAt (fun v : E4 => (v, S.Pc (η i))) u :=
    continuousAt_id.prodMk continuousAt_const
  exact ContinuousAt.comp (f := fun v : E4 => (v, S.Pc (η i))) this hf

include hloc hsub hMg in
/-- The glued line field has the required properties. -/
theorem line_field_of_cover :
    ContinuousOn (fun p : E4 × E4 => S.PiF η ρ p.1 p.2) (M ×ˢ Set.univ) ∧
      ∀ u ∈ M, ∃ w : E4, w ≠ 0 ∧ ⟪w, u⟫ = 0 ∧ ⟪w, e4⟫ = 0 ∧
        ∀ x, S.PiF η ρ u x = (⟪w, x⟫ / ⟪w, w⟫) • w := by
  have hid : ∀ u ∈ M, ∃ w : E4, w ≠ 0 ∧ ⟪w, u⟫ = 0 ∧ ⟪w, e4⟫ = 0 ∧
      S.tau η ρ u = ⟪w, w⟫ ∧ ∀ x, S.PiF η ρ u x = (⟪w, x⟫ / ⟪w, w⟫) • w := by
    intro u hu
    obtain ⟨hu1, hg⟩ := hMg u hu
    have hd := (S.dC_pos hu1 hg).ne'
    obtain ⟨σ, hcoef, hw0⟩ := S.pointwise η ρ hloc hsub hMg hu
    set w := ∑ i, (ρ i u * σ i) • S.wv η i u
    have htau : S.tau η ρ u = ⟪w, w⟫ := by
      simp only [tau, hcoef]
      exact sum_sum_inner_eq _ _ _
    refine ⟨w, hw0, ?_, ?_, htau, fun x => ?_⟩
    · simp only [w, sum_inner, inner_smul_left, wv, S.Amap_inner_u hu1, mul_zero,
        Finset.sum_const_zero]
    · simp only [w, sum_inner, inner_smul_left, wv, S.Amap_inner_e hd, mul_zero,
        Finset.sum_const_zero]
    · simp only [PiF, hcoef, htau]
      rw [sum_sum_smul_eq, smul_smul, div_eq_inv_mul]
  refine ⟨?_, fun u hu => ?_⟩
  · intro p hp
    obtain ⟨hu, -⟩ := hp
    obtain ⟨w, hw0, -, -, htau, -⟩ := hid p.1 hu
    have htau0 : S.tau η ρ p.1 ≠ 0 := by
      rw [htau]; exact (real_inner_self_pos.mpr hw0).ne'
    have hc : ∀ i j, ContinuousAt (fun q : E4 × E4 => S.coef η ρ i j q.1) p := fun i j =>
      (S.continuousAt_coef η ρ hloc hsub hMg hu i j).comp continuousAt_fst
    have hw : ∀ i, ContinuousAt (fun q : E4 × E4 => S.wv η i q.1) p := fun i =>
      (S.continuousAt_wv η hMg hu i).comp continuousAt_fst
    have htc : ContinuousAt (fun q : E4 × E4 => S.tau η ρ q.1) p := by
      simp only [tau]
      exact tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ =>
        (hc i j).mul ((hw i).inner (hw j))
    refine ContinuousAt.continuousWithinAt ?_
    simp only [PiF]
    refine (htc.inv₀ htau0).smul ?_
    exact tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ =>
      ((hc i j).mul ((hw j).inner continuousAt_snd)).smul (hw i)
  · obtain ⟨w, hw0, h1, h2, -, h3⟩ := hid u hu
    exact ⟨w, hw0, h1, h2, h3⟩

end Setup

namespace Setup

variable (S : Setup N)

/-- **Lemmas 5.5–5.6 (negative section and nonvanishing projected tangent vector), in the
form of a line field.** Over every compact `M ⊆ 𝒪 ∩ 𝕊(S)` there is a continuous line field
`u ↦ ℝ w(u)` with `0 ≠ w(u) ⊥ u, e`. -/
theorem lemma_line_field {O : Set E4} (hgood : ∀ c ∈ O ∩ sphere 0 1, S.Good c)
    {M : Set E4} (hM : M ⊆ O ∩ sphere 0 1) (hMc : IsCompact M) :
    ∃ Pi : E4 → E4 → E4, ContinuousOn (fun p : E4 × E4 => Pi p.1 p.2) (M ×ˢ Set.univ) ∧
      ∀ u ∈ M, ∃ w : E4, w ≠ 0 ∧ ⟪w, u⟫ = 0 ∧ ⟪w, e4⟫ = 0 ∧
        ∀ x, Pi u x = (⟪w, x⟫ / ⟪w, w⟫) • w := by
  have hMg : ∀ u ∈ M, ‖u‖ = 1 ∧ S.Good u := fun u hu =>
    ⟨by simpa using (hM hu).2, hgood u (hM hu)⟩
  have hex := fun u0 : M => S.exists_local_section (hMg u0 u0.2).2
  choose η V hVo hu0V hloc using hex
  obtain ⟨t, ht⟩ := hMc.elim_finite_subcover (fun u0 : M => V u0) (fun u0 => hVo u0)
    (fun u hu => Set.mem_iUnion.mpr ⟨⟨u, hu⟩, hu0V _⟩)
  have hcover : M ⊆ ⋃ i : t, V i.1 := by
    intro u hu
    obtain ⟨i, hi, hui⟩ := Set.mem_iUnion₂.mp (ht hu)
    exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hui⟩
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate hMc.isClosed (fun i : t => V i.1)
    (fun i => hVo i.1) hcover
  exact ⟨S.PiF (fun i : t => η i.1) ρ,
    S.line_field_of_cover (fun i : t => η i.1) ρ (V := fun i : t => V i.1)
      (fun i u hu => hloc i.1 u hu) hρ hMg⟩

end Setup

end FourthRatio

end
