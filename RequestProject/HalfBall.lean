module

public import RequestProject.BallDegreeOne
public import RequestProject.Reflection
public import RequestProject.Nodal

/-!
# Half balls and antisymmetric functions

For `c ≠ 0` let `σ_c` be the reflection of `ℝ^N` in the hyperplane through `y` orthogonal to `c`
and `B⁺ = B_R(y) ∩ {⟨c, x - y⟩ > 0}` the corresponding half ball (`R = j_{ν,1}/√a`).

* The degree-one eigenfunction `Ψ_c = ⟨c, x - y⟩ g(|x - y|²)`, restricted to `B⁺`, is a positive
  eigenfunction of `B⁺`, so `λ₁(B⁺) = C_N a`.
* If `v ∈ H₀¹(B)`, then the restriction of `v - v ∘ σ_c` to `B⁺` lies in `H₀¹(B⁺)`.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Function Set
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

variable {N : ℕ}

/-! ### The reflection `σ_c` -/

/-- Linear reflection in the hyperplane orthogonal to `c`. -/
def reflC (c : RN N) : RN N ≃ₗᵢ[ℝ] RN N := (ℝ ∙ c)ᗮ.reflection

lemma reflC_reflC (c v : RN N) : reflC c (reflC c v) = v :=
  Submodule.reflection_reflection _ _

lemma reflC_apply (c v : RN N) : reflC c v = v - (2 * (⟪c, v⟫ / ‖c‖ ^ 2)) • c := by
  rw [reflC, Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply]
  simp only [RCLike.ofReal_real_eq_id, id]
  rw [neg_sub, two_nsmul, two_mul, add_smul]

lemma inner_reflC (c v : RN N) : ⟪c, reflC c v⟫ = -⟪c, v⟫ := by
  rw [reflC_apply, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq]
  by_cases hc : c = 0
  · simp [hc]
  have : ‖c‖ ^ 2 ≠ 0 := by positivity
  field_simp
  ring

lemma reflC_neg (c : RN N) : reflC (-c) = reflC c := by
  ext v
  simp [reflC_apply, neg_div]

/-- The reflection `σ_c` through `y`. -/
abbrev sigC (y c : RN N) : RN N → RN N := isoMap (reflC c) y

/-- The action of `σ_c` on pairs. -/
abbrev opC (y c : RN N) : Amb N →L[ℝ] Amb N := isoOp (reflC c) y

lemma sigC_sigC (y c x : RN N) : sigC y c (sigC y c x) = x := by
  simp [isoMap, reflC_reflC]

lemma inner_sigC (y c x : RN N) : ⟪c, sigC y c x - y⟫ = -⟪c, x - y⟫ := by
  rw [isoMap_sub, inner_reflC]

lemma norm_sigC (y c x : RN N) : ‖sigC y c x - y‖ = ‖x - y‖ := norm_isoMap_sub _ _ _

lemma sub_sigC (y c x : RN N) :
    x - sigC y c x = (2 * (⟪c, x - y⟫ / ‖c‖ ^ 2)) • c := by
  have : sigC y c x = y + reflC c (x - y) := rfl
  rw [this, reflC_apply]
  abel

lemma opC_opC (y c : RN N) (u : Amb N) : opC y c (opC y c u) = u :=
  isoOp_isoOp _ (reflC_reflC c) y u

/-- The half ball `B_r(y) ∩ {⟨c, x - y⟩ > 0}`. -/
def halfB (y : RN N) (r : ℝ) (c : RN N) : Set (RN N) := ball y r ∩ {x | 0 < ⟪c, x - y⟫}

lemma isOpen_halfB (y : RN N) (r : ℝ) (c : RN N) : IsOpen (halfB y r c) :=
  isOpen_ball.inter (isOpen_lt continuous_const (by fun_prop))

lemma halfB_subset (y : RN N) (r : ℝ) (c : RN N) : halfB y r c ⊆ ball y r := inter_subset_left

lemma isDomain_halfB {y : RN N} {r : ℝ} (hr : 0 < r) {c : RN N} (hc : c ≠ 0) :
    IsDomain (halfB y r c) := by
  have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hne : (halfB y r c).Nonempty := by
    set t := r / (2 * ‖c‖) with ht
    have htp : 0 < t := by positivity
    refine ⟨y + t • c, ?_, ?_⟩
    · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos htp, ht]
      field_simp
      linarith
    · simp only [mem_setOf_eq, add_sub_cancel_left, inner_smul_right, real_inner_self_eq_norm_sq]
      positivity
  have hconv : Convex ℝ (halfB y r c) := by
    refine (convex_ball y r).inter ?_
    have : {x : RN N | 0 < ⟪c, x - y⟫} = {x | ⟪c, y⟫ < ⟪c, x⟫} := by
      ext x; simp [inner_sub_right]
    rw [this]
    exact convex_halfSpace_gt (by constructor <;> intros <;> simp [inner_add_right, inner_smul_right]) _
  exact ⟨⟨isOpen_halfB y r c, hne, isBounded_ball.subset (halfB_subset y r c)⟩,
    hconv.isConnected hne⟩

/-! ### The degree-one eigenfunction on the half ball -/

lemma deg1Fun_sigC (N : ℕ) (a : ℝ) (y c x : RN N) :
    deg1Fun N a y c (sigC y c x) = -deg1Fun N a y c x := by
  simp only [deg1Fun, inner_sigC, norm_sigC, neg_mul]

lemma deg1G_pos (hN : 2 ≤ N) {a : ℝ} (ha : 0 < a) {y x : RN N} (hx : ‖x - y‖ < annR N a) :
    0 < deg1G N a (‖x - y‖ ^ 2) := by
  have hν : (0 : ℝ) ≤ (N : ℝ) / 2 := by positivity
  have hC : 0 < CN N * a := mul_pos (zero_lt_one.trans (CN_gt_one hN)) ha
  have hs : 0 < Real.sqrt (CN N * a) := Real.sqrt_pos.mpr hC
  have hsR := sqrt_CN_mul_annR hN ha
  rw [deg1G_eq_besselF hN ha]
  refine besselF_pos_before hν (by positivity) ?_
  rw [← hsR]; exact mul_lt_mul_of_pos_left hx hs

/-- `exists_deg1` with the gradient component. -/
lemma exists_deg1' (hN : 2 ≤ N) {a : ℝ} (ha : 0 < a) (y c : RN N) :
    ∃ w : Amb N, w ∈ H (ball y (annR N a)) ∧
      (w.1 : RN N → ℝ) =ᵐ[volume] (ball y (annR N a)).indicator (deg1Fun N a y c) ∧
      (w.2 : RN N → RN N) =ᵐ[volume]
        (ball y (annR N a)).indicator (gradient (deg1Fun N a y c)) ∧
      ∀ φ ∈ H (ball y (annR N a)), qf w φ = CN N * a * l2 w φ := by
  have hν : (0 : ℝ) ≤ (N : ℝ) / 2 := by positivity
  have hC : 0 < CN N * a := mul_pos (zero_lt_one.trans (CN_gt_one hN)) ha
  set s := Real.sqrt (CN N * a) with hsdef
  have hs : 0 < s := Real.sqrt_pos.mpr hC
  obtain ⟨hj1, hj12, hF1, hF2, -, -⟩ := besselZero_props hν
  set R := annR N a with hRdef
  have hsR : s * R = besselZero ((N : ℝ) / 2) 1 := sqrt_CN_mul_annR hN ha
  have hR : 0 < R := annR_pos hN ha
  set R' := besselZero ((N : ℝ) / 2) 2 / s with hR'def
  have hsR' : s * R' = besselZero ((N : ℝ) / 2) 2 := by rw [hR'def]; field_simp
  have hRR : R < R' := by
    have : s * R < s * R' := by rw [hsR, hsR']; exact hj12
    exact lt_of_mul_lt_mul_left this hs.le
  set F : RN N → ℝ := fun x => deg1G N a (‖x - y‖ ^ 2) with hFdef
  have hFeq : ∀ x, F x = besselF ((N : ℝ) / 2) (s * ‖x - y‖) := fun x =>
    deg1G_eq_besselF hN ha _
  have hpos : ∀ x, ‖x - y‖ < R → 0 < F x := fun x hx => deg1G_pos hN ha hx
  have hnp : ∀ x, R ≤ ‖x - y‖ → ‖x - y‖ ≤ R' → F x ≤ 0 := fun x h1 h2 => by
    rw [hFeq]
    have e1 : besselZero ((N : ℝ) / 2) 1 ≤ s * ‖x - y‖ := by
      rw [← hsR]; exact mul_le_mul_of_nonneg_left h1 hs.le
    have e2 : s * ‖x - y‖ ≤ besselZero ((N : ℝ) / 2) 2 := by
      rw [← hsR']; exact mul_le_mul_of_nonneg_left h2 hs.le
    rcases e1.eq_or_lt with h | h
    · rw [← h, hF1]
    rcases e2.eq_or_lt with h' | h'
    · rw [h', hF2]
    exact (besselF_neg_between hν h h').le
  obtain ⟨φ, hφH, hφ1, hφ2⟩ := mem_H_ball_of_sign (contDiff_deg1Rad hN ha y) hR hRR hpos hnp
  obtain ⟨w, hwH, hw1, hw2⟩ := mem_H_ball_mul_inner (contDiff_deg1Rad hN ha y) hφH hφ1 hφ2 c
  exact ⟨w, hwH, hw1, hw2, weak_eigen_of_laplacian (contDiff_deg1Fun hN ha y c)
    (laplacian_deg1Fun hN ha y c) hw1 hw2⟩

lemma posSign_deg1 (hN : 2 ≤ N) {a : ℝ} (ha : 0 < a) (y c : RN N) :
    posSign (ball y (annR N a)) (deg1Fun N a y c) = halfB y (annR N a) c := by
  ext x
  simp only [posSign, halfB, mem_inter_iff, mem_setOf_eq]
  constructor
  · rintro ⟨hx, h⟩
    refine ⟨hx, ?_⟩
    have hg := deg1G_pos hN ha (y := y) (x := x) (by simpa [dist_eq_norm] using hx)
    exact pos_of_mul_pos_left h hg.le
  · rintro ⟨hx, h⟩
    exact ⟨hx, mul_pos h (deg1G_pos hN ha (by simpa [dist_eq_norm] using hx))⟩

/-- The degree-one eigenfunction restricted to the half ball lies in `H₀¹(B⁺)`. -/
lemma exists_half_deg1 (hN : 2 ≤ N) {a : ℝ} (ha : 0 < a) (y c : RN N) :
    ∃ w : Amb N, w ∈ H (halfB y (annR N a) c) ∧
      (w.1 : RN N → ℝ) =ᵐ[volume] (halfB y (annR N a) c).indicator (deg1Fun N a y c) ∧
      (w.2 : RN N → RN N) =ᵐ[volume]
        (halfB y (annR N a) c).indicator (gradient (deg1Fun N a y c)) := by
  obtain ⟨wB, hwH, hw1, hw2, -⟩ := exists_deg1' hN ha y c
  set B := ball y (annR N a)
  have hR := annR_pos hN ha
  have hE : IsAdmissible B := (isDomain_ball y hR).1
  have hcont : Continuous (deg1Fun N a y c) := (contDiff_deg1Fun hN ha y c).continuous
  have hrep : IsContRep B wB (deg1Fun N a y c) := by
    refine ⟨hcont.continuousOn, ?_⟩
    rw [EventuallyEq, ae_restrict_iff' isOpen_ball.measurableSet]
    filter_upwards [hw1] with x hx hxB
    rw [hx, indicator_of_mem hxB]
  have hpos := posPart_mem_H_posSign hE hwH hrep
  rw [posSign_deg1 hN ha] at hpos
  refine ⟨posPart wB, hpos, ?_, ?_⟩
  · filter_upwards [posPart_fst_ae' wB, hw1] with x e1 e2
    rw [e1, e2]
    by_cases hx : x ∈ halfB y (annR N a) c
    · rw [indicator_of_mem (halfB_subset _ _ _ hx), indicator_of_mem hx]
      exact max_eq_left (by
        have := (posSign_deg1 hN ha y c ▸ hx : x ∈ posSign B (deg1Fun N a y c)).2
        exact this.le)
    · rw [indicator_of_notMem hx]
      by_cases hxB : x ∈ B
      · rw [indicator_of_mem hxB]
        refine max_eq_right (not_lt.mp fun h => hx ?_)
        rw [← posSign_deg1 hN ha y c]; exact ⟨hxB, h⟩
      · rw [indicator_of_notMem hxB]; simp
  · filter_upwards [posPart_snd_ae_ite wB, hw1, hw2] with x e1 e2 e3
    rw [e1, e2, e3]
    by_cases hx : x ∈ halfB y (annR N a) c
    · have hp := (posSign_deg1 hN ha y c ▸ hx : x ∈ posSign B (deg1Fun N a y c))
      rw [indicator_of_mem (halfB_subset _ _ _ hx), indicator_of_mem hx,
        indicator_of_mem (halfB_subset _ _ _ hx), if_pos (show 0 < deg1Fun N a y c x from hp.2), one_smul]
    · rw [indicator_of_notMem hx]
      by_cases hxB : x ∈ B
      · rw [indicator_of_mem hxB, if_neg, zero_smul]
        intro h; apply hx; rw [← posSign_deg1 hN ha y c]; exact ⟨hxB, h⟩
      · rw [indicator_of_notMem hxB]; simp

/-- **First eigenvalue of the half ball**: `λ₁(B⁺) = C_N a`, with first eigenfunction `Ψ_c`. -/
theorem half_first_eigen (hN : 2 ≤ N) {a : ℝ} (ha : 0 < a) (y : RN N) {c : RN N} (hc : c ≠ 0) :
    eigenvalue (halfB y (annR N a) c) 1 = CN N * a ∧
      ∃ w : Amb N, IsEigenfunction (halfB y (annR N a) c) w (CN N * a) ∧
        (w.1 : RN N → ℝ) =ᵐ[volume] (halfB y (annR N a) c).indicator (deg1Fun N a y c) := by
  obtain ⟨w, hwH, hw1, hw2⟩ := exists_half_deg1 hN ha y c
  obtain ⟨wB, -, hB1, hB2, hBw⟩ := exists_deg1' hN ha y c
  have hR := annR_pos hN ha
  have hD := isDomain_halfB (y := y) hR hc
  have hHm : MeasurableSet (halfB y (annR N a) c) := (isOpen_halfB _ _ _).measurableSet
  have hposf : ∀ x ∈ halfB y (annR N a) c, 0 < deg1Fun N a y c x := fun x hx =>
    mul_pos hx.2 (deg1G_pos hN ha (by simpa [dist_eq_norm] using hx.1))
  have hweak : ∀ φ ∈ H (halfB y (annR N a) c), qf w φ = CN N * a * l2 w φ := by
    refine weak_of_agree hHm (halfB_subset _ _ _) hBw ?_ ?_
    · rw [EventuallyEq, ae_restrict_iff' hHm]
      filter_upwards [hw1, hB1] with x e1 e2 hx
      rw [e1, e2, indicator_of_mem hx, indicator_of_mem (halfB_subset _ _ _ hx)]
    · rw [EventuallyEq, ae_restrict_iff' hHm]
      filter_upwards [hw2, hB2] with x e1 e2 hx
      rw [e1, e2, indicator_of_mem hx, indicator_of_mem (halfB_subset _ _ _ hx)]
  have hE : IsEigenfunction (halfB y (annR N a) c) w (CN N * a) :=
    ⟨hwH, ne_zero_of_indicator_pos (isOpen_halfB _ _ _) hD.1.2.1 hposf hw1, hweak⟩
  exact ⟨eigenvalue_one_eq_of_nonneg hN hD hE (nonneg_of_indicator_pos hposf hw1), w, hE, hw1⟩

end FourthRatio

end
