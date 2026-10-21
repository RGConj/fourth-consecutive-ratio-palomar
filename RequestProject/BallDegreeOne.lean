module

public import RequestProject.BallSpectral
public import RequestProject.BallSteps

/-!
# Degree-one eigenfunctions of the ball

With `ν = N/2 - 1`, `a > 0`, `R = j_{ν,1}/√a` and `b = C_N a`, the functions
`Ψ_c(x) = ⟨c, x - y⟩ g(|x - y|²)`, where `g(r²) = c' r^{-N/2} J_{N/2}(√b r)` is the entire
Bessel series of order `N/2` and parameter `b`, restricted to `B = B_R(y)`, lie in `H₀¹(B)` and
are weak eigenfunctions of `B` with eigenvalue `C_N a` (note `√b R = j_{N/2,1}`, so `g` vanishes on
`∂B`).  The map `c ↦ Ψ_c` is linear and injective, so these eigenfunctions span an
`N`-dimensional space.

This is the part of the second-eigenspace statement of the paper's ball lemma that is used in the
proof of the main theorem (in the ball–annulus lemma): it provides `N` linearly independent
eigenfunctions of the ball with eigenvalue `C_N a`, without identifying `C_N a` as `λ₂(B)`.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Function Set
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

variable {N : ℕ}

/-- Laplacian of `z ↦ ⟨c, z⟩ G(|z|²)`. -/
lemma laplacian_inner_radial_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι]
    (v : OrthonormalBasis ι ℝ E) (c : E) (G G' G'' : ℝ → ℝ)
    (hG : ∀ s, HasDerivAt G (G' s) s) (hG' : ∀ s, HasDerivAt G' (G'' s) s) (x : E) :
    Laplacian.laplacian (fun z : E => ⟪c, z⟫ * G (‖z‖ ^ 2)) x =
      ⟪c, x⟫ * (2 * (Fintype.card ι + 2) * G' (‖x‖^2) + 4 * ‖x‖^2 * G'' (‖x‖^2)) := by
  have hr : ∀ y : E, HasFDerivAt (fun z => G (‖z‖ ^ 2)) (G' (‖y‖^2) • (2 • innerSL ℝ y)) y :=
    fun y => (hG _).comp_hasFDerivAt y (hasStrictFDerivAt_norm_sq y).hasFDerivAt
  have hr' : ∀ y : E, HasFDerivAt (fun z => G' (‖z‖ ^ 2)) (G'' (‖y‖^2) • (2 • innerSL ℝ y)) y :=
    fun y => (hG' _).comp_hasFDerivAt y (hasStrictFDerivAt_norm_sq y).hasFDerivAt
  have hc : ∀ y : E, HasFDerivAt (fun z : E => ⟪c, z⟫) (innerSL ℝ c) y :=
    fun y => (innerSL ℝ c).hasFDerivAt
  have hd : ∀ y : E, HasFDerivAt (fun z : E => ⟪c, z⟫ * G (‖z‖ ^ 2))
      ((⟪c, y⟫ * G' (‖y‖^2)) • ((2 • innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ) y) +
        G (‖y‖^2) • innerSL ℝ c) y := by
    intro y
    refine ((hc y).mul (hr y)).congr_fderiv ?_
    ext w
    simp [innerSL]
    ring
  have hf : fderiv ℝ (fun z : E => ⟪c, z⟫ * G (‖z‖ ^ 2)) =
      fun y => (⟪c, y⟫ * G' (‖y‖^2)) • ((2 • innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ) y) +
        G (‖y‖^2) • innerSL ℝ c := by
    funext y; rw [(hd y).fderiv]
  have h1 : HasFDerivAt (fun y : E => ⟪c, y⟫ * G' (‖y‖^2))
      (⟪c, x⟫ • (G'' (‖x‖^2) • (2 • innerSL ℝ x)) + G' (‖x‖^2) • innerSL ℝ c) x :=
    (hc x).mul (hr' x)
  have h2 := (2 • innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).hasFDerivAt (x := x)
  have h3 : HasFDerivAt (fun y : E => (⟪c, y⟫ * G' (‖y‖^2)) •
      ((2 • innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ) y) + G (‖y‖^2) • innerSL ℝ c) _ x :=
    (h1.smul h2).add ((hr x).smul_const (innerSL ℝ c))
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ v]
  simp only [iteratedFDeriv_two_apply]
  rw [hf, h3.fderiv]
  have hs : ∑ i, ⟪x, v i⟫ * ⟪x, v i⟫ = ‖x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← v.sum_inner_mul_inner x x]
    simp [real_inner_comm]
  have hs2 : ∑ i, ⟪c, v i⟫ * ⟪x, v i⟫ = ⟪c, x⟫ := by
    rw [← v.sum_inner_mul_inner c x]
    simp [real_inner_comm]
  simp [innerSL]
  rw [Finset.sum_congr rfl (fun i _ => show _ = ⟪c, x⟫ * G' (‖x‖ ^ 2) * 2 +
    (4 * ⟪c, x⟫ * G'' (‖x‖ ^ 2)) * (⟪x, v i⟫ * ⟪x, v i⟫) +
      (4 * G' (‖x‖ ^ 2)) * (⟪c, v i⟫ * ⟪x, v i⟫) by ring)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum (s := Finset.univ) (a := 4 * ⟪c, x⟫ * G'' (‖x‖ ^ 2)),
    ← Finset.mul_sum (s := Finset.univ) (a := 4 * G' (‖x‖ ^ 2)), hs, hs2]
  simp
  ring

/-- `F_ν = J_ν(x) (x/2)^{-ν}` is negative between the first two zeros. -/
lemma besselF_neg_between {ν : ℝ} (hν : 0 ≤ ν) {x : ℝ} (h1 : besselZero ν 1 < x)
    (h2 : x < besselZero ν 2) : besselF ν x < 0 := by
  have hx : 0 < x := (besselZero_props hν).1.trans h1
  have hJ := besselJ_neg_between hν h1 h2
  rw [besselJ_eq_besselF ν hx] at hJ
  have hp : 0 < (x / 2) ^ ν := Real.rpow_pos_of_pos (by positivity) ν
  by_contra hc
  push_neg at hc
  linarith [mul_nonneg hp.le hc]

/-- The radial factor `g(s) = Σ c_m(N/2, C_N a) s^m` of the degree-one eigenfunctions. -/
def deg1G (N : ℕ) (a s : ℝ) : ℝ := besselSeries ((N : ℝ) / 2) (CN N * a) s

/-- The degree-one function `Ψ_c(x) = ⟨c, x - y⟩ g(|x - y|²)`. -/
def deg1Fun (N : ℕ) (a : ℝ) (y c x : RN N) : ℝ := ⟪c, x - y⟫ * deg1G N a (‖x - y‖ ^ 2)

/-- `√(C_N a) · j_{ν,1}/√a = j_{N/2,1}`. -/
lemma sqrt_CN_mul_annR (hN : 2 ≤ N) {a : ℝ} (ha : 0 < a) :
    Real.sqrt (CN N * a) * annR N a = besselZero ((N : ℝ) / 2) 1 := by
  have h1 := (besselZero_props (hN_nu hN)).1
  have h2 := (besselZero_props (ν := (N : ℝ) / 2) (by positivity)).1
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  rw [CN, annR, Real.sqrt_mul (by positivity), Real.sqrt_div' _ (by positivity),
    Real.sqrt_sq h2.le, Real.sqrt_sq h1.le]
  generalize besselZero ((N : ℝ) / 2 - 1) 1 = j at h1 ⊢
  field_simp

/-- The radial factor in terms of `F_{N/2}`. -/
lemma deg1G_eq_besselF (hN : 2 ≤ N) {a : ℝ} (ha : 0 < a) (r : ℝ) :
    deg1G N a (r ^ 2) = besselF ((N : ℝ) / 2) (Real.sqrt (CN N * a) * r) := by
  have hC : 0 ≤ CN N * a := mul_nonneg (zero_le_one.trans (CN_gt_one hN).le) ha.le
  rw [deg1G, besselSeries_scale, besselF, mul_pow, Real.sq_sqrt hC]

/-- A smooth function that is positive on `B_R(y)` and nonpositive on a closed annulus around
`∂B_R(y)` gives, restricted to `B_R(y)`, an element of `H₀¹(B_R(y))`. -/
lemma mem_H_ball_of_sign {F : RN N → ℝ} (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) {y : RN N}
    {R R' : ℝ} (hR : 0 < R) (hRR : R < R') (hpos : ∀ x, ‖x - y‖ < R → 0 < F x)
    (hnp : ∀ x, R ≤ ‖x - y‖ → ‖x - y‖ ≤ R' → F x ≤ 0) :
    ∃ φ : Amb N, φ ∈ H (ball y R) ∧
      (φ.1 : RN N → ℝ) =ᵐ[volume] (ball y R).indicator F ∧
      (φ.2 : RN N → RN N) =ᵐ[volume] (ball y R).indicator (gradient F) := by
  set B := ball y R with hBdef
  have hBo : IsOpen B := isOpen_ball
  have hBm : MeasurableSet B := hBo.measurableSet
  obtain ⟨χ, hχs, hχc, hχE, U, hU, hKU, hU1⟩ := exists_cutoff (isCompact_closedBall y R')
    isOpen_ball (closedBall_subset_ball (by linarith : R' < R' + 1))
  set G : RN N → ℝ := fun x => χ x * F x with hGdef
  have hGs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G := hχs.mul hF
  have hGc : HasCompactSupport G := hχc.mul_right
  have hGE : tsupport G ⊆ ball y (R' + 1) := tsupport_mul_subset_left.trans hχE
  set v := testPair G hGs hGc with hvdef
  have hvH : v ∈ H (ball y (R' + 1)) := testGraph_subset_H _ (testPair_mem hGs hGc hGE)
  have hE : IsAdmissible (ball y (R' + 1)) :=
    ⟨isOpen_ball, nonempty_ball.mpr (by linarith), isBounded_ball⟩
  have hv1 : (v.1 : RN N → ℝ) =ᵐ[volume] G := MemLp.coeFn_toLp (memLp_of_testFun hGs hGc)
  have hv2 : (v.2 : RN N → RN N) =ᵐ[volume] gradient G :=
    MemLp.coeFn_toLp (memLp_gradient_of_testFun hGs hGc)
  have hvc : IsContRep (ball y (R' + 1)) v G :=
    ⟨hGs.continuous.continuousOn, ae_restrict_of_ae hv1⟩
  have hpos' := posPart_mem_H_posSign hE hvH hvc
  have hcn : Continuous fun x : RN N => ‖x - y‖ := by fun_prop
  set S := posSign (ball y (R' + 1)) G ∩ {x | R' < ‖x - y‖}
  have hS : IsOpen S :=
    (isOpen_posSign isOpen_ball hGs.continuous.continuousOn).inter
      (isOpen_lt continuous_const hcn)
  have hBS : Disjoint B S := by
    rw [Set.disjoint_left]
    intro x hxB hxS
    have : ‖x - y‖ < R := by simpa [B, dist_eq_norm] using hxB
    have h2 : R' < ‖x - y‖ := hxS.2
    linarith
  have hBU : ∀ x ∈ B, x ∈ U := fun x hx => hKU (by
    have : ‖x - y‖ < R := by simpa [B, dist_eq_norm] using hx
    rw [mem_closedBall, dist_eq_norm]; linarith)
  have hBpos : ∀ x ∈ B, 0 < F x := fun x hx =>
    hpos x (by simpa [B, dist_eq_norm] using hx)
  have hGB : ∀ x ∈ B, G x = F x := fun x hx => by
    simp only [G, hU1 x (hBU x hx), one_mul]
  have hsub : posSign (ball y (R' + 1)) G ⊆ B ∪ S := by
    rintro x ⟨hxE, hxG⟩
    by_cases h : R' < ‖x - y‖
    · exact Or.inr ⟨⟨hxE, hxG⟩, h⟩
    left
    push_neg at h
    have hχ1 : χ x = 1 := hU1 x (hKU (by rw [mem_closedBall, dist_eq_norm]; exact h))
    have hF' : 0 < F x := by simpa [G, hχ1] using hxG
    show dist x y < R
    rw [dist_eq_norm]
    by_contra hle
    push_neg at hle
    linarith [hnp x hle h]
  refine ⟨restrictTo B (posPart v),
    restrictTo_mem_H_of_union hBo hS hBS (H_mono hsub hpos'), ?_, ?_⟩
  · filter_upwards [restrictTo_fst_ae hBm (posPart v), posPart_fst_ae' v, hv1] with x h1 h2 h3
    rw [h1]
    by_cases hx : x ∈ B
    · rw [indicator_of_mem hx, indicator_of_mem hx, h2, h3, hGB x hx,
        max_eq_left (hBpos x hx).le]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx]
  · filter_upwards [restrictTo_snd_ae hBm (posPart v), posPart_snd_ae_ite v, hv1, hv2]
      with x h1 h2 h3 h4
    rw [h1]
    by_cases hx : x ∈ B
    · rw [indicator_of_mem hx, indicator_of_mem hx, h2, h3, h4, hGB x hx,
        if_pos (hBpos x hx), one_smul]
      refine Filter.EventuallyEq.gradient_eq ?_
      filter_upwards [hU.mem_nhds (hBU x hx)] with z hz
      simp only [G, hU1 z hz, one_mul]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx]

/-- Multiplying an element of `H₀¹(B_R(y))` represented by a smooth `F` by `⟨c, x - y⟩`. -/
lemma mem_H_ball_mul_inner {F : RN N → ℝ} (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    {y : RN N} {R : ℝ} {φ : Amb N} (hφ : φ ∈ H (ball y R))
    (h1 : (φ.1 : RN N → ℝ) =ᵐ[volume] (ball y R).indicator F)
    (h2 : (φ.2 : RN N → RN N) =ᵐ[volume] (ball y R).indicator (gradient F)) (c : RN N) :
    ∃ w : Amb N, w ∈ H (ball y R) ∧
      (w.1 : RN N → ℝ) =ᵐ[volume] (ball y R).indicator (fun x => ⟪c, x - y⟫ * F x) ∧
      (w.2 : RN N → RN N) =ᵐ[volume]
        (ball y R).indicator (gradient (fun x => ⟪c, x - y⟫ * F x)) := by
  have hgc : ∀ x, gradient (fun x : RN N => ⟪c, x - y⟫) x = c := fun x => by
    have : HasGradientAt (fun x : RN N => ⟪c, x - y⟫) c x := by
      rw [hasGradientAt_iff_hasFDerivAt]
      have := ((innerSL ℝ c).hasFDerivAt).comp x ((hasFDerivAt_id x).sub_const y)
      convert this using 1
      · rfl
      · ext z
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
          InnerProductSpace.toDual_apply_apply, innerSL_apply_apply]
    exact this.gradient
  have hin : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : RN N => ⟪c, x - y⟫) :=
    contDiff_const.inner ℝ (contDiff_id.sub contDiff_const)
  obtain ⟨χ, hχs, hχc, -, U, hU, hKU, hU1⟩ := exists_cutoff (isCompact_closedBall y R)
    isOpen_univ (subset_univ _)
  set h : RN N → ℝ := fun x => χ x * ⟪c, x - y⟫ with hhdef
  have hhs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h := hχs.mul hin
  have hhc : HasCompactSupport h := hχc.mul_right
  obtain ⟨hg, C, -, hC⟩ := exists_bound_cutoff hhs hhc
  have hBU : ∀ x ∈ ball y R, x ∈ U := fun x hx => hKU (ball_subset_closedBall hx)
  have hloc : ∀ x ∈ ball y R, h =ᶠ[𝓝 x] fun x => ⟪c, x - y⟫ := fun x hx => by
    filter_upwards [hU.mem_nhds (hBU x hx)] with z hz
    simp [h, hU1 z hz]
  refine ⟨Mpair hhs.continuous hg hC φ, Mpair_mem_H_self hhs.continuous hg hC hhs hφ, ?_, ?_⟩
  · filter_upwards [Mpair_fst_ae hhs.continuous hg hC φ, h1] with x e1 e2
    rw [e1, e2]
    by_cases hx : x ∈ ball y R
    · rw [indicator_of_mem hx, indicator_of_mem hx, (hloc x hx).self_of_nhds]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, mul_zero]
  · filter_upwards [Mpair_snd_ae hhs.continuous hg hC φ, h1, h2] with x e1 e2 e3
    rw [e1, e2, e3]
    by_cases hx : x ∈ ball y R
    · rw [indicator_of_mem hx, indicator_of_mem hx, indicator_of_mem hx,
        (hloc x hx).self_of_nhds, (hloc x hx).gradient_eq, hgc,
        gradient_mul_of_contDiff hin hF, hgc]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, indicator_of_notMem hx]
      simp

lemma contDiff_deg1Rad (hN : 2 ≤ N) {a : ℝ} (ha : 0 < a) (y : RN N) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : RN N => deg1G N a (‖x - y‖ ^ 2)) := by
  have hC : 0 ≤ CN N * a := mul_nonneg (zero_le_one.trans (CN_gt_one hN).le) ha.le
  have hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deg1G N a) := by
    have : AnalyticOnNhd ℝ (deg1G N a) univ := fun s _ =>
      analyticAt_besselSeries (by positivity) hC s
    exact (contDiffOn_univ.mp (this.contDiffOn uniqueDiffOn_univ)).of_le le_top
  exact hG.comp ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const))

lemma contDiff_deg1Fun (hN : 2 ≤ N) {a : ℝ} (ha : 0 < a) (y c : RN N) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deg1Fun N a y c) :=
  (contDiff_const.inner ℝ (contDiff_id.sub contDiff_const)).mul (contDiff_deg1Rad hN ha y)

lemma laplacian_deg1Fun (hN : 2 ≤ N) {a : ℝ} (ha : 0 < a) (y c x : RN N) :
    Laplacian.laplacian (deg1Fun N a y c) x = -(CN N * a) * deg1Fun N a y c x := by
  have hC : 0 ≤ CN N * a := mul_nonneg (zero_le_one.trans (CN_gt_one hN).le) ha.le
  have hν : (0 : ℝ) ≤ (N : ℝ) / 2 := by positivity
  set b := EuclideanSpace.basisFun (Fin N) ℝ
  have h1 : Laplacian.laplacian (deg1Fun N a y c) x =
      Laplacian.laplacian (fun z : RN N => ⟪c, z⟫ * deg1G N a (‖z‖ ^ 2)) (x - y) := by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ b,
      InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ b]
    have := iteratedFDeriv_comp_sub (𝕜 := ℝ) (n := 2)
      (f := fun z : RN N => ⟪c, z⟫ * deg1G N a (‖z‖ ^ 2)) y x
    exact Finset.sum_congr rfl fun i _ => by rw [← this]; rfl
  have h2 := laplacian_inner_radial_sq b c (deg1G N a)
    (fun s => ∑' m : ℕ, ((m : ℝ) + 1) * besselCoef ((N : ℝ) / 2) (CN N * a) (m + 1) * s ^ m)
    (fun s => ∑' m : ℕ, ((m : ℝ) + 1) * (((m + 1 : ℕ) : ℝ) + 1) *
      besselCoef ((N : ℝ) / 2) (CN N * a) (m + 1 + 1) * s ^ m)
    (fun s => hasDerivAt_besselSeries hν hC s)
    (fun s => hasDerivAt_besselSeries_deriv hν hC s) (x - y)
  rw [h1, h2, Fintype.card_fin]
  have hode := besselSeries_ode hν hC (‖x - y‖ ^ 2)
  simp only [deg1Fun, deg1G]
  have hN' : ((N : ℝ) + 2) = 2 * ((N : ℝ) / 2) + 2 := by ring
  rw [hN']
  linear_combination ⟪c, x - y⟫ * hode

/-- The degree-one eigenfunctions of the ball: for every `c` there is `w ∈ H₀¹(B)` represented by
`Ψ_c` on `B`, which is a weak eigenfunction with eigenvalue `C_N a`. -/
lemma exists_deg1 (hN : 2 ≤ N) {a : ℝ} (ha : 0 < a) (y c : RN N) :
    ∃ w : Amb N, w ∈ H (ball y (annR N a)) ∧
      (w.1 : RN N → ℝ) =ᵐ[volume] (ball y (annR N a)).indicator (deg1Fun N a y c) ∧
      ∀ φ ∈ H (ball y (annR N a)), qf w φ = CN N * a * l2 w φ := by
  have hν : (0 : ℝ) ≤ (N : ℝ) / 2 := by positivity
  have hC : 0 < CN N * a := mul_pos (zero_lt_one.trans (CN_gt_one hN)) ha
  set s := Real.sqrt (CN N * a) with hsdef
  have hs : 0 < s := Real.sqrt_pos.mpr hC
  obtain ⟨hj1, hj12, hF1, hF2, -, -⟩ := besselZero_props hν
  set R := annR N a with hRdef
  have hsR : s * R = besselZero ((N : ℝ) / 2) 1 := sqrt_CN_mul_annR hN ha
  have hR : 0 < R := by
    have := hsR ▸ hj1; exact pos_of_mul_pos_right this hs.le
  set R' := besselZero ((N : ℝ) / 2) 2 / s with hR'def
  have hsR' : s * R' = besselZero ((N : ℝ) / 2) 2 := by rw [hR'def]; field_simp
  have hRR : R < R' := by
    have : s * R < s * R' := by rw [hsR, hsR']; exact hj12
    exact lt_of_mul_lt_mul_left this hs.le
  set F : RN N → ℝ := fun x => deg1G N a (‖x - y‖ ^ 2) with hFdef
  have hFeq : ∀ x, F x = besselF ((N : ℝ) / 2) (s * ‖x - y‖) := fun x =>
    deg1G_eq_besselF hN ha _
  have hpos : ∀ x, ‖x - y‖ < R → 0 < F x := fun x hx => by
    rw [hFeq]
    refine besselF_pos_before hν (by positivity) ?_
    rw [← hsR]; exact mul_lt_mul_of_pos_left hx hs
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
  exact ⟨w, hwH, hw1, weak_eigen_of_laplacian (contDiff_deg1Fun hN ha y c)
    (laplacian_deg1Fun hN ha y c) hw1 hw2⟩

/-- If `Ψ_c` vanishes almost everywhere on `B`, then `c = 0`. -/
lemma deg1_inj (hN : 2 ≤ N) {a : ℝ} (ha : 0 < a) (y c : RN N)
    (h : (ball y (annR N a)).indicator (deg1Fun N a y c) =ᵐ[volume] 0) : c = 0 := by
  have hν : (0 : ℝ) ≤ (N : ℝ) / 2 := by positivity
  have hC : 0 < CN N * a := mul_pos (zero_lt_one.trans (CN_gt_one hN)) ha
  have hs : 0 < Real.sqrt (CN N * a) := Real.sqrt_pos.mpr hC
  have hsR := sqrt_CN_mul_annR hN ha
  have hR : 0 < annR N a := by
    have := hsR ▸ (besselZero_props hν).1; exact pos_of_mul_pos_right this hs.le
  have hpos : ∀ x, ‖x - y‖ < annR N a → 0 < deg1G N a (‖x - y‖ ^ 2) := fun x hx => by
    rw [deg1G_eq_besselF hN ha]
    refine besselF_pos_before hν (by positivity) ?_
    rw [← hsR]; exact mul_lt_mul_of_pos_left hx hs
  by_contra hc
  set Ω' : Set (RN N) := ball y (annR N a) ∩ {x | 0 < ⟪c, x - y⟫} with hΩ'
  have hΩo : IsOpen Ω' :=
    isOpen_ball.inter (isOpen_lt continuous_const (by fun_prop))
  have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hc
  set t := annR N a / (2 * ‖c‖) with ht
  have htp : 0 < t := by positivity
  have hne : Ω'.Nonempty := by
    refine ⟨y + t • c, ?_, ?_⟩
    · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos htp, ht]
      field_simp
      linarith
    · simp only [mem_setOf_eq, add_sub_cancel_left, inner_smul_right, real_inner_self_eq_norm_sq]
      positivity
  have hae : ∀ᵐ x ∂(volume.restrict Ω'), False := by
    rw [ae_restrict_iff' hΩo.measurableSet]
    filter_upwards [h] with x hx hxΩ
    rw [indicator_of_mem hxΩ.1] at hx
    have h1 : ‖x - y‖ < annR N a := by simpa [dist_eq_norm] using hxΩ.1
    have : 0 < deg1Fun N a y c x := mul_pos hxΩ.2 (hpos x h1)
    simp only [Pi.zero_apply] at hx
    linarith
  have : volume.restrict Ω' = 0 := ae_eq_bot.mp (eventually_false_iff_eq_bot.mp hae)
  rw [Measure.restrict_eq_zero] at this
  exact (hΩo.measure_pos volume hne).ne' this

/-- **Degree-one eigenfunctions of the ball.** With `ν = N/2 - 1`, `a > 0` and
`R = j_{ν,1}/√a`, for every ball `B = B_R(y)` there is an `N`-dimensional space of weak
eigenfunctions of `B` with eigenvalue `C_N a`. -/
theorem ball_degree_one (hN : 2 ≤ N) {a : ℝ} (ha : 0 < a) :
    let ν : ℝ := (N : ℝ) / 2 - 1
    let R := besselZero ν 1 / Real.sqrt a
    ∀ y : RN N, ∃ V : Submodule ℝ (Amb N), Module.finrank ℝ V = N ∧
      ∀ u ∈ V, u ∈ H (ball y R) ∧ ∀ φ ∈ H (ball y R), qf u φ = CN N * a * l2 u φ := by
  intro ν R y
  change ∃ V : Submodule ℝ (Amb N), Module.finrank ℝ V = N ∧
      ∀ u ∈ V, u ∈ H (ball y (annR N a)) ∧
        ∀ φ ∈ H (ball y (annR N a)), qf u φ = CN N * a * l2 u φ
  choose w hwH hw1 hweq using exists_deg1 hN ha y
  set B := ball y (annR N a)
  have hBm : MeasurableSet B := isOpen_ball.measurableSet
  have hadd : ∀ c d, w (c + d) = w c + w d := fun c d => by
    refine eq_of_fst_eq (hwH _) ((H B).add_mem (hwH c) (hwH d)) (Lp.ext ?_)
    filter_upwards [hw1 (c + d), hw1 c, hw1 d, Lp.coeFn_add (w c).1 (w d).1] with x e1 e2 e3 e4
    simp only [Prod.fst_add] at e4 ⊢
    rw [e1, e4, Pi.add_apply, e2, e3]
    by_cases hx : x ∈ B
    · simp only [indicator_of_mem hx, deg1Fun, inner_add_left]; ring
    · simp [indicator_of_notMem hx]
  have hsmul : ∀ (t : ℝ) c, w (t • c) = t • w c := fun t c => by
    refine eq_of_fst_eq (hwH _) ((H B).smul_mem t (hwH c)) (Lp.ext ?_)
    filter_upwards [hw1 (t • c), hw1 c, Lp.coeFn_smul t (w c).1] with x e1 e2 e3
    simp only [Prod.smul_fst] at e3 ⊢
    rw [e1, e3, Pi.smul_apply, e2, smul_eq_mul]
    by_cases hx : x ∈ B
    · simp only [indicator_of_mem hx, deg1Fun, inner_smul_left]; simp; ring
    · simp [indicator_of_notMem hx]
  let L : RN N →ₗ[ℝ] Amb N := { toFun := w, map_add' := hadd, map_smul' := hsmul }
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    refine deg1_inj hN ha y c ?_
    have h0 : (w c).1 = 0 := by
      change L c = 0 at hc; rw [show w c = L c from rfl, hc]; rfl
    filter_upwards [hw1 c, Lp.coeFn_zero ℝ 2 (volume : Measure (RN N))] with x e1 e2
    rw [← e1, h0, e2]
  refine ⟨LinearMap.range L, ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj hinj, finrank_euclideanSpace_fin]
  · rintro u ⟨c, rfl⟩
    exact ⟨hwH c, hweq c⟩

end FourthRatio

end
