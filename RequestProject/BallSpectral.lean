module

public import RequestProject.AnnulusSep

/-!
# First eigenvalue and first eigenfunction of the ball and of the annulus

With `ν = N/2 - 1`, `a > 0`, `R = j_{ν,1}/√a`, `R' = j_{ν,2}/√a` and the Bessel profile
`Φ = besselEntire N a` (`-ΔΦ = aΦ`, `Φ > 0` on `B_R`, `Φ < 0` on `R < |x| < R'`):

* `Φ(· - y)` restricted to `B = B_R(y)` lies in `H₀¹(B)` and is a weak eigenfunction with
  eigenvalue `a` (integration by parts against test functions, then density);
* `-Φ(· - y)` restricted to `A = {R < |x - y| < R'}` lies in `H₀¹(A)` and is a weak
  eigenfunction with eigenvalue `a`;
* `λ₁(B) = a` and `λ₁(A) = a`: a positive eigenfunction is not orthogonal to the positive
  ground state, so its eigenvalue is `λ₁`.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Function Set
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

variable {N : ℕ}

/-- A smooth solution of `-ΔΨ = aΨ`, restricted to an open set `Ω` (function and gradient), satisfies
the weak eigenvalue equation against all of `H_Ω`. -/
lemma weak_eigen_of_laplacian {Ω : Set (RN N)} {Ψ : RN N → ℝ} {a : ℝ}
    (hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ) (hΔ : ∀ x, Laplacian.laplacian Ψ x = -a * Ψ x)
    {u : Amb N} (hu1 : (u.1 : RN N → ℝ) =ᵐ[volume] Ω.indicator Ψ)
    (hu2 : (u.2 : RN N → RN N) =ᵐ[volume] Ω.indicator (gradient Ψ)) :
    ∀ φ ∈ H Ω, qf u φ = a * l2 u φ := by
  set L : Amb N →L[ℝ] ℝ := (innerSL ℝ u.2).comp (ContinuousLinearMap.snd ℝ _ _) -
    a • (innerSL ℝ u.1).comp (ContinuousLinearMap.fst ℝ _ _) with hL
  have hLapp : ∀ p, L p = qf u p - a * l2 u p := by
    intro p; simp [hL, qf, l2]
  have hle : H Ω ≤ LinearMap.ker L.toLinearMap := by
    refine Submodule.topologicalClosure_minimal _ ?_ (ContinuousLinearMap.isClosed_ker _)
    rw [Submodule.span_le]
    intro p hp
    obtain ⟨φ, hφ, hφc, hts, h4, h5⟩ := hp
    change L p = 0
    rw [hLapp]
    have hq : qf u p = ∫ x, ⟪gradient Ψ x, gradient φ x⟫ := by
      rw [qf, MeasureTheory.L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hu2, h5] with x h1 h2
      rw [h1, h2]
      by_cases hx : x ∈ Ω
      · rw [indicator_of_mem hx]
      · rw [indicator_of_notMem hx, gradient_eq_zero_of_notMem_tsupport (fun h => hx (hts h))]
        simp
    have hl : l2 u p = ∫ x, Ψ x * φ x := by
      rw [l2, MeasureTheory.L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hu1, h4] with x h1 h2
      simp only [RCLike.inner_apply, conj_trivial]
      rw [h1, h2]
      by_cases hx : x ∈ Ω
      · rw [indicator_of_mem hx]; ring
      · rw [indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport (fun h => hx (hts h))]
        simp
    rw [hq, hl, integral_inner_gradient_eq_neg_laplacian hΨ hφ hφc]
    simp_rw [hΔ, neg_mul, mul_assoc, integral_neg, integral_const_mul]
    ring
  intro φ hφ
  have := hle hφ
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hLapp] at this
  linarith

/-! ### The Bessel profile, shifted -/

lemma laplacian_besselEntire_shift (hN : 2 ≤ N) {a : ℝ} (ha : 0 ≤ a) (c : ℝ) (y x : RN N) :
    Laplacian.laplacian (fun x => c * besselEntire N a (x - y)) x =
      -a * (c * besselEntire N a (x - y)) := by
  set b := EuclideanSpace.basisFun (Fin N) ℝ
  have h1 : Laplacian.laplacian (fun x => besselEntire N a (x - y)) x =
      Laplacian.laplacian (besselEntire N a) (x - y) := by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ b,
      InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ b]
    simp [iteratedFDeriv_comp_sub]
  have hs : ContDiffAt ℝ 2 (fun x => besselEntire N a (x - y)) x :=
    (((contDiff_besselEntire hN ha).comp (contDiff_id.sub contDiff_const)).of_le
      (WithTop.coe_le_coe.mpr le_top)).contDiffAt
  have h2 := InnerProductSpace.laplacian_smul c hs
  change Laplacian.laplacian (c • fun x => besselEntire N a (x - y)) x = _
  rw [h2, h1, besselEntire_laplacian hN ha, smul_eq_mul]
  ring

lemma contDiff_besselEntire_shift (hN : 2 ≤ N) {a : ℝ} (ha : 0 ≤ a) (c : ℝ) (y : RN N) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => c * besselEntire N a (x - y)) :=
  contDiff_const.mul ((contDiff_besselEntire hN ha).comp (contDiff_id.sub contDiff_const))

lemma hasGradientAt_shift' (hN : 2 ≤ N) {a : ℝ} (ha : 0 ≤ a) (y x : RN N) :
    HasGradientAt (fun x => besselEntire N a (x - y)) (gradPhi N a (x - y)) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have := ((hasGradientAt_besselEntire hN ha (x - y)).hasFDerivAt).comp x
    ((hasFDerivAt_id x).sub_const y)
  convert this using 1
  · rfl
  · simp

/-- A pair represented by a function that is positive on a nonempty open set and vanishes
outside it is nonzero. -/
lemma ne_zero_of_indicator_pos {Ω : Set (RN N)} (hΩ : IsOpen Ω) (hne : Ω.Nonempty)
    {f : RN N → ℝ} (hf : ∀ x ∈ Ω, 0 < f x) {u : Amb N}
    (hu : (u.1 : RN N → ℝ) =ᵐ[volume] Ω.indicator f) : u ≠ 0 := by
  intro h0
  have hz : (u.1 : RN N → ℝ) =ᵐ[volume] 0 := by rw [h0]; exact Lp.coeFn_zero _ _ _
  have hae : ∀ᵐ x ∂(volume.restrict Ω), False := by
    rw [ae_restrict_iff' hΩ.measurableSet]
    filter_upwards [hu, hz] with x h1 h2 hx
    rw [h2, indicator_of_mem hx] at h1
    exact (hf x hx).ne' (by simpa using h1.symm)
  have : volume.restrict Ω = 0 := ae_eq_bot.mp (eventually_false_iff_eq_bot.mp hae)
  rw [Measure.restrict_eq_zero] at this
  exact (hΩ.measure_pos volume hne).ne' this

lemma nonneg_of_indicator_pos {Ω : Set (RN N)} {f : RN N → ℝ} (hf : ∀ x ∈ Ω, 0 < f x)
    {u : Amb N} (hu : (u.1 : RN N → ℝ) =ᵐ[volume] Ω.indicator f) :
    0 ≤ᵐ[volume] (u.1 : RN N → ℝ) := by
  filter_upwards [hu] with x hx
  rw [hx]
  by_cases h : x ∈ Ω
  · rw [indicator_of_mem h]; exact (hf x h).le
  · rw [indicator_of_notMem h]; rfl

/-- **The eigenvalue of a nonnegative eigenfunction is `λ₁`.** -/
lemma eigenvalue_one_eq_of_nonneg (hN : 2 ≤ N) {D : Set (RN N)} (hD : IsDomain D) {u : Amb N}
    {a : ℝ} (hu : IsEigenfunction D u a) (hnn : 0 ≤ᵐ[volume] (u.1 : RN N → ℝ)) :
    eigenvalue D 1 = a := by
  obtain ⟨u0, f, hu0, hf, hpos⟩ := ground_state_pos hN hD
  have hl := l2_pos_of_nonneg hD.1 hu.1 hu.2.1 hnn hu0.1 hf hpos
  have e1 := hu.2.2 u0 hu0.1
  have e2 := hu0.2.2 u hu.1
  have hq : qf u u0 = qf u0 u := real_inner_comm _ _
  have hl' : l2 u0 u = l2 u u0 := real_inner_comm _ _
  rw [hq, e2, hl'] at e1
  have : (eigenvalue D 1 - a) * l2 u u0 = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · linarith
  · exact absurd h hl.ne'

/-! ### The ball -/

/-- **The ball eigenfunction lies in `H₀¹(B)`.** The restriction of `Φ(· - y)` to
`B = B_R(y)` (function and gradient) belongs to `H₀¹(B)`. -/
theorem exists_ball_phi (hN : 2 ≤ N) {a : ℝ} (ha : 0 < a) (y : RN N) :
    ∃ φ : Amb N, φ ∈ H (ball y (annR N a)) ∧
      (φ.1 : RN N → ℝ) =ᵐ[volume] (ball y (annR N a)).indicator
        (fun x => 1 * besselEntire N a (x - y)) ∧
      (φ.2 : RN N → RN N) =ᵐ[volume] (ball y (annR N a)).indicator
        (gradient (fun x => 1 * besselEntire N a (x - y))) := by
  have hν := hN_nu hN
  obtain ⟨-, -, hz1, hz2, -, -⟩ := besselZero_props hν
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  set R := annR N a with hRdef
  set R' := annR' N a with hR'def
  have hR : 0 < R := div_pos (besselZero_props hν).1 hsa
  have hRR : R < R' := div_lt_div_of_pos_right (besselZero_props hν).2.1 hsa
  set B := ball y R with hBdef
  have hBo : IsOpen B := isOpen_ball
  have hBm : MeasurableSet B := hBo.measurableSet
  obtain ⟨χ, hχs, hχc, hχE, U, hU, hKU, hU1⟩ := exists_cutoff (isCompact_closedBall y R')
    isOpen_ball (closedBall_subset_ball (by linarith : R' < R' + 1))
  have hΦs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => besselEntire N a (x - y)) :=
    (contDiff_besselEntire hN ha.le).comp (contDiff_id.sub contDiff_const)
  set F : RN N → ℝ := fun x => χ x * besselEntire N a (x - y) with hFdef
  have hFs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F := hχs.mul hΦs
  have hFc : HasCompactSupport F := hχc.mul_right
  have hFE : tsupport F ⊆ ball y (R' + 1) := tsupport_mul_subset_left.trans hχE
  set v := testPair F hFs hFc with hvdef
  have hvH : v ∈ H (ball y (R' + 1)) := testGraph_subset_H _ (testPair_mem hFs hFc hFE)
  have hE : IsAdmissible (ball y (R' + 1)) :=
    ⟨isOpen_ball, nonempty_ball.mpr (by linarith), isBounded_ball⟩
  have hv1 : (v.1 : RN N → ℝ) =ᵐ[volume] F := MemLp.coeFn_toLp (memLp_of_testFun hFs hFc)
  have hv2 : (v.2 : RN N → RN N) =ᵐ[volume] gradient F :=
    MemLp.coeFn_toLp (memLp_gradient_of_testFun hFs hFc)
  have hvc : IsContRep (ball y (R' + 1)) v F := ⟨hFs.continuous.continuousOn, ae_restrict_of_ae hv1⟩
  have hpos := posPart_mem_H_posSign hE hvH hvc
  have hcn : Continuous fun x : RN N => ‖x - y‖ := by fun_prop
  set S := posSign (ball y (R' + 1)) F ∩ {x | R' < ‖x - y‖}
  have hS : IsOpen S :=
    (isOpen_posSign isOpen_ball hFs.continuous.continuousOn).inter (isOpen_lt continuous_const hcn)
  have hBS : Disjoint B S := by
    rw [Set.disjoint_left]
    intro x hxB hxS
    have : ‖x - y‖ < R := by simpa [B, dist_eq_norm] using hxB
    have h2 : R' < ‖x - y‖ := hxS.2
    linarith
  have hBU : ∀ x ∈ B, x ∈ U := fun x hx => hKU (by
    have : ‖x - y‖ < R := by simpa [B, dist_eq_norm] using hx
    rw [mem_closedBall, dist_eq_norm]; linarith)
  have hBpos : ∀ x ∈ B, 0 < besselEntire N a (x - y) := fun x hx =>
    besselEntire_pos hN ha (by
      change ‖x - y‖ < R
      simpa only [B, mem_ball, dist_eq_norm] using hx)
  have hFB : ∀ x ∈ B, F x = besselEntire N a (x - y) := fun x hx => by
    simp only [F, hU1 x (hBU x hx), one_mul]
  have hsub : posSign (ball y (R' + 1)) F ⊆ B ∪ S := by
    rintro x ⟨hxE, hxF⟩
    by_cases h : R' < ‖x - y‖
    · exact Or.inr ⟨⟨hxE, hxF⟩, h⟩
    left
    push_neg at h
    have hχ1 : χ x = 1 := hU1 x (hKU (by rw [mem_closedBall, dist_eq_norm]; exact h))
    have hF' : 0 < besselEntire N a (x - y) := by
      simpa [F, hχ1] using hxF
    rw [besselEntire_eq_radPhi] at hF'
    show dist x y < R
    rw [dist_eq_norm]
    by_contra hle
    push_neg at hle
    rcases hle.eq_or_lt with heq | hlt
    · rw [← heq, hRdef, annR, radPhi_zero ha hz1] at hF'
      exact lt_irrefl _ hF'
    rcases h.eq_or_lt with heq' | hlt'
    · rw [heq', hR'def, annR', radPhi_zero ha hz2] at hF'
      exact lt_irrefl _ hF'
    have := radPhi_neg_annulus hN ha hlt hlt'
    linarith
  refine ⟨restrictTo B (posPart v),
    restrictTo_mem_H_of_union hBo hS hBS (H_mono hsub hpos), ?_, ?_⟩
  · filter_upwards [restrictTo_fst_ae hBm (posPart v), posPart_fst_ae' v, hv1] with x h1 h2 h3
    rw [h1]
    by_cases hx : x ∈ B
    · rw [indicator_of_mem hx, indicator_of_mem hx, h2, h3, hFB x hx,
        max_eq_left (hBpos x hx).le, one_mul]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx]
  · filter_upwards [restrictTo_snd_ae hBm (posPart v), posPart_snd_ae_ite v, hv1, hv2]
      with x h1 h2 h3 h4
    rw [h1]
    by_cases hx : x ∈ B
    · rw [indicator_of_mem hx, indicator_of_mem hx, h2, h3, h4, hFB x hx,
        if_pos (hBpos x hx), one_smul]
      refine Filter.EventuallyEq.gradient_eq ?_
      filter_upwards [hU.mem_nhds (hBU x hx)] with z hz
      simp only [F, hU1 z hz, one_mul]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx]

/-- **`Φ(· - y)` is a first eigenfunction of the ball `B_R(y)`, and `λ₁(B_R(y)) = a`.** -/
theorem ball_first_eigen (hN : 2 ≤ N) {a : ℝ} (ha : 0 < a) (y : RN N) :
    eigenvalue (ball y (annR N a)) 1 = a ∧
      ∃ φ : Amb N, IsEigenfunction (ball y (annR N a)) φ a ∧
        (φ.1 : RN N → ℝ) =ᵐ[volume]
          (ball y (annR N a)).indicator (fun x => besselEntire N a (x - y)) := by
  obtain ⟨φ, hφH, h1, h2⟩ := exists_ball_phi hN ha y
  have hR : 0 < annR N a := div_pos (besselZero_props (hN_nu hN)).1 (Real.sqrt_pos.mpr ha)
  have hpos : ∀ x ∈ ball y (annR N a), 0 < 1 * besselEntire N a (x - y) := fun x hx => by
    rw [one_mul]
    exact besselEntire_pos hN ha (by
      change ‖x - y‖ < annR N a
      simpa only [mem_ball, dist_eq_norm] using hx)
  have hE : IsEigenfunction (ball y (annR N a)) φ a :=
    ⟨hφH, ne_zero_of_indicator_pos isOpen_ball (nonempty_ball.mpr hR) hpos h1,
      weak_eigen_of_laplacian (contDiff_besselEntire_shift hN ha.le 1 y)
        (laplacian_besselEntire_shift hN ha.le 1 y) h1 h2⟩
  refine ⟨eigenvalue_one_eq_of_nonneg hN (isDomain_ball y hR) hE
    (nonneg_of_indicator_pos hpos h1), φ, hE, ?_⟩
  simpa using h1

/-! ### The annulus -/

/-- **`-Φ(· - y)` is a first eigenfunction of the annulus `R < |x - y| < R'`, and `λ₁ = a`.** -/
theorem annulus_first_eigen (hN : 2 ≤ N) {a : ℝ} (ha : 0 < a) (y : RN N) :
    eigenvalue (annulus N a y) 1 = a ∧
      ∃ ψ : Amb N, IsEigenfunction (annulus N a y) ψ a ∧
        (ψ.1 : RN N → ℝ) =ᵐ[volume]
          (annulus N a y).indicator (fun x => -besselEntire N a (x - y)) := by
  obtain ⟨ψ, hψH, h1, h2⟩ := exists_annulus_psi hN ha y
  have hR := annR_pos hN ha
  have hRR := annR_lt hN ha
  have hP1 : ∀ z : RN N, annP1 N a 1 0 z = (-1) * besselEntire N a z := by
    intro z; simp [annP1, besselEntire_eq_radPhi]
  have h1' : (ψ.1 : RN N → ℝ) =ᵐ[volume]
      (annulus N a y).indicator (fun x => (-1) * besselEntire N a (x - y)) := by
    filter_upwards [h1] with x hx
    rw [hx]
    simp only [hP1]
  have h2' : (ψ.2 : RN N → RN N) =ᵐ[volume]
      (annulus N a y).indicator (gradient (fun x => (-1) * besselEntire N a (x - y))) := by
    filter_upwards [h2] with x hx
    rw [hx]
    by_cases hxA : x ∈ annulus N a y
    · rw [indicator_of_mem hxA, indicator_of_mem hxA]
      have hg := (hasGradientAt_shift hN ha.le y x).gradient
      have hfun : (fun x => (-1) * besselEntire N a (x - y)) =
          fun x => -besselEntire N a (x - y) := by funext z; ring
      rw [hfun, hg]
      simp [annP2]
    · rw [indicator_of_notMem hxA, indicator_of_notMem hxA]
  have hpos : ∀ x ∈ annulus N a y, 0 < (-1) * besselEntire N a (x - y) := fun x hx => by
    rw [besselEntire_eq_radPhi]
    have := radPhi_neg_annulus hN ha hx.1 hx.2
    linarith
  have hne : (annulus N a y).Nonempty := by
    obtain ⟨u, hu⟩ : ∃ u : RN N, ‖u‖ = 1 :=
      ⟨EuclideanSpace.single ⟨0, by omega⟩ 1, by simp [PiLp.norm_single]⟩
    refine ⟨y + ((annR N a + annR' N a) / 2) • u, ?_, ?_⟩ <;>
      simp only [add_sub_cancel_left, norm_smul, hu, mul_one, Real.norm_eq_abs] <;>
      rw [abs_of_pos (by linarith)] <;> linarith
  have hD : IsDomain (annulus N a y) :=
    ⟨⟨isOpen_annulus a y, hne,
      (isBounded_ball (x := y) (r := annR' N a)).subset fun x hx => by
        simpa [dist_eq_norm] using hx.2⟩,
      isConnected_annulus hN y hR.le hRR⟩
  have hE : IsEigenfunction (annulus N a y) ψ a :=
    ⟨hψH, ne_zero_of_indicator_pos (isOpen_annulus a y) hne hpos h1',
      weak_eigen_of_laplacian (contDiff_besselEntire_shift hN ha.le (-1) y)
        (laplacian_besselEntire_shift hN ha.le (-1) y) h1' h2'⟩
  refine ⟨eigenvalue_one_eq_of_nonneg hN hD hE (nonneg_of_indicator_pos hpos h1'), ψ, hE, ?_⟩
  filter_upwards [h1'] with x hx
  rw [hx]
  simp

/-! ### Full ball/annulus data -/

/-- **Ball and annulus data, without the second eigenvalue.** With `ν = N/2 - 1`, `a > 0`,
`R = j_{ν,1}/√a`, `R' = j_{ν,2}/√a`: the Bessel profile `Φ` extends analytically to `ℝ^N`,
solves `-ΔΦ = aΦ`, is positive on `B_R` and negative on the annulus `R < |x| < R'`; `C_N > 1`;
for every ball `B = B_R(y)`, `λ₁(B) = a` with first eigenfunction `Φ(· - y)`, and on the annulus
`A`, `λ₁(A) = a` with first eigenfunction `-Φ(· - y)`.

This is the statement `ext_ball` without the clauses `λ₂(B) = C_N a` and `dim E₂(B) = N`; it is
proved without any external input. -/
theorem ext_ball_basic (hN : 2 ≤ N) {a : ℝ} (ha : 0 < a) :
    let ν : ℝ := (N : ℝ) / 2 - 1
    let R := besselZero ν 1 / Real.sqrt a
    let R' := besselZero ν 2 / Real.sqrt a
    ∃ Φ : RN N → ℝ, AnalyticOnNhd ℝ Φ Set.univ ∧
      (∀ x, x ≠ 0 → Φ x = besselProfile N a x) ∧
      (∀ x, Laplacian.laplacian Φ x = -a * Φ x) ∧
      (∀ x, ‖x‖ < R → 0 < Φ x) ∧
      (∀ x, R < ‖x‖ → ‖x‖ < R' → Φ x < 0) ∧
      0 < R ∧ R < R' ∧ 1 < CN N ∧
      ∀ y : RN N,
        eigenvalue (ball y R) 1 = a ∧
        (∃ φ : Amb N, IsEigenfunction (ball y R) φ a ∧
          (φ.1 : RN N → ℝ) =ᵐ[volume] (ball y R).indicator (fun x => Φ (x - y))) ∧
        (eigenvalue {x | R < ‖x - y‖ ∧ ‖x - y‖ < R'} 1 = a ∧
          ∃ ψ : Amb N, IsEigenfunction {x | R < ‖x - y‖ ∧ ‖x - y‖ < R'} ψ a ∧
          (ψ.1 : RN N → ℝ) =ᵐ[volume]
            {x | R < ‖x - y‖ ∧ ‖x - y‖ < R'}.indicator (fun x => -Φ (x - y))) := by
  intro ν R R'
  obtain ⟨hj1, hj12, hJneg, hC⟩ := ext_bessel hN
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hR : 0 < R := div_pos hj1 hsa
  refine ⟨besselEntire N a, besselEntire_analytic hN ha.le,
    fun _ hx => besselEntire_eq_profile ha hx, besselEntire_laplacian hN ha.le,
    fun x hx => besselEntire_pos hN ha hx, fun x hx1 hx2 => ?_, hR,
    div_lt_div_of_pos_right hj12 hsa, hC, fun y => ?_⟩
  · have hx0 : x ≠ 0 := by
      rintro rfl; simp at hx1; linarith
    refine besselEntire_neg_of_besselJ_neg ha hx0 (hJneg _ ?_ ?_)
    · calc besselZero ν 1 = Real.sqrt a * R := by simp only [R]; field_simp
        _ < Real.sqrt a * ‖x‖ := by gcongr
    · calc Real.sqrt a * ‖x‖ < Real.sqrt a * R' := by gcongr
        _ = besselZero ν 2 := by simp only [R']; field_simp
  · obtain ⟨hB1, φ, hφ, hφ1⟩ := ball_first_eigen hN ha y
    obtain ⟨hA1, ψ, hψ, hψ1⟩ := annulus_first_eigen hN ha y
    exact ⟨hB1, ⟨φ, hφ, hφ1⟩, hA1, ψ, hψ, hψ1⟩

/-- The radius of a ball is determined by its first eigenvalue. -/
lemma ball_radius_eq (hN : 2 ≤ N) {y : RN N} {R a : ℝ} (hR : 0 < R) (ha : 0 < a)
    (h : eigenvalue (ball y R) 1 = a) :
    R = besselZero ((N : ℝ) / 2 - 1) 1 / Real.sqrt a := by
  set j := besselZero ((N : ℝ) / 2 - 1) 1
  obtain ⟨-, -, -, -, -, -, hR0, -, -, -⟩ := ext_ball_basic hN ha
  have hj : 0 < j := by
    have := hR0
    exact (div_pos_iff_of_pos_right (Real.sqrt_pos.mpr ha)).mp this
  set a' := (j / R) ^ 2
  have ha' : 0 < a' := by positivity
  obtain ⟨Φ', _, _, _, _, _, _, _, _, hb'⟩ := ext_ball_basic hN ha'
  have hsq : Real.sqrt a' = j / R := Real.sqrt_sq (by positivity)
  have hrad : j / Real.sqrt a' = R := by rw [hsq]; field_simp
  have h1 := (hb' y).1
  rw [hrad, h] at h1
  rw [h1, hsq]
  field_simp

end FourthRatio

end
