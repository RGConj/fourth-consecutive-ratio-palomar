module

public import RequestProject.WeylSmooth

/-!
# Derivative estimates for harmonic functions

* `laplacian_fderiv_apply` — `Δ(∂_h F) = ∂_h(ΔF)` for smooth `F`;
* `harmonic_iteratedFDeriv` — all partial derivatives of a harmonic function are harmonic;
* `harmonic_grad_bound` — the interior gradient estimate `|∂_h f(y)| ≤ (A/s) M |h|` when
  `|f| ≤ M` on `B̄(y, s)`;
* `harmonic_iteratedFDeriv_bound` — the iterated estimate
  `‖D^k f(y)‖ ≤ M (2 A e / r)^k k!` for `y ∈ B(x₀, r/2)` when `|f| ≤ M` on `B̄(x₀, r)`.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Function Set
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

variable {n : ℕ}

/-! ### The Laplacian commutes with directional derivatives -/

lemma iter3_swap12 {F : RN n → ℝ} (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (x v1 v2 v3 : RN n) :
    iteratedFDeriv ℝ 3 F x ![v1, v2, v3] = iteratedFDeriv ℝ 3 F x ![v2, v1, v3] := by
  have hF' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ F) :=
    hF.fderiv_right (m := (⊤ : ℕ∞)) (WithTop.coe_le_coe.mpr le_top)
  have key : ∀ a b : RN n, iteratedFDeriv ℝ 3 F x ![a, b, v3] =
      iteratedFDeriv ℝ 2 ((ContinuousLinearMap.apply ℝ ℝ v3) ∘ fderiv ℝ F) x ![a, b] := by
    intro a b
    rw [(ContinuousLinearMap.apply ℝ ℝ v3).iteratedFDeriv_comp_left hF'.contDiffAt
      (WithTop.coe_le_coe.mpr le_top), iteratedFDeriv_succ_apply_right]
    have hinit : Fin.init ![a, b, v3] = ![a, b] := by
      funext j; fin_cases j <;> rfl
    rw [hinit]
    rfl
  have hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      ((ContinuousLinearMap.apply ℝ ℝ v3) ∘ fderiv ℝ F) :=
    (ContinuousLinearMap.apply ℝ ℝ v3).contDiff.comp hF'
  have hsym := hG.contDiffAt.isSymmSndFDerivAt (x := x)
    (by simpa using (WithTop.coe_le_coe.mpr (le_top : (2:ℕ∞) ≤ ⊤)))
  rw [key, key]
  exact hsym.iteratedFDeriv_cons

lemma iter3_swap23 {F : RN n → ℝ} (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (x v1 v2 v3 : RN n) :
    iteratedFDeriv ℝ 3 F x ![v1, v2, v3] = iteratedFDeriv ℝ 3 F x ![v1, v3, v2] := by
  have hd2 : DifferentiableAt ℝ (iteratedFDeriv ℝ 2 F) x :=
    hF.contDiffAt.differentiableAt_iteratedFDeriv (WithTop.coe_lt_coe.mpr (ENat.coe_lt_top _))
  have key : ∀ a b : RN n, iteratedFDeriv ℝ 3 F x ![v1, a, b] =
      fderiv ℝ (fun y => iteratedFDeriv ℝ 2 F y ![a, b]) x v1 := by
    intro a b
    rw [iteratedFDeriv_succ_apply_left, fderiv_continuousMultilinear_apply_const_apply hd2]
    have htail : Fin.tail ![v1, a, b] = ![a, b] := by
      funext j; fin_cases j <;> rfl
    rw [htail]
    rfl
  have hsym : (fun y => iteratedFDeriv ℝ 2 F y ![v2, v3]) =
      fun y => iteratedFDeriv ℝ 2 F y ![v3, v2] := by
    funext y
    exact (hF.contDiffAt.isSymmSndFDerivAt (x := y)
      (by simpa using (WithTop.coe_le_coe.mpr (le_top : (2:ℕ∞) ≤ ⊤)))).iteratedFDeriv_cons
  rw [key, key, hsym]

lemma laplacian_fderiv_apply {F : RN n → ℝ} (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (h x : RN n) :
    Laplacian.laplacian (fun y => fderiv ℝ F y h) x = fderiv ℝ (Laplacian.laplacian F) x h := by
  set b := EuclideanSpace.basisFun (Fin n) ℝ
  have hF' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ F) :=
    hF.fderiv_right (m := (⊤ : ℕ∞)) (WithTop.coe_le_coe.mpr le_top)
  have hlap : Laplacian.laplacian F = fun y => ∑ i, iteratedFDeriv ℝ 2 F y ![b i, b i] := by
    funext y
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ b]
  have hd2 : ∀ y, DifferentiableAt ℝ (iteratedFDeriv ℝ 2 F) y := fun y =>
    hF.contDiffAt.differentiableAt_iteratedFDeriv (WithTop.coe_lt_coe.mpr (ENat.coe_lt_top _))
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ b, hlap]
  rw [fderiv_fun_sum (fun i _ => (hd2 x).continuousMultilinear_apply_const _)]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  -- left side
  have e1 : (fun y => fderiv ℝ F y h) = (ContinuousLinearMap.apply ℝ ℝ h) ∘ fderiv ℝ F := rfl
  rw [e1, (ContinuousLinearMap.apply ℝ ℝ h).iteratedFDeriv_comp_left hF'.contDiffAt
    (WithTop.coe_le_coe.mpr le_top)]
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, comp_apply,
    ContinuousLinearMap.apply_apply]
  have e2 := iteratedFDeriv_succ_apply_right (𝕜 := ℝ) (f := F) (x := x) (n := 2) ![b i, b i, h]
  have hinit : Fin.init ![b i, b i, h] = ![b i, b i] := by
    funext j; fin_cases j <;> rfl
  rw [hinit] at e2
  simp only [Fin.last] at e2
  have e2' : iteratedFDeriv ℝ 3 F x ![b i, b i, h] =
      (iteratedFDeriv ℝ 2 (fun y => fderiv ℝ F y) x ![b i, b i]) h := by
    rw [e2]; rfl
  rw [← e2']
  -- right side
  rw [fderiv_continuousMultilinear_apply_const_apply (hd2 x)]
  have e3 := iteratedFDeriv_succ_apply_left (𝕜 := ℝ) (f := F) (x := x) (n := 2) ![h, b i, b i]
  have htail : Fin.tail ![h, b i, b i] = ![b i, b i] := by
    funext j; fin_cases j <;> rfl
  rw [htail] at e3
  have e3' : iteratedFDeriv ℝ 3 F x ![h, b i, b i] =
      (fderiv ℝ (iteratedFDeriv ℝ 2 F) x h) ![b i, b i] := by
    rw [e3]; rfl
  rw [← e3']
  rw [iter3_swap23 hF x (b i) (b i) h, iter3_swap12 hF x (b i) h (b i)]

/-- A smooth function on an open set which is harmonic there. -/
def HarmOn (U : Set (RN n)) (f : RN n → ℝ) : Prop :=
  ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f U ∧ ∀ x ∈ U, Laplacian.laplacian f x = 0

lemma HarmOn.congr {U : Set (RN n)} (hU : IsOpen U) {f g : RN n → ℝ} (hf : HarmOn U f)
    (h : ∀ x ∈ U, f x = g x) : HarmOn U g := by
  refine ⟨hf.1.congr fun x hx => (h x hx).symm, fun x hx => ?_⟩
  rw [← laplacian_eq_of_eqOn_open hU h hx]
  exact hf.2 x hx

/-- Directional derivatives of harmonic functions are harmonic. -/
lemma HarmOn.fderiv_apply {U : Set (RN n)} (hU : IsOpen U) {f : RN n → ℝ} (hf : HarmOn U f)
    (h : RN n) : HarmOn U (fun y => fderiv ℝ f y h) := by
  refine ⟨(hf.1.fderiv_of_isOpen hU (m := (⊤ : ℕ∞)) (by exact_mod_cast le_top)).clm_apply
    contDiffOn_const, fun x hx => ?_⟩
  obtain ⟨F, hF, -, -, V, hVo, hxV, hFV⟩ :=
    exists_smooth_extension hU isCompact_singleton (singleton_subset_iff.mpr hx) hf.1
  have hxV' : x ∈ V := hxV rfl
  have hev : F =ᶠ[𝓝 x] f := by
    filter_upwards [hVo.mem_nhds hxV'] with z hz
    exact hFV z hz
  have hev' : ∀ z ∈ V, fderiv ℝ F z h = fderiv ℝ f z h := by
    intro z hz
    have : F =ᶠ[𝓝 z] f := by
      filter_upwards [hVo.mem_nhds hz] with w hw
      exact hFV w hw
    rw [this.fderiv_eq]
  rw [← laplacian_eq_of_eqOn_open hVo hev' hxV', laplacian_fderiv_apply hF]
  have h0 : Laplacian.laplacian F =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [(hVo.inter hU).mem_nhds ⟨hxV', hx⟩] with z hz
    rw [laplacian_eq_of_eqOn_open hVo hFV hz.1]
    exact hf.2 z hz.2
  rw [h0.fderiv_eq]
  simp

/-- All partial derivatives of a harmonic function are harmonic. -/
lemma HarmOn.iterDeriv {U : Set (RN n)} (hU : IsOpen U) {f : RN n → ℝ} (hf : HarmOn U f)
    (j : ℕ) (v : Fin j → RN n) : HarmOn U (fun y => iteratedFDeriv ℝ j f y v) := by
  induction j with
  | zero =>
    refine hf.congr hU fun x _ => ?_
    simp
  | succ j ih =>
    have h1 := (ih (Fin.tail v)).fderiv_apply hU (v 0)
    refine h1.congr hU fun x hx => ?_
    rw [iteratedFDeriv_succ_apply_left]
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ j f) x :=
      (hf.1.contDiffAt (hU.mem_nhds hx)).differentiableAt_iteratedFDeriv
        (WithTop.coe_lt_coe.mpr (ENat.coe_lt_top _))
    rw [fderiv_continuousMultilinear_apply_const_apply hd]

/-! ### The gradient estimate -/

/-- The constant `A_n = 2 ∫ |∇ kern_1|` of the gradient estimate. -/
def gradConst (n : ℕ) : ℝ := 2 * ∫ z, ‖fderiv ℝ (kern n 1) z‖

lemma fderiv_kern_scale {t : ℝ} (ht : 0 < t) (z : RN n) :
    fderiv ℝ (kern n t) z = ((t ^ n)⁻¹ * t⁻¹) • fderiv ℝ (kern n 1) (t⁻¹ • z) := by
  have hfun : kern n t = fun z => (t ^ n)⁻¹ * kern n 1 (t⁻¹ • z) := funext (kern_scale ht)
  have hd : DifferentiableAt ℝ (kern n 1) (t⁻¹ • z) :=
    (contDiff_kern 1).differentiable (by simp) _
  have h1 : HasFDerivAt (fun z : RN n => kern n 1 (t⁻¹ • z))
      ((fderiv ℝ (kern n 1) (t⁻¹ • z)).comp (t⁻¹ • ContinuousLinearMap.id ℝ (RN n))) z := by
    refine hd.hasFDerivAt.comp z ?_
    exact (ContinuousLinearMap.id ℝ (RN n)).hasFDerivAt.const_smul t⁻¹
  rw [hfun, (h1.const_mul (t ^ n)⁻¹).fderiv]
  ext v
  simp [smul_smul, mul_comm]

lemma integral_norm_fderiv_kern {t : ℝ} (ht : 0 < t) :
    ∫ z, ‖fderiv ℝ (kern n t) z‖ = t⁻¹ * ∫ z, ‖fderiv ℝ (kern n 1) z‖ := by
  simp_rw [fderiv_kern_scale ht, norm_smul, Real.norm_eq_abs,
    abs_of_pos (show 0 < (t ^ n)⁻¹ * t⁻¹ by positivity)]
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg volume
    (fun z => ‖fderiv ℝ (kern n 1) z‖) ht.le, finrank_euclideanSpace_fin, smul_eq_mul]
  field_simp

lemma continuous_fderiv_kern (t : ℝ) : Continuous (fderiv ℝ (kern n t)) :=
  (contDiff_kern t).continuous_fderiv (by simp)

lemma hasCompactSupport_fderiv_kern {t : ℝ} (ht : 0 < t) :
    HasCompactSupport (fderiv ℝ (kern n t)) :=
  (hasCompactSupport_kern ht).fderiv (𝕜 := ℝ)

lemma integrable_norm_fderiv_kern {t : ℝ} (ht : 0 < t) (M : ℝ) :
    Integrable (fun τ => ‖fderiv ℝ (kern n t) τ‖ * M) := by
  have hc : Continuous (fderiv ℝ (kern n t)) := continuous_fderiv_kern t
  have h1 : HasCompactSupport (fderiv ℝ (kern n t)) := hasCompactSupport_fderiv_kern ht
  have h2 : Integrable (fun τ => ‖fderiv ℝ (kern n t) τ‖) :=
    (hc.integrable_of_hasCompactSupport h1).norm
  exact h2.mul_const M

lemma norm_fderiv_meanK_le {t : ℝ} (ht : 0 < t) {g : RN n → ℝ} (hg : LocallyIntegrable g)
    {M : ℝ} (hM0 : 0 ≤ M) (hb : ∀ z, |g z| ≤ M) (y : RN n) :
    ‖fderiv ℝ (meanK n t g) y‖ ≤ M * ∫ z, ‖fderiv ℝ (kern n t) z‖ := by
  have hG := (hasCompactSupport_kern ht).hasFDerivAt_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) ((contDiff_kern (n := n) t).of_le (by simp)) hg y
  unfold meanK
  rw [hG.fderiv, convolution_def]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hbound : ∀ τ, ‖(ContinuousLinearMap.precompL (RN n) (ContinuousLinearMap.lsmul ℝ ℝ))
      (fderiv ℝ (kern n t) τ) (g (y - τ))‖ ≤ ‖fderiv ℝ (kern n t) τ‖ * M := by
    intro τ
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    simp only [ContinuousLinearMap.precompL_apply, ContinuousLinearMap.lsmul_apply,
      smul_eq_mul, norm_mul]
    have h1 : ‖g (y - τ)‖ ≤ M := by rw [Real.norm_eq_abs]; exact hb _
    have h2 := (fderiv ℝ (kern n t) τ).le_opNorm v
    calc ‖fderiv ℝ (kern n t) τ v‖ * ‖g (y - τ)‖
        ≤ (‖fderiv ℝ (kern n t) τ‖ * ‖v‖) * M :=
          mul_le_mul h2 h1 (norm_nonneg _) (by positivity)
      _ = ‖fderiv ℝ (kern n t) τ‖ * M * ‖v‖ := by ring
  refine (integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
    (integrable_norm_fderiv_kern ht M) (Eventually.of_forall hbound)).trans (le_of_eq ?_)
  rw [integral_mul_const, mul_comm]

/-- **Interior gradient estimate** for harmonic functions. -/
theorem harmonic_grad_bound (hn : 1 ≤ n) {U : Set (RN n)} (hU : IsOpen U) {f : RN n → ℝ}
    (hf : HarmOn U f) {y : RN n} {s : ℝ} (hs : 0 < s) (hsub : closedBall y s ⊆ U) {M : ℝ}
    (hM : ∀ z ∈ closedBall y s, |f z| ≤ M) :
    ‖fderiv ℝ f y‖ ≤ gradConst n / s * M := by
  set t := s / 2 with htdef
  have ht : 0 < t := by positivity
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM y (mem_closedBall_self hs.le))
  have hli : LocallyIntegrable ((closedBall y s).indicator f) :=
    locallyIntegrable_indicator (hf.1.continuousOn.locallyIntegrableOn hU.measurableSet) hsub
  have hev : meanK n t ((closedBall y s).indicator f) =ᶠ[𝓝 y] f := by
    filter_upwards [ball_mem_nhds y ht] with z hz
    have hs' : closedBall z t ⊆ closedBall y s := by
      intro w hw
      rw [mem_closedBall] at hw ⊢
      rw [mem_ball] at hz
      linarith [dist_triangle w z y]
    rw [meanK_indicator ht hs', ← harmonic_mean_value hn hU hf.1 hf.2 ht (hs'.trans hsub)]
  have hb : ∀ z, |(closedBall y s).indicator f z| ≤ M := by
    intro z
    by_cases hm : z ∈ closedBall y s
    · rw [indicator_of_mem hm]; exact hM _ hm
    · rw [indicator_of_notMem hm, abs_zero]; exact hM0
  rw [← hev.fderiv_eq]
  refine (norm_fderiv_meanK_le ht hli hM0 hb y).trans (le_of_eq ?_)
  rw [integral_norm_fderiv_kern ht, gradConst, htdef]
  field_simp

/-! ### Iterated estimates -/

lemma harmonic_iter_bound_aux (hn : 1 ≤ n) {U : Set (RN n)} (hU : IsOpen U) {f : RN n → ℝ}
    (hf : HarmOn U f) {x0 : RN n} {r : ℝ} (hsub : closedBall x0 r ⊆ U) {M : ℝ}
    (hM : ∀ z ∈ closedBall x0 r, |f z| ≤ M) {s : ℝ} (hs : 0 < s) (j : ℕ) :
    ∀ y, closedBall y (j * s) ⊆ closedBall x0 r → ∀ v : Fin j → RN n,
      |iteratedFDeriv ℝ j f y v| ≤ M * (gradConst n / s) ^ j * ∏ i, ‖v i‖ := by
  induction j with
  | zero =>
    intro y hy v
    simp only [CharP.cast_eq_zero, zero_mul, closedBall_zero, singleton_subset_iff] at hy
    simp [hM y hy]
  | succ j ih =>
    intro y hy v
    have hyU : y ∈ U := hsub (hy (mem_closedBall_self (by positivity)))
    have hF := (hf.iterDeriv hU j (Fin.tail v))
    have hball : closedBall y s ⊆ U := by
      refine (closedBall_subset_closedBall ?_).trans (hy.trans hsub)
      push_cast; nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    have hb := harmonic_grad_bound hn hU hF hs hball
      (M := M * (gradConst n / s) ^ j * ∏ i, ‖Fin.tail v i‖) (fun z hz => by
        refine ih z (fun w hw => hy ?_) _
        rw [mem_closedBall] at hz hw ⊢
        push_cast
        linarith [dist_triangle w z y])
    rw [iteratedFDeriv_succ_apply_left]
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ j f) y :=
      (hf.1.contDiffAt (hU.mem_nhds hyU)).differentiableAt_iteratedFDeriv
        (WithTop.coe_lt_coe.mpr (ENat.coe_lt_top _))
    rw [← fderiv_continuousMultilinear_apply_const_apply hd]
    calc |fderiv ℝ (fun z => iteratedFDeriv ℝ j f z (Fin.tail v)) y (v 0)|
        ≤ ‖fderiv ℝ (fun z => iteratedFDeriv ℝ j f z (Fin.tail v)) y‖ * ‖v 0‖ := by
          rw [← Real.norm_eq_abs]; exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ (gradConst n / s * (M * (gradConst n / s) ^ j * ∏ i, ‖Fin.tail v i‖)) * ‖v 0‖ := by
          gcongr
      _ = M * (gradConst n / s) ^ (j + 1) * ∏ i, ‖v i‖ := by
          rw [Fin.prod_univ_succ]
          simp only [Fin.tail]
          ring

/-- **Iterated interior estimates.** If `f` is harmonic on `U ⊇ B̄(x₀, r)` and `|f| ≤ M` there,
then `‖D^k f(y)‖ ≤ M (2 A_n e / r)^k k!` for `y ∈ B(x₀, r/2)`. -/
theorem harmonic_iteratedFDeriv_bound (hn : 1 ≤ n) {U : Set (RN n)} (hU : IsOpen U)
    {f : RN n → ℝ} (hf : HarmOn U f) {x0 : RN n} {r : ℝ} (hr : 0 < r)
    (hsub : closedBall x0 r ⊆ U) {M : ℝ} (hM : ∀ z ∈ closedBall x0 r, |f z| ≤ M) :
    ∀ y ∈ ball x0 (r / 2), ∀ k : ℕ,
      ‖iteratedFDeriv ℝ k f y‖ ≤ M * (2 * gradConst n * Real.exp 1 / r) ^ k * k.factorial := by
  intro y hy k
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM x0 (mem_closedBall_self hr.le))
  have hA : 0 ≤ gradConst n := by
    unfold gradConst; exact mul_nonneg zero_le_two (integral_nonneg fun _ => norm_nonneg _)
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one]
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    exact hM y (ball_subset_closedBall (ball_subset_ball (by linarith) hy))
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  set s := r / (2 * k) with hsdef
  have hs : 0 < s := by positivity
  have hball : closedBall y (k * s) ⊆ closedBall x0 r := by
    intro w hw
    rw [mem_closedBall] at hw ⊢
    rw [mem_ball] at hy
    have : (k : ℝ) * s = r / 2 := by rw [hsdef]; field_simp
    linarith [dist_triangle w y x0]
  have hb := harmonic_iter_bound_aux hn hU hf hsub hM hs k y hball
  have hnorm : ‖iteratedFDeriv ℝ k f y‖ ≤ M * (gradConst n / s) ^ k :=
    ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun v => by
      rw [Real.norm_eq_abs]; exact hb v
  refine hnorm.trans ?_
  have hkk : (k : ℝ) ^ k ≤ Real.exp 1 ^ k * k.factorial := by
    have := Real.pow_div_factorial_le_exp (k : ℝ) hkpos.le k
    rw [div_le_iff₀ (by positivity), ← Real.exp_one_pow] at this
    exact this
  have e : gradConst n / s = 2 * gradConst n / r * k := by
    rw [hsdef]; field_simp
  rw [e, mul_pow, mul_assoc]
  gcongr M * ?_
  calc (2 * gradConst n / r) ^ k * (k : ℝ) ^ k
      ≤ (2 * gradConst n / r) ^ k * (Real.exp 1 ^ k * k.factorial) := by gcongr
    _ = (2 * gradConst n * Real.exp 1 / r) ^ k * k.factorial := by
        rw [div_pow, div_pow, mul_pow]; ring

end FourthRatio

end
