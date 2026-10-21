module

public import RequestProject.Defs

/-!
# The entire Bessel profile

The radial Bessel profile `Φ(x) = |x|^{-ν} J_ν(√a |x|)` (`ν = N/2 - 1`) of the ball/annulus
external lemma is, up to the factor `(√a/2)^ν`, the entire power series
`Σ_m (-1)^m (a/4)^m / (m! Γ(m+ν+1)) · |x|^{2m}` in `|x|²`.  Here we prove, from the definitions
alone, the analytic part of that external lemma:

* `besselEntire_analytic` — `Φ` (defined at `0` by the series) is real analytic on `ℝ^N`;
* `besselEntire_eq_profile` — it agrees with `besselProfile N a` away from the origin;
* `besselEntire_laplacian` — it solves `ΔΦ = -aΦ` on all of `ℝ^N`;
* `besselEntire_pos` — `Φ > 0` on the ball `|x| < j_{ν,1}/√a` (from the definition of `j_{ν,1}`
  as the first positive zero of `J_ν`);
* `besselEntire_neg_of_besselJ_neg` — `Φ(x) < 0` wherever `J_ν(√a|x|) < 0`.
-/

@[expose] public section

open InnerProductSpace Nat Metric
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

/-! ### Generic facts on power series with factorially decaying coefficients -/

lemma summable_bound_shift (K α R : ℝ) :
    Summable (fun n : ℕ => K * α ^ n / (n ! : ℝ) * (n * R ^ (n - 1))) := by
  rw [← summable_nat_add_iff 1]
  have h := (Real.summable_pow_div_factorial (α * R)).mul_left (K * α)
  refine h.congr fun k => ?_
  simp only [Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    pow_succ, mul_pow]
  have : (k ! : ℝ) ≠ 0 := by positivity
  field_simp

lemma hasDerivAt_powSeries (c : ℕ → ℝ) {K α : ℝ} (hc : ∀ m, |c m| ≤ K * α ^ m / (m ! : ℝ))
    (s : ℝ) :
    HasDerivAt (fun s => ∑' m, c m * s ^ m) (∑' m : ℕ, ((m : ℝ) + 1) * c (m + 1) * s ^ m) s := by
  set R := |s| + 1
  have hR : 0 ≤ R := by positivity
  have hu := summable_bound_shift K α R
  have key := hasDerivAt_tsum_of_isPreconnected (g := fun n y => c n * y ^ n)
    (g' := fun n y => c n * (n * y ^ (n - 1))) (t := Metric.ball 0 R) (y₀ := 0) (y := s) hu
    Metric.isOpen_ball (convex_ball _ _).isPreconnected
    (fun n y _ => (hasDerivAt_pow n y).const_mul (c n))
    (fun n y hy => by
      rw [mem_ball_zero_iff, Real.norm_eq_abs] at hy
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, Nat.abs_cast]
      gcongr
      · exact le_trans (abs_nonneg _) (hc n)
      · exact hc n)
    (Metric.mem_ball_self (by positivity))
    (by
      refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
      simp at hn; simp [zero_pow hn])
    (by rw [mem_ball_zero_iff, Real.norm_eq_abs]; simp [R])
  convert key using 1
  have hsum : Summable (fun n : ℕ => c n * (n * s ^ (n - 1))) := by
    refine Summable.of_norm_bounded hu fun n => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, Nat.abs_cast]
    gcongr
    · exact le_trans (abs_nonneg _) (hc n)
    · exact hc n
    · simp [R]
  rw [hsum.tsum_eq_zero_add]
  simp only [CharP.cast_eq_zero, zero_mul, mul_zero, zero_add, Nat.add_sub_cancel, Nat.cast_add,
    Nat.cast_one]
  congr 1; funext m; ring

lemma summable_abs_powSeries (c : ℕ → ℝ) {K α : ℝ} (hc : ∀ m, |c m| ≤ K * α ^ m / (m ! : ℝ))
    (s : ℝ) : Summable (fun m => |c m| * |s| ^ m) := by
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
    ((Real.summable_pow_div_factorial (α * |s|)).mul_left K)
  calc |c m| * |s| ^ m ≤ K * α ^ m / (m ! : ℝ) * |s| ^ m := by gcongr; exact hc m
    _ = K * ((α * |s|) ^ m / (m ! : ℝ)) := by rw [mul_pow]; ring

lemma summable_powSeries (c : ℕ → ℝ) {K α : ℝ} (hc : ∀ m, |c m| ≤ K * α ^ m / (m ! : ℝ))
    (s : ℝ) : Summable (fun m => c m * s ^ m) :=
  Summable.of_norm (by simpa [Real.norm_eq_abs, abs_mul, abs_pow] using
    summable_abs_powSeries c hc s)

lemma derivCoef_bound (c : ℕ → ℝ) {K α : ℝ} (hc : ∀ m, |c m| ≤ K * α ^ m / (m ! : ℝ)) (m : ℕ) :
    |((m : ℝ) + 1) * c (m + 1)| ≤ (K * α) * α ^ m / (m ! : ℝ) := by
  rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < m + 1)]
  calc ((m : ℝ) + 1) * |c (m + 1)| ≤ ((m : ℝ) + 1) * (K * α ^ (m + 1) / ((m + 1) ! : ℝ)) := by
        gcongr; exact hc _
    _ = (K * α) * α ^ m / (m ! : ℝ) := by
        rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]; push_cast
        have : (m ! : ℝ) ≠ 0 := by positivity
        field_simp

/-! ### The Bessel coefficients -/

/-- Coefficients of the entire series `Σ c_m s^m` with `|x|^{-ν} J_ν(√a |x|) = (√a/2)^ν Σ c_m |x|^{2m}`. -/
def besselCoef (ν a : ℝ) (m : ℕ) : ℝ :=
  (-1) ^ m * (a / 4) ^ m / ((m ! : ℝ) * Real.Gamma (m + ν + 1))

lemma Gamma_le_Gamma_add {ν : ℝ} (hν : 0 ≤ ν) (m : ℕ) :
    Real.Gamma (ν + 1) ≤ Real.Gamma (m + ν + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hpos : 0 < (m : ℝ) + ν + 1 := by positivity
    have h1 : Real.Gamma ((m + 1 : ℕ) + ν + 1) = ((m : ℝ) + ν + 1) * Real.Gamma (m + ν + 1) := by
      rw [← Real.Gamma_add_one hpos.ne']; push_cast; ring_nf
    have hg : 0 < Real.Gamma (m + ν + 1) := Real.Gamma_pos_of_pos hpos
    rw [h1]; nlinarith

lemma besselCoef_bound {ν a : ℝ} (hν : 0 ≤ ν) (ha : 0 ≤ a) (m : ℕ) :
    |besselCoef ν a m| ≤ (Real.Gamma (ν + 1))⁻¹ * (a / 4) ^ m / (m ! : ℝ) := by
  have hg0 : 0 < Real.Gamma (ν + 1) := Real.Gamma_pos_of_pos (by positivity)
  have hg := Gamma_le_Gamma_add hν m
  have hgm : 0 < Real.Gamma (m + ν + 1) := lt_of_lt_of_le hg0 hg
  unfold besselCoef
  rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_pow,
    abs_of_nonneg (by positivity : 0 ≤ a / 4), abs_of_pos (by positivity)]
  rw [div_le_iff₀ (by positivity)]
  have hf : (0 : ℝ) < m ! := by positivity
  calc (a / 4) ^ m = (Real.Gamma (ν + 1))⁻¹ * (a / 4) ^ m / (m ! : ℝ) *
        ((m ! : ℝ) * Real.Gamma (ν + 1)) := by field_simp
    _ ≤ _ := by gcongr

lemma besselCoef_succ {ν : ℝ} (hν : 0 ≤ ν) (a : ℝ) (m : ℕ) :
    ((m : ℝ) + 1) * ((m : ℝ) + ν + 1) * besselCoef ν a (m + 1) = -(a / 4) * besselCoef ν a m := by
  have hpos : 0 < (m : ℝ) + ν + 1 := by positivity
  have h1 : Real.Gamma ((m + 1 : ℕ) + ν + 1) = ((m : ℝ) + ν + 1) * Real.Gamma (m + ν + 1) := by
    rw [← Real.Gamma_add_one hpos.ne']; push_cast; ring_nf
  have hgm : 0 < Real.Gamma (m + ν + 1) := Real.Gamma_pos_of_pos hpos
  unfold besselCoef
  rw [h1, Nat.factorial_succ, Nat.cast_mul, pow_succ, pow_succ]
  have hf : (0 : ℝ) < m ! := by positivity
  push_cast
  field_simp


/-- Laplacian of a radial function `x ↦ G(|x|²)`. -/
lemma laplacian_radial_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι]
    (v : OrthonormalBasis ι ℝ E) (G G' G'' : ℝ → ℝ)
    (hG : ∀ s, HasDerivAt G (G' s) s) (hG' : ∀ s, HasDerivAt G' (G'' s) s) (x : E) :
    Laplacian.laplacian (fun z : E => G (‖z‖ ^ 2)) x =
      2 * Fintype.card ι * G' (‖x‖^2) + 4 * ‖x‖^2 * G'' (‖x‖^2) := by
  have hd : ∀ y : E, HasFDerivAt (fun z => G (‖z‖ ^ 2)) (G' (‖y‖^2) • (2 • innerSL ℝ y)) y := by
    intro y
    exact (hG _).comp_hasFDerivAt y (hasStrictFDerivAt_norm_sq y).hasFDerivAt
  have hf : (fun y => fderiv ℝ (fun z => G (‖z‖ ^ 2)) y) =
      fun y => G' (‖y‖^2) • ((2 • innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ) y) := by
    funext y; rw [(hd y).fderiv]; simp
  have h1 : HasFDerivAt (fun y : E => G' (‖y‖^2)) (G'' (‖x‖^2) • (2 • innerSL ℝ x)) x :=
    (hG' _).comp_hasFDerivAt x (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have h2 := (2 • innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).hasFDerivAt (x := x)
  have h3 : HasFDerivAt (fun y => fderiv ℝ (fun z => G (‖z‖ ^ 2)) y)
      ((G' (‖x‖^2)) • (2 • innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ) +
        (ContinuousLinearMap.smulRight ((G'' (‖x‖^2)) • (2 • innerSL ℝ x)) (2 • innerSL ℝ x))) x := by
    rw [hf]; convert h1.smul h2 using 1
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis _ v]
  simp only [iteratedFDeriv_two_apply, h3.fderiv]
  simp [Finset.sum_add_distrib, innerSL_apply_apply]
  have hs : ∑ i, ⟪x, v i⟫ * ⟪x, v i⟫ = ‖x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← v.sum_inner_mul_inner x x]
    simp [real_inner_comm]
  have : ∑ i, G'' (‖x‖ ^ 2) * (2 * ⟪x, v i⟫) * (2 * ⟪x, v i⟫) =
      4 * G'' (‖x‖ ^ 2) * ∑ i, ⟪x, v i⟫ * ⟪x, v i⟫ := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring
  rw [this, hs]
  have hdiag (i : ι) : (innerSL ℝ (v i)) (v i) = 1 := v.inner_eq_one i
  simp [hdiag] <;> ring

/-- The entire series `g(s) = Σ c_m s^m`. -/
def besselSeries (ν a s : ℝ) : ℝ := ∑' m, besselCoef ν a m * s ^ m

/-- The analytic extension of the Bessel profile to all of `ℝ^N`:
`Φ(x) = (√a/2)^ν g(|x|²)`, `ν = N/2 - 1`. -/
def besselEntire (N : ℕ) (a : ℝ) (x : RN N) : ℝ :=
  (Real.sqrt a / 2) ^ ((N : ℝ) / 2 - 1) * besselSeries ((N : ℝ) / 2 - 1) a (‖x‖ ^ 2)

lemma powSeries_ode_aux (c : ℕ → ℝ) {K α ν a : ℝ} (hc : ∀ m, |c m| ≤ K * α ^ m / (m ! : ℝ))
    (hrec : ∀ m : ℕ, ((m : ℝ) + 1) * ((m : ℝ) + ν + 1) * c (m + 1) = -(a / 4) * c m) (s : ℝ) :
    2 * (2 * ν + 2) * (∑' m : ℕ, ((m : ℝ) + 1) * c (m + 1) * s ^ m) +
      4 * s * (∑' m : ℕ, ((m : ℝ) + 1) * (((m + 1 : ℕ) : ℝ) + 1) * c (m + 1 + 1) * s ^ m) =
      -a * ∑' m, c m * s ^ m := by
  obtain ⟨d, hd_def⟩ : ∃ d : ℕ → ℝ, d = fun m : ℕ => ((m : ℝ) + 1) * c (m + 1) := ⟨_, rfl⟩
  have hdm : ∀ m : ℕ, d m = ((m : ℝ) + 1) * c (m + 1) := fun m => by rw [hd_def]
  have hd : ∀ m : ℕ, |d m| ≤ (K * α) * α ^ m / (m ! : ℝ) := fun m => by
    rw [hdm]; exact derivCoef_bound c hc m
  have he : ∀ m : ℕ, |((m : ℝ) + 1) * d (m + 1)| ≤ (K * α * α) * α ^ m / (m ! : ℝ) :=
    derivCoef_bound d hd
  have hsE := summable_powSeries _ he s
  have hsD := summable_powSeries _ hd s
  have hshift : Summable (fun m : ℕ => ((m + 1 : ℕ) : ℝ) * d (m + 1) * s ^ (m + 1)) :=
    (hsE.mul_left s).congr (fun m => by push_cast; ring)
  have hn : Summable (fun n : ℕ => (n : ℝ) * d n * s ^ n) :=
    (summable_nat_add_iff 1).mp hshift
  have heq : ∑' n : ℕ, (n : ℝ) * d n * s ^ n =
      s * ∑' m : ℕ, ((m : ℝ) + 1) * d (m + 1) * s ^ m := by
    rw [tsum_eq_zero_add' (f := fun n : ℕ => (n : ℝ) * d n * s ^ n) hshift, ← tsum_mul_left]
    simp only [CharP.cast_eq_zero, zero_mul, zero_add]
    congr 1; funext m; push_cast; ring
  have e1 : (∑' m : ℕ, ((m : ℝ) + 1) * (((m + 1 : ℕ) : ℝ) + 1) * c (m + 1 + 1) * s ^ m) =
      ∑' m : ℕ, ((m : ℝ) + 1) * d (m + 1) * s ^ m := by
    congr 1; funext m; rw [hdm]; push_cast; ring
  have e2 : (∑' m : ℕ, ((m : ℝ) + 1) * c (m + 1) * s ^ m) = ∑' m : ℕ, d m * s ^ m := by
    congr 1; funext m; rw [hdm]
  rw [e1, e2, mul_assoc 4 s, ← heq, ← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left,
    ← (hsD.mul_left _).tsum_add (hn.mul_left _)]
  congr 1; funext n
  rw [hdm]
  linear_combination 4 * s ^ n * hrec n

lemma besselSeries_ode {ν a : ℝ} (hν : 0 ≤ ν) (ha : 0 ≤ a) (s : ℝ) :
    2 * (2 * ν + 2) * (∑' m : ℕ, ((m : ℝ) + 1) * besselCoef ν a (m + 1) * s ^ m) +
      4 * s * (∑' m : ℕ, ((m : ℝ) + 1) * (((m + 1 : ℕ) : ℝ) + 1) * besselCoef ν a (m + 1 + 1) *
        s ^ m) = -a * besselSeries ν a s :=
  powSeries_ode_aux _ (besselCoef_bound hν ha) (besselCoef_succ hν a) s

lemma hasDerivAt_besselSeries {ν a : ℝ} (hν : 0 ≤ ν) (ha : 0 ≤ a) (s : ℝ) :
    HasDerivAt (besselSeries ν a)
      (∑' m : ℕ, ((m : ℝ) + 1) * besselCoef ν a (m + 1) * s ^ m) s :=
  hasDerivAt_powSeries _ (besselCoef_bound hν ha) s

lemma hasDerivAt_besselSeries_deriv {ν a : ℝ} (hν : 0 ≤ ν) (ha : 0 ≤ a) (s : ℝ) :
    HasDerivAt (fun s => ∑' m : ℕ, ((m : ℝ) + 1) * besselCoef ν a (m + 1) * s ^ m)
      (∑' m : ℕ, ((m : ℝ) + 1) * (((m + 1 : ℕ) : ℝ) + 1) * besselCoef ν a (m + 1 + 1) *
        s ^ m) s := by
  have := hasDerivAt_powSeries (fun m => ((m : ℝ) + 1) * besselCoef ν a (m + 1))
    (derivCoef_bound _ (besselCoef_bound hν ha)) s
  convert this using 1
  · congr 1; funext m; ring

/-- `ΔΦ = -aΦ` on all of `ℝ^N`. -/
theorem besselEntire_laplacian {N : ℕ} (hN : 2 ≤ N) {a : ℝ} (ha : 0 ≤ a) (x : RN N) :
    Laplacian.laplacian (besselEntire N a) x = -a * besselEntire N a x := by
  set ν : ℝ := (N : ℝ) / 2 - 1
  have hν : 0 ≤ ν := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    simp only [ν]; linarith
  set K := (Real.sqrt a / 2) ^ ν
  have h := laplacian_radial_sq (EuclideanSpace.basisFun (Fin N) ℝ)
    (fun s => K * besselSeries ν a s)
    (fun s => K * ∑' m : ℕ, ((m : ℝ) + 1) * besselCoef ν a (m + 1) * s ^ m)
    (fun s => K * ∑' m : ℕ, ((m : ℝ) + 1) * (((m + 1 : ℕ) : ℝ) + 1) *
      besselCoef ν a (m + 1 + 1) * s ^ m)
    (fun s => (hasDerivAt_besselSeries hν ha s).const_mul K)
    (fun s => (hasDerivAt_besselSeries_deriv hν ha s).const_mul K) x
  change Laplacian.laplacian (fun z : RN N => K * besselSeries ν a (‖z‖ ^ 2)) x =
    -a * (K * besselSeries ν a (‖x‖ ^ 2))
  rw [h, Fintype.card_fin]
  have hN' : (N : ℝ) = 2 * ν + 2 := by simp only [ν]; ring
  rw [hN']
  linear_combination K * besselSeries_ode hν ha (‖x‖ ^ 2)

lemma analyticAt_besselSeries {ν a : ℝ} (hν : 0 ≤ ν) (ha : 0 ≤ a) (s : ℝ) :
    AnalyticAt ℝ (besselSeries ν a) s := by
  set p := FormalMultilinearSeries.ofScalars ℝ (besselCoef ν a)
  have hrad : p.radius = ⊤ := by
    refine p.radius_eq_top_of_summable_norm fun r => ?_
    simp only [p, FormalMultilinearSeries.ofScalars_norm, Real.norm_eq_abs]
    simpa [abs_of_nonneg r.coe_nonneg] using
      summable_abs_powSeries _ (besselCoef_bound hν ha) (r : ℝ)
  have hsum : besselSeries ν a = p.sum := by
    funext t
    change _ = FormalMultilinearSeries.ofScalarsSum (besselCoef ν a) t
    rw [FormalMultilinearSeries.ofScalarsSum_eq_tsum]
    simp [besselSeries, smul_eq_mul]
  rw [hsum]
  have hp := p.hasFPowerSeriesOnBall (by rw [hrad]; exact ENNReal.zero_lt_top)
  rw [hrad] at hp
  exact hp.analyticAt_of_mem (by simp)

/-- `Φ` is real analytic on all of `ℝ^N`. -/
theorem besselEntire_analytic {N : ℕ} (hN : 2 ≤ N) {a : ℝ} (ha : 0 ≤ a) :
    AnalyticOnNhd ℝ (besselEntire N a) Set.univ := by
  intro x _
  have hν : 0 ≤ (N : ℝ) / 2 - 1 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hsq : AnalyticAt ℝ (fun z : RN N => ‖z‖ ^ 2) x := by
    have h1 := (innerSL ℝ : RN N →L[ℝ] RN N →L[ℝ] ℝ).analyticAt_bilinear (x, x)
    have h2 : AnalyticAt ℝ (fun z : RN N => (z, z)) x := analyticAt_id.prod analyticAt_id
    have h3 : AnalyticAt ℝ ((fun p : RN N × RN N => innerSL ℝ p.1 p.2) ∘
        (fun z : RN N => (z, z))) x :=
      AnalyticAt.comp (g := fun p : RN N × RN N => innerSL ℝ p.1 p.2)
        (f := fun z : RN N => (z, z)) h1 h2
    convert h3 using 1
    funext z; simp
  exact analyticAt_const.mul ((analyticAt_besselSeries hν ha _).comp hsq)

/-- Away from the origin `Φ` is the Bessel profile `|x|^{-ν} J_ν(√a |x|)`. -/
theorem besselEntire_eq_profile {N : ℕ} {a : ℝ} (ha : 0 < a) {x : RN N} (hx : x ≠ 0) :
    besselEntire N a x = besselProfile N a x := by
  set ν : ℝ := (N : ℝ) / 2 - 1
  set r := ‖x‖
  have hr : 0 < r := norm_pos_iff.mpr hx
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  unfold besselEntire besselProfile besselJ besselSeries
  change (Real.sqrt a / 2) ^ ν * ∑' m, besselCoef ν a m * (r ^ 2) ^ m =
    r ^ (-ν) * ∑' m : ℕ, (-1 : ℝ) ^ m / ((m ! : ℝ) * Real.Gamma (m + ν + 1)) *
      (Real.sqrt a * r / 2) ^ (2 * (m : ℝ) + ν)
  rw [← tsum_mul_left, ← tsum_mul_left]
  congr 1; funext m
  have hb : 0 < Real.sqrt a * r / 2 := by positivity
  rw [Real.rpow_add hb, show (2 * (m : ℝ)) = ((2 * m : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast, show Real.sqrt a * r / 2 = (Real.sqrt a / 2) * r by ring,
    Real.mul_rpow (by positivity) hr.le, mul_pow, pow_mul, pow_mul, div_pow (Real.sqrt a) 2 2,
    Real.sq_sqrt ha.le, show (2 : ℝ) ^ 2 = 4 by norm_num]
  have hrr : r ^ (-ν) * r ^ ν = 1 := by
    rw [Real.rpow_neg hr.le, inv_mul_cancel₀ (Real.rpow_pos_of_pos hr ν).ne']
  unfold besselCoef
  calc (Real.sqrt a / 2) ^ ν * ((-1) ^ m * (a / 4) ^ m / (↑m ! * Real.Gamma (↑m + ν + 1)) *
        (r ^ 2) ^ m)
      = (r ^ (-ν) * r ^ ν) * ((Real.sqrt a / 2) ^ ν * ((-1) ^ m * (a / 4) ^ m /
          (↑m ! * Real.Gamma (↑m + ν + 1)) * (r ^ 2) ^ m)) := by rw [hrr, one_mul]
    _ = _ := by ring

/-! ### Sign of `Φ` -/

lemma besselSeries_zero (ν a : ℝ) : besselSeries ν a 0 = (Real.Gamma (ν + 1))⁻¹ := by
  unfold besselSeries
  rw [tsum_eq_single 0 (fun m hm => by simp [zero_pow hm])]
  simp [besselCoef]

lemma besselEntire_zero_pos {N : ℕ} (hN : 2 ≤ N) {a : ℝ} (ha : 0 < a) :
    0 < besselEntire N a 0 := by
  have hν : 0 ≤ (N : ℝ) / 2 - 1 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  unfold besselEntire
  rw [norm_zero, zero_pow two_ne_zero, besselSeries_zero]
  have : 0 < Real.sqrt a / 2 := by positivity
  have hg : 0 < Real.Gamma ((N : ℝ) / 2 - 1 + 1) := Real.Gamma_pos_of_pos (by linarith)
  positivity

lemma besselJ_ne_zero_of_lt_besselZero {ν s : ℝ} (hs : 0 < s) (hs1 : s < besselZero ν 1) :
    besselJ ν s ≠ 0 := by
  intro h0
  have : besselZero ν 1 ≤ s := by
    change sInf {x : ℝ | besselZero ν 0 < x ∧ besselJ ν x = 0} ≤ s
    exact csInf_le ⟨0, fun y hy => by simpa [besselZero] using hy.1.le⟩ ⟨by simpa [besselZero], h0⟩
  linarith

/-- `Φ > 0` on the ball `|x| < j_{ν,1}/√a` (from the definition of `j_{ν,1}` as the first positive
zero of `J_ν`, `Φ(0) > 0` and connectedness of the ball). -/
theorem besselEntire_pos {N : ℕ} (hN : 2 ≤ N) {a : ℝ} (ha : 0 < a) {x : RN N}
    (hx : ‖x‖ < besselZero ((N : ℝ) / 2 - 1) 1 / Real.sqrt a) : 0 < besselEntire N a x := by
  set R := besselZero ((N : ℝ) / 2 - 1) 1 / Real.sqrt a
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hR : 0 < R := lt_of_le_of_lt (norm_nonneg _) hx
  by_contra hneg
  push_neg at hneg
  have hcont : ContinuousOn (besselEntire N a) (ball (0 : RN N) R) :=
    ((besselEntire_analytic hN ha.le).continuousOn).mono (Set.subset_univ _)
  have hmem : (0 : ℝ) ∈ Set.Icc (besselEntire N a x) (besselEntire N a 0) :=
    ⟨hneg, (besselEntire_zero_pos hN ha).le⟩
  obtain ⟨z, hz, hz0⟩ := (convex_ball (0 : RN N) R).isPreconnected.intermediate_value
    (by simpa using hx) (mem_ball_self hR) hcont hmem
  have hzne : z ≠ 0 := by
    rintro rfl; exact (besselEntire_zero_pos hN ha).ne' hz0
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hzne
  rw [besselEntire_eq_profile ha hzne] at hz0
  unfold besselProfile at hz0
  have hJ : besselJ ((N : ℝ) / 2 - 1) (Real.sqrt a * ‖z‖) = 0 := by
    rcases mul_eq_zero.mp hz0 with h | h
    · exact absurd h (Real.rpow_pos_of_pos hzpos _).ne'
    · exact h
  refine besselJ_ne_zero_of_lt_besselZero (by positivity) ?_ hJ
  have hz' : ‖z‖ < R := by simpa using hz
  calc Real.sqrt a * ‖z‖ < Real.sqrt a * R := by gcongr
    _ = besselZero ((N : ℝ) / 2 - 1) 1 := by simp only [R]; field_simp

/-- `Φ < 0` where `J_ν(√a|x|) < 0`. -/
theorem besselEntire_neg_of_besselJ_neg {N : ℕ} {a : ℝ} (ha : 0 < a) {x : RN N} (hx : x ≠ 0)
    (hJ : besselJ ((N : ℝ) / 2 - 1) (Real.sqrt a * ‖x‖) < 0) : besselEntire N a x < 0 := by
  rw [besselEntire_eq_profile ha hx]
  unfold besselProfile
  exact mul_neg_of_pos_of_neg (Real.rpow_pos_of_pos (norm_pos_iff.mpr hx) _) hJ

end FourthRatio

end
