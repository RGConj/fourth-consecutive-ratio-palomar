module

public import RequestProject.BesselEntire

/-!
# Radial solutions of the Poisson equation

Auxiliary one-dimensional analysis for Weyl's lemma:

* `contDiff_param_integral` — smoothness of `u ↦ ∫₀¹ F(u, τ) dτ` for smooth `F`;
* `molProf` — the smooth profile used for radial mollifiers;
* `radial_solve` — for a smooth `g` vanishing on `[R², ∞)` with `∫₀^R ρ^{n-1} g(ρ²) dρ = 0`
  there is a smooth `Φ` vanishing on `[R², ∞)` with `4uΦ''(u) + 2nΦ'(u) = g(u)` for `u ≥ 0`;
  consequently `ψ(z) = Φ(|z - c|²)` is a test function supported in `B̄(c, R)` with
  `Δψ(z) = g(|z - c|²)`.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Function Set intervalIntegral
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

/-! ### Smoothness of parametric integrals over `[0, 1]` -/

/-- The partial derivative in the first variable of a function of two real variables. -/
def pd1 (F : ℝ → ℝ → ℝ) (u τ : ℝ) : ℝ := fderiv ℝ (Function.uncurry F) (u, τ) (1, 0)

lemma contDiff_pd1 {F : ℝ → ℝ → ℝ}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry F)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry (pd1 F)) := by
  have : Function.uncurry (pd1 F) = fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry F) p (1, 0) := by
    funext p; rfl
  rw [this]
  exact (hF.fderiv_right (m := (⊤ : ℕ∞)) (WithTop.coe_le_coe.mpr le_top)).clm_apply
    contDiff_const

lemma hasDerivAt_pd1 {F : ℝ → ℝ → ℝ}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry F)) (u τ : ℝ) :
    HasDerivAt (fun v => F v τ) (pd1 F u τ) u := by
  have h1 : HasFDerivAt (Function.uncurry F) (fderiv ℝ (Function.uncurry F) (u, τ)) (u, τ) :=
    (hF.differentiable (by simp) (u, τ)).hasFDerivAt
  have h2 : HasDerivAt (fun v : ℝ => (v, τ)) ((1 : ℝ), (0 : ℝ)) u :=
    (hasDerivAt_id u).prodMk (hasDerivAt_const u τ)
  exact h1.comp_hasDerivAt u h2

lemma hasDerivAt_param_integral {F : ℝ → ℝ → ℝ}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry F)) (u : ℝ) :
    HasDerivAt (fun v => ∫ τ in (0 : ℝ)..1, F v τ) (∫ τ in (0 : ℝ)..1, pd1 F u τ) u := by
  have hc : Continuous (Function.uncurry (pd1 F)) := (contDiff_pd1 hF).continuous
  obtain ⟨C, hC⟩ := (isCompact_closedBall u 1 |>.prod (isCompact_Icc (a := (0 : ℝ)) (b := 1)))
    |>.exists_bound_of_continuousOn hc.continuousOn
  have hFc : Continuous (Function.uncurry F) := hF.continuous
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (bound := fun _ => C) (ball_mem_nhds u one_pos) ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Eventually.of_forall fun v =>
      (hFc.comp (Continuous.prodMk_right v)).aestronglyMeasurable
  · exact (hFc.comp (Continuous.prodMk_right u)).intervalIntegrable 0 1
  · exact (hc.comp (Continuous.prodMk_right u)).aestronglyMeasurable
  · refine Eventually.of_forall fun τ hτ v hv => ?_
    have hτ' : τ ∈ Icc (0 : ℝ) 1 := by
      rw [uIoc_of_le zero_le_one] at hτ; exact ⟨hτ.1.le, hτ.2⟩
    exact hC (v, τ) ⟨ball_subset_closedBall hv, hτ'⟩
  · exact _root_.intervalIntegrable_const
  · exact Eventually.of_forall fun τ _ v _ => hasDerivAt_pd1 hF v τ

/-- Smoothness of `u ↦ ∫₀¹ F(u, τ) dτ` for a smooth function `F` of two variables. -/
lemma contDiff_param_integral {F : ℝ → ℝ → ℝ}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry F)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u => ∫ τ in (0 : ℝ)..1, F u τ) := by
  rw [contDiff_infty]
  intro k
  induction k generalizing F with
  | zero =>
    refine contDiff_zero.mpr ?_
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      hF.continuous 0 1
  | succ k ih =>
    have hd := hasDerivAt_param_integral hF
    rw [Nat.cast_succ, contDiff_succ_iff_deriv]
    refine ⟨fun u => (hd u).differentiableAt, by simp, ?_⟩
    rw [show deriv (fun v => ∫ τ in (0 : ℝ)..1, F v τ) =
        fun u => ∫ τ in (0 : ℝ)..1, pd1 F u τ from funext fun u => (hd u).deriv]
    exact ih (contDiff_pd1 hF)

/-! ### The radial ODE -/

/-- `G(u) = ½ ∫₀¹ τ^{n-1} g(uτ²) dτ`, the derivative of the radial solution. -/
def radG (n : ℕ) (g : ℝ → ℝ) (u : ℝ) : ℝ := (1 / 2) * ∫ τ in (0 : ℝ)..1, τ ^ (n - 1) * g (u * τ ^ 2)

/-- `G'(u) = ½ ∫₀¹ τ^{n+1} g'(uτ²) dτ`. -/
def radG' (n : ℕ) (g : ℝ → ℝ) (u : ℝ) : ℝ :=
  (1 / 2) * ∫ τ in (0 : ℝ)..1, τ ^ (n + 1) * deriv g (u * τ ^ 2)

variable {n : ℕ} {g : ℝ → ℝ}

lemma contDiff_radG (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (radG n g) := by
  unfold radG
  refine contDiff_const.mul (contDiff_param_integral (F := fun u τ => τ ^ (n - 1) * g (u * τ ^ 2)) ?_)
  change ContDiff ℝ _ (fun p : ℝ × ℝ => p.2 ^ (n - 1) * g (p.1 * p.2 ^ 2))
  exact (contDiff_snd.pow _).mul (hg.comp (contDiff_fst.mul (contDiff_snd.pow 2)))

lemma hasDerivAt_radG (hn : 1 ≤ n) (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (u : ℝ) :
    HasDerivAt (radG n g) (radG' n g u) u := by
  set F : ℝ → ℝ → ℝ := fun u τ => τ ^ (n - 1) * g (u * τ ^ 2) with hFdef
  have hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry F) := by
    change ContDiff ℝ _ (fun p : ℝ × ℝ => p.2 ^ (n - 1) * g (p.1 * p.2 ^ 2))
    exact (contDiff_snd.pow _).mul (hg.comp (contDiff_fst.mul (contDiff_snd.pow 2)))
  have h := (hasDerivAt_param_integral hF u).const_mul (1 / 2 : ℝ)
  have hgd : Differentiable ℝ g := hg.differentiable (by simp)
  have heq : ∀ τ, pd1 F u τ = τ ^ (n + 1) * deriv g (u * τ ^ 2) := by
    intro τ
    have h1 := hasDerivAt_pd1 hF u τ
    have h2 : HasDerivAt (fun v => F v τ) (τ ^ (n - 1) * (deriv g (u * τ ^ 2) * τ ^ 2)) u := by
      have := ((hgd (u * τ ^ 2)).hasDerivAt.comp u ((hasDerivAt_id u).mul_const (τ ^ 2)))
      simp only [id, one_mul] at this
      exact this.const_mul _
    rw [h1.unique h2]
    have : τ ^ (n + 1) = τ ^ (n - 1) * τ ^ 2 := by
      rw [← pow_add]; congr 1; omega
    rw [this]; ring
  simp only [heq] at h
  exact h

lemma radG_ode (hn : 1 ≤ n) (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (u : ℝ) :
    2 * n * radG n g u + 4 * u * radG' n g u = g u := by
  have hgd : Differentiable ℝ g := hg.differentiable (by simp)
  set h : ℝ → ℝ := fun τ => g (u * τ ^ 2) with hhdef
  have hh : ∀ τ, HasDerivAt h (deriv g (u * τ ^ 2) * (u * (2 * τ))) τ := by
    intro τ
    have := (hgd (u * τ ^ 2)).hasDerivAt.comp τ ((hasDerivAt_pow 2 τ).const_mul u)
    convert this using 1
    · rfl
    · norm_num
  have hp : ∀ τ, HasDerivAt (fun τ : ℝ => τ ^ n) (n * τ ^ (n - 1)) τ := fun τ => by
    simpa using hasDerivAt_pow n τ
  have hcont_h' : Continuous fun τ => deriv g (u * τ ^ 2) * (u * (2 * τ)) :=
    ((hg.continuous_deriv (by simp)).comp (continuous_const.mul (continuous_pow 2))).mul
      (continuous_const.mul (continuous_const.mul continuous_id))
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := (0 : ℝ)) (b := 1)
    (fun τ _ => hp τ) (fun τ _ => hh τ)
    ((continuous_const.mul (continuous_pow _)).intervalIntegrable _ _)
    (hcont_h'.intervalIntegrable _ _)
  have hn0 : (0 : ℝ) ^ n = 0 := zero_pow (by omega)
  simp only [one_pow, one_mul, hn0, zero_mul, sub_zero, hhdef, mul_one] at hibp
  unfold radG radG'
  have e1 : ∫ τ in (0 : ℝ)..1, τ ^ n * (deriv g (u * τ ^ 2) * (u * (2 * τ))) =
      2 * u * ∫ τ in (0 : ℝ)..1, τ ^ (n + 1) * deriv g (u * τ ^ 2) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun τ _ => ?_
    ring
  have e2 : ∫ τ in (0 : ℝ)..1, (n : ℝ) * τ ^ (n - 1) * g (u * τ ^ 2) =
      n * ∫ τ in (0 : ℝ)..1, τ ^ (n - 1) * g (u * τ ^ 2) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun τ _ => ?_
    ring
  rw [e1, e2] at hibp
  linarith

/-- Change of variables `ρ = rτ`. -/
lemma radG_eq_scaled (hn : 1 ≤ n) {r : ℝ} (hr : 0 < r) :
    radG n g (r ^ 2) = (1 / 2) * (r ^ n)⁻¹ * ∫ ρ in (0 : ℝ)..r, ρ ^ (n - 1) * g (ρ ^ 2) := by
  unfold radG
  have h := intervalIntegral.integral_comp_mul_left (a := (0 : ℝ)) (b := 1)
    (fun ρ => ρ ^ (n - 1) * g (ρ ^ 2)) (ne_of_gt hr)
  simp only [mul_zero, mul_one] at h
  have e : ∫ τ in (0 : ℝ)..1, τ ^ (n - 1) * g (r ^ 2 * τ ^ 2) =
      (r ^ (n - 1))⁻¹ * ∫ τ in (0 : ℝ)..1, (r * τ) ^ (n - 1) * g ((r * τ) ^ 2) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun τ _ => ?_
    simp only [mul_pow]
    field_simp
  rw [e, h, smul_eq_mul]
  have : r ^ n = r ^ (n - 1) * r := by
    rw [← pow_succ]; congr 1; omega
  rw [this]
  field_simp

lemma radG_eq_zero (hn : 1 ≤ n) (hgc : Continuous g) {R : ℝ} (hR : 0 < R)
    (hsupp : ∀ u, R ^ 2 ≤ u → g u = 0)
    (hint : ∫ ρ in (0 : ℝ)..R, ρ ^ (n - 1) * g (ρ ^ 2) = 0) {u : ℝ} (hu : R ^ 2 ≤ u) :
    radG n g u = 0 := by
  have hu0 : 0 ≤ u := le_trans (sq_nonneg R) hu
  set r := Real.sqrt u with hr
  have hrR : R ≤ r := Real.le_sqrt_of_sq_le hu
  have hr0 : 0 < r := lt_of_lt_of_le hR hrR
  have hur : u = r ^ 2 := (Real.sq_sqrt hu0).symm
  rw [hur, radG_eq_scaled hn hr0]
  have hcont : Continuous fun ρ : ℝ => ρ ^ (n - 1) * g (ρ ^ 2) :=
    (continuous_pow _).mul (hgc.comp (continuous_pow 2))
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := R)
    (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _), hint, zero_add]
  have : ∫ ρ in R..r, ρ ^ (n - 1) * g (ρ ^ 2) = 0 := by
    rw [intervalIntegral.integral_of_le hrR]
    refine setIntegral_eq_zero_of_forall_eq_zero fun ρ hρ => ?_
    rw [hsupp _ (pow_le_pow_left₀ hR.le hρ.1.le 2), mul_zero]
  rw [this, mul_zero]

/-- The radial primitive `Φ(u) = ∫_{R²}^u G`. -/
def weylPhi (n : ℕ) (g : ℝ → ℝ) (R : ℝ) (u : ℝ) : ℝ := ∫ v in R ^ 2..u, radG n g v

lemma hasDerivAt_weylPhi (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (R u : ℝ) :
    HasDerivAt (weylPhi n g R) (radG n g u) u :=
  intervalIntegral.integral_hasDerivAt_right ((contDiff_radG hg).continuous.intervalIntegrable _ _)
    ((contDiff_radG hg).continuous.stronglyMeasurableAtFilter _ _) (contDiff_radG hg).continuous.continuousAt

lemma contDiff_weylPhi (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (R : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (weylPhi n g R) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun u => (hasDerivAt_weylPhi hg R u).differentiableAt, ?_⟩
  rw [show deriv (weylPhi n g R) = radG n g from funext fun u => (hasDerivAt_weylPhi hg R u).deriv]
  exact contDiff_radG hg

lemma weylPhi_eq_zero (hn : 1 ≤ n) (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) {R : ℝ}
    (hR : 0 < R) (hsupp : ∀ u, R ^ 2 ≤ u → g u = 0)
    (hint : ∫ ρ in (0 : ℝ)..R, ρ ^ (n - 1) * g (ρ ^ 2) = 0) {u : ℝ} (hu : R ^ 2 ≤ u) :
    weylPhi n g R u = 0 := by
  unfold weylPhi
  rw [intervalIntegral.integral_of_le hu]
  exact setIntegral_eq_zero_of_forall_eq_zero fun v hv =>
    radG_eq_zero hn hg.continuous hR hsupp hint hv.1.le

/-- **Radial test functions with prescribed Laplacian.** If `g` is smooth, vanishes on `[R², ∞)`
and `∫₀^R ρ^{n-1} g(ρ²) dρ = 0`, there is a test function `ψ` supported in `B̄(c, R)` with
`Δψ(z) = g(|z - c|²)`. -/
theorem exists_radial_test (hn : 1 ≤ n) (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) {R : ℝ}
    (hR : 0 < R) (hsupp : ∀ u, R ^ 2 ≤ u → g u = 0)
    (hint : ∫ ρ in (0 : ℝ)..R, ρ ^ (n - 1) * g (ρ ^ 2) = 0) (c : RN n) :
    ∃ ψ : RN n → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ ∧ HasCompactSupport ψ ∧
      tsupport ψ ⊆ closedBall c R ∧ ∀ z, Laplacian.laplacian ψ z = g (‖z - c‖ ^ 2) := by
  set Φ := weylPhi n g R
  have hsub : tsupport (fun z : RN n => Φ (‖z - c‖ ^ 2)) ⊆ closedBall c R := by
    refine closure_minimal (fun z hz => ?_) isClosed_closedBall
    by_contra h
    apply hz
    rw [mem_closedBall, dist_eq_norm, not_le] at h
    exact weylPhi_eq_zero hn hg hR hsupp hint (pow_le_pow_left₀ hR.le h.le 2)
  refine ⟨fun z => Φ (‖z - c‖ ^ 2), ?_, ?_, hsub, fun z => ?_⟩
  · exact (contDiff_weylPhi hg R).comp ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const))
  · exact (isCompact_closedBall c R).of_isClosed_subset (isClosed_tsupport _) hsub
  · set b := EuclideanSpace.basisFun (Fin n) ℝ
    have h1 : Laplacian.laplacian (fun z : RN n => Φ (‖z - c‖ ^ 2)) z =
        Laplacian.laplacian (fun z : RN n => Φ (‖z‖ ^ 2)) (z - c) := by
      change Laplacian.laplacian (fun x => (fun z : RN n => Φ (‖z‖ ^ 2)) (x - c)) z = _
      rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ b,
        InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ b]
      exact Finset.sum_congr rfl fun i _ => by
        rw [iteratedFDeriv_comp_sub (f := fun z : RN n => Φ (‖z‖ ^ 2)) 2 c z]
    rw [h1, laplacian_radial_sq b Φ (radG n g) (radG' n g) (hasDerivAt_weylPhi hg R)
      (hasDerivAt_radG hn hg) (z - c)]
    simp only [Fintype.card_fin]
    exact radG_ode hn hg _

end FourthRatio

end
