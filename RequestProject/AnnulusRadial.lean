module

public import RequestProject.BesselZeros
public import RequestProject.AnnulusSym

/-!
# Radial calculus for the Bessel profile on the annulus

With `ν = N/2 - 1`, `c = (√a/2)^ν` and `g = besselSeries ν a`, the entire Bessel profile is
`Φ(z) = c g(|z|²) = φ(|z|)` where `φ(r) = c g(r²)`.  We record
* the gradient `∇Φ(z) = 2c g'(|z|²) z`, whose norm is `|φ'(|z|)|`;
* the radial equation `(r^{N-1} φ')' = -a r^{N-1} φ`;
* the energy identity `∫_R^{R'} r^{N-1} φ'² = a ∫_R^{R'} r^{N-1} φ²` between consecutive zeros;
* polar coordinates for functions of `|z|` supported in an annulus.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Function Set
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

variable {N : ℕ}

/-- The first derivative series `g'` of `g = besselSeries ν a`. -/
def besselSeriesD (ν a s : ℝ) : ℝ := ∑' m : ℕ, ((m : ℝ) + 1) * besselCoef ν a (m + 1) * s ^ m

/-- The second derivative series `g''` of `g = besselSeries ν a`. -/
def besselSeriesDD (ν a s : ℝ) : ℝ :=
  ∑' m : ℕ, ((m : ℝ) + 1) * (((m + 1 : ℕ) : ℝ) + 1) * besselCoef ν a (m + 1 + 1) * s ^ m

/-- The radial profile `φ(r) = (√a/2)^ν g(r²)` of `Φ = besselEntire N a`. -/
def radPhi (N : ℕ) (a r : ℝ) : ℝ :=
  (Real.sqrt a / 2) ^ ((N : ℝ) / 2 - 1) * besselSeries ((N : ℝ) / 2 - 1) a (r ^ 2)

/-- Its derivative `φ'(r) = 2 (√a/2)^ν r g'(r²)`. -/
def radPhi1 (N : ℕ) (a r : ℝ) : ℝ :=
  (Real.sqrt a / 2) ^ ((N : ℝ) / 2 - 1) * (2 * r * besselSeriesD ((N : ℝ) / 2 - 1) a (r ^ 2))

/-- The gradient of `Φ`, `∇Φ(z) = 2 (√a/2)^ν g'(|z|²) z`. -/
def gradPhi (N : ℕ) (a : ℝ) (z : RN N) : RN N :=
  ((Real.sqrt a / 2) ^ ((N : ℝ) / 2 - 1) * (2 * besselSeriesD ((N : ℝ) / 2 - 1) a (‖z‖ ^ 2))) • z

lemma besselEntire_eq_radPhi (a : ℝ) (z : RN N) : besselEntire N a z = radPhi N a ‖z‖ := rfl

lemma hN_nu (hN : 2 ≤ N) : 0 ≤ (N : ℝ) / 2 - 1 := by
  have : (2 : ℝ) ≤ N := by exact_mod_cast hN
  linarith

lemma hasDerivAt_radPhi (hN : 2 ≤ N) {a : ℝ} (ha : 0 ≤ a) (r : ℝ) :
    HasDerivAt (radPhi N a) (radPhi1 N a r) r := by
  have h := ((hasDerivAt_besselSeries (hN_nu hN) ha (r ^ 2)).comp r (hasDerivAt_pow 2 r)).const_mul
    ((Real.sqrt a / 2) ^ ((N : ℝ) / 2 - 1))
  convert h using 1
  · rfl
  · simp only [radPhi1, besselSeriesD]
    push_cast
    ring

lemma continuous_radPhi (hN : 2 ≤ N) {a : ℝ} (ha : 0 ≤ a) : Continuous (radPhi N a) :=
  continuous_iff_continuousAt.mpr fun r => (hasDerivAt_radPhi hN ha r).continuousAt

lemma radial_ode_aux {ν a : ℝ} (hν : 0 ≤ ν) (ha : 0 ≤ a) (cst : ℝ) (n : ℕ)
    (hνn : 2 * ν + 2 = (n : ℝ) + 2) (r : ℝ) :
    HasDerivAt (fun x => x ^ (n + 1) * (cst * (2 * x * besselSeriesD ν a (x ^ 2))))
      (-a * (r ^ (n + 1) * (cst * besselSeries ν a (r ^ 2)))) r := by
  have h1 : HasDerivAt (fun x => besselSeriesD ν a (x ^ 2))
      (besselSeriesDD ν a (r ^ 2) * (2 * r)) r := by
    have := (hasDerivAt_besselSeries_deriv hν ha (r ^ 2)).comp r (hasDerivAt_pow 2 r)
    convert this using 1
    · rfl
    · simp [besselSeriesDD]
  have h2 := (hasDerivAt_pow (n + 1) r).mul ((((hasDerivAt_id r).const_mul 2).mul h1).const_mul cst)
  have hode := besselSeries_ode hν ha (r ^ 2)
  rw [hνn] at hode
  change 2 * ((n : ℝ) + 2) * besselSeriesD ν a (r ^ 2) + 4 * r ^ 2 * besselSeriesDD ν a (r ^ 2) =
    -a * besselSeries ν a (r ^ 2) at hode
  convert h2 using 1
  · rfl
  · simp only [id, Nat.add_sub_cancel, Pi.mul_apply]
    push_cast
    linear_combination (-(cst * r ^ (n + 1))) * hode

lemma radial_ode (hN : 2 ≤ N) {a : ℝ} (ha : 0 ≤ a) (r : ℝ) :
    HasDerivAt (fun r => r ^ (N - 1) * radPhi1 N a r) (-a * (r ^ (N - 1) * radPhi N a r)) r := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
  have e : n + 2 - 1 = n + 1 := by omega
  simp only [e, radPhi1, radPhi]
  exact radial_ode_aux (hN_nu hN) ha _ n (by push_cast; ring) r

lemma continuous_besselSeriesD {ν a : ℝ} (hν : 0 ≤ ν) (ha : 0 ≤ a) :
    Continuous (besselSeriesD ν a) :=
  continuous_iff_continuousAt.mpr fun s => (hasDerivAt_besselSeries_deriv hν ha s).continuousAt

lemma continuous_radPhi1 (hN : 2 ≤ N) {a : ℝ} (ha : 0 ≤ a) : Continuous (radPhi1 N a) := by
  have := continuous_besselSeriesD (hN_nu hN) ha
  unfold radPhi1
  fun_prop

lemma hasGradientAt_besselEntire (hN : 2 ≤ N) {a : ℝ} (ha : 0 ≤ a) (z : RN N) :
    HasGradientAt (besselEntire N a) (gradPhi N a z) z := by
  have h1 := (hasFDerivAt_id (𝕜 := ℝ) z).norm_sq
  have h2 := ((hasDerivAt_besselSeries (hN_nu hN) ha (‖z‖ ^ 2)).comp_hasFDerivAt z h1).const_mul
    ((Real.sqrt a / 2) ^ ((N : ℝ) / 2 - 1))
  rw [hasGradientAt_iff_hasFDerivAt]
  convert h2 using 1
  · rfl
  · ext w
    simp [gradPhi, besselSeriesD]
    ring

lemma continuous_gradPhi (hN : 2 ≤ N) {a : ℝ} (ha : 0 ≤ a) : Continuous (gradPhi N a) := by
  have := continuous_besselSeriesD (hN_nu hN) ha
  unfold gradPhi
  fun_prop

lemma norm_gradPhi_sq (a : ℝ) (z : RN N) : ‖gradPhi N a z‖ ^ 2 = radPhi1 N a ‖z‖ ^ 2 := by
  simp only [gradPhi, radPhi1, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-- **Energy identity** between two zeros of `φ`. -/
lemma radial_energy (hN : 2 ≤ N) {a : ℝ} (ha : 0 ≤ a) {R R' : ℝ}
    (h0 : radPhi N a R = 0) (h1 : radPhi N a R' = 0) :
    ∫ r in R..R', r ^ (N - 1) * radPhi1 N a r ^ 2 = a * ∫ r in R..R', r ^ (N - 1) * radPhi N a r ^ 2 := by
  have hc0 := continuous_radPhi hN ha
  have hc1 := continuous_radPhi1 hN ha
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := R) (b := R')
    (u := fun r => r ^ (N - 1) * radPhi1 N a r) (v := radPhi N a)
    (u' := fun r => -a * (r ^ (N - 1) * radPhi N a r)) (v' := radPhi1 N a)
    (fun r _ => radial_ode hN ha r) (fun r _ => hasDerivAt_radPhi hN ha r)
    ((by fun_prop : Continuous fun r => -a * (r ^ (N - 1) * radPhi N a r)).intervalIntegrable _ _)
    (hc1.intervalIntegrable _ _)
  simp only [h0, h1, mul_zero, sub_zero] at h
  have e1 : ∫ r in R..R', r ^ (N - 1) * radPhi1 N a r ^ 2 =
      ∫ r in R..R', r ^ (N - 1) * radPhi1 N a r * radPhi1 N a r := by
    congr 1; funext r; ring
  have e2 : ∫ r in R..R', -a * (r ^ (N - 1) * radPhi N a r) * radPhi N a r =
      -a * ∫ r in R..R', r ^ (N - 1) * radPhi N a r ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext r; ring
  rw [e1, h, e2]
  ring

lemma besselSeries_scale (ν a s : ℝ) : besselSeries ν a s = besselSeries ν 1 (a * s) := by
  unfold besselSeries besselCoef
  congr 1; funext m
  rw [div_pow, div_pow, mul_pow, one_pow]
  ring

/-- `φ` vanishes at `j_{ν,k}/√a`. -/
lemma radPhi_zero {a : ℝ} (ha : 0 < a) {k : ℕ}
    (hk : besselF ((N : ℝ) / 2 - 1) (besselZero ((N : ℝ) / 2 - 1) k) = 0) :
    radPhi N a (besselZero ((N : ℝ) / 2 - 1) k / Real.sqrt a) = 0 := by
  unfold radPhi
  rw [besselSeries_scale, div_pow, Real.sq_sqrt ha.le, mul_div_cancel₀ _ ha.ne']
  unfold besselF at hk
  rw [hk, mul_zero]

/-- For `r > 0`, `φ(r) = r^{-ν} J_ν(√a r)`. -/
lemma radPhi_eq_bessel (hN : 2 ≤ N) {a : ℝ} (ha : 0 < a) {r : ℝ} (hr : 0 < r) :
    radPhi N a r = r ^ (-((N : ℝ) / 2 - 1)) * besselJ ((N : ℝ) / 2 - 1) (Real.sqrt a * r) := by
  set z : RN N := EuclideanSpace.single (⟨0, by omega⟩ : Fin N) r
  have hz : ‖z‖ = r := by simp [z, abs_of_pos hr]
  have hz0 : z ≠ 0 := by rw [← norm_pos_iff, hz]; exact hr
  have := besselEntire_eq_profile ha hz0
  rw [besselEntire_eq_radPhi, hz] at this
  rw [this]
  unfold besselProfile
  rw [hz]

/-- **Polar coordinates** for a function of `|z|` supported in the annulus `R < |z| < R'`. -/
lemma integral_annulus_radial (hN : 2 ≤ N) {R R' : ℝ} (hR : 0 ≤ R) (hRR : R ≤ R') (G : ℝ → ℝ) :
    ∫ z : RN N, (Ioo R R').indicator G ‖z‖ =
      (N * volume.real (ball (0 : RN N) 1)) * ∫ r in R..R', r ^ (N - 1) * G r := by
  haveI : Nontrivial (RN N) := by
    have : Nontrivial (Fin N) := Fin.nontrivial_iff_two_le.mpr hN
    infer_instance
  rw [integral_fun_norm_addHaar volume ((Ioo R R').indicator G), finrank_euclideanSpace_fin]
  simp only [smul_eq_mul, nsmul_eq_mul]
  rw [mul_assoc]
  congr 2
  have e : (fun y : ℝ => y ^ (N - 1) * (Ioo R R').indicator G y) =
      (Ioo R R').indicator (fun y => y ^ (N - 1) * G y) := by
    funext y; by_cases hy : y ∈ Ioo R R' <;> simp [hy]
  rw [e, setIntegral_indicator measurableSet_Ioo, intervalIntegral.integral_of_le hRR,
    integral_Ioc_eq_integral_Ioo,
    inter_eq_right.mpr (Ioo_subset_Ioi_self.trans (Ioi_subset_Ioi hR))]

end FourthRatio

end
