module

public import RequestProject.WeylRadial

/-!
# Radial mollifiers and the mean value property of weakly harmonic functions

* `kern n t` — the radial mollifier `z ↦ β(|z|²/t²)/(t^n c_n)` of radius `t` and mass `1`;
* `meanK n t w = kern n t ⋆ w` — the corresponding weighted mean of `w`;
* `WeakHarmonic U w` — `w` is locally integrable on `U` and `∫ w Δφ = 0` for every test function
  `φ` supported in `U`;
* `meanK_const` — for a weakly harmonic `w` the weighted means `meanK n t w x` do not depend on
  `t` as long as `B̄(x, t) ⊆ U` (proved with the radial test functions of
  `RequestProject/WeylRadial.lean`);
* `ae_tendsto_meanK` — Lebesgue differentiation: `meanK n t w x → w x` for a.e. `x`.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Function Set
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

/-! ### The mollifier profile -/

/-- The smooth profile `β(u) = s(1 - u)`: equal to `1` for `u ≤ 0`, positive for `u < 1` and
`0` for `u ≥ 1`. -/
def molProf (u : ℝ) : ℝ := Real.smoothTransition (1 - u)

lemma contDiff_molProf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) molProf :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)

lemma molProf_nonneg (u : ℝ) : 0 ≤ molProf u := Real.smoothTransition.nonneg _

lemma molProf_le_one (u : ℝ) : molProf u ≤ 1 := Real.smoothTransition.le_one _

lemma molProf_eq_zero {u : ℝ} (hu : 1 ≤ u) : molProf u = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

lemma molProf_zero : molProf 0 = 1 := Real.smoothTransition.one_of_one_le (by norm_num)

variable {n : ℕ}

/-- The normalising constant `c_n = ∫ β(|z|²) dz`. -/
def kc (n : ℕ) : ℝ := ∫ z : RN n, molProf (‖z‖ ^ 2)

lemma molProf_norm_eq_zero {z : RN n} {t : ℝ} (ht : 0 < t) (hz : t ≤ ‖z‖) :
    molProf (‖z‖ ^ 2 / t ^ 2) = 0 := by
  refine molProf_eq_zero ?_
  rw [le_div_iff₀ (by positivity), one_mul]
  exact pow_le_pow_left₀ ht.le hz 2

lemma kc_pos : 0 < kc n := by
  have hc : Continuous fun z : RN n => molProf (‖z‖ ^ 2) :=
    contDiff_molProf.continuous.comp (continuous_norm.pow 2)
  refine hc.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0) ?_
    (fun z => molProf_nonneg _) (by simp [molProf_zero])
  refine HasCompactSupport.intro (isCompact_closedBall 0 1) fun z hz => ?_
  rw [mem_closedBall, dist_zero_right, not_le] at hz
  have := molProf_norm_eq_zero (z := z) one_pos hz.le
  simpa using this

/-! ### The mollifiers -/

/-- The radial mollifier of radius `t`: `kern n t z = β(|z|²/t²)/(t^n c_n)`. -/
def kern (n : ℕ) (t : ℝ) (z : RN n) : ℝ := molProf (‖z‖ ^ 2 / t ^ 2) / (t ^ n * kc n)

lemma contDiff_kern (t : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (kern n t) :=
  (contDiff_molProf.comp ((contDiff_norm_sq ℝ).div_const _)).div_const _

lemma kern_nonneg {t : ℝ} (ht : 0 < t) (z : RN n) : 0 ≤ kern n t z :=
  div_nonneg (molProf_nonneg _) (mul_nonneg (pow_nonneg ht.le _) kc_pos.le)

lemma kern_le {t : ℝ} (ht : 0 < t) (z : RN n) : kern n t z ≤ 1 / (t ^ n * kc n) :=
  div_le_div_of_nonneg_right (molProf_le_one _) (mul_nonneg (pow_nonneg ht.le _) kc_pos.le)

lemma kern_eq_zero {t : ℝ} (ht : 0 < t) {z : RN n} (hz : t ≤ ‖z‖) : kern n t z = 0 := by
  rw [kern, molProf_norm_eq_zero ht hz, zero_div]

lemma support_kern {t : ℝ} (ht : 0 < t) : support (kern n t) ⊆ ball 0 t := by
  intro z hz
  rw [mem_ball, dist_zero_right]
  by_contra h
  exact hz (kern_eq_zero ht (not_lt.mp h))

lemma tsupport_kern {t : ℝ} (ht : 0 < t) : tsupport (kern n t) ⊆ closedBall 0 t :=
  closure_minimal ((support_kern ht).trans ball_subset_closedBall) isClosed_closedBall

lemma hasCompactSupport_kern {t : ℝ} (ht : 0 < t) : HasCompactSupport (kern n t) :=
  (isCompact_closedBall 0 t).of_isClosed_subset (isClosed_tsupport _) (tsupport_kern ht)

lemma kern_neg (t : ℝ) (z : RN n) : kern n t (-z) = kern n t z := by
  simp [kern]

lemma kern_scale {t : ℝ} (ht : 0 < t) (z : RN n) : kern n t z = (t ^ n)⁻¹ * kern n 1 (t⁻¹ • z) := by
  simp only [kern, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht, one_pow, div_one, one_mul,
    mul_pow, inv_pow]
  have : (t ^ 2)⁻¹ * ‖z‖ ^ 2 = ‖z‖ ^ 2 / t ^ 2 := by rw [div_eq_inv_mul]
  rw [this]
  field_simp

lemma integral_kern {t : ℝ} (ht : 0 < t) : ∫ z, kern n t z = 1 := by
  have h1 : ∫ z, kern n 1 z = 1 := by
    simp only [kern, one_pow, div_one, one_mul]
    rw [integral_div]
    exact div_self kc_pos.ne'
  have h2 := Measure.integral_comp_inv_smul_of_nonneg (volume : Measure (RN n)) (kern n 1) ht.le
  rw [finrank_euclideanSpace_fin, h1, smul_eq_mul, mul_one] at h2
  simp_rw [kern_scale ht]
  rw [integral_const_mul, h2]
  exact inv_mul_cancel₀ (pow_ne_zero _ ht.ne')

/-! ### Weighted means -/

/-- The weighted mean `meanK n t w = kern n t ⋆ w`. -/
def meanK (n : ℕ) (t : ℝ) (w : RN n → ℝ) : RN n → ℝ :=
  convolution (kern n t) w (ContinuousLinearMap.lsmul ℝ ℝ) volume

lemma meanK_eq (t : ℝ) (w : RN n → ℝ) (x : RN n) :
    meanK n t w x = ∫ y, kern n t (x - y) * w y := by
  rw [meanK, convolution_eq_swap]
  rfl

/-- `w` is *weakly harmonic* on `U`: locally integrable on `U` with `∫ w Δφ = 0` for every test
function `φ` supported in `U`. -/
def WeakHarmonic (U : Set (RN n)) (w : RN n → ℝ) : Prop :=
  LocallyIntegrableOn w U ∧ ∀ φ : RN n → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ →
    HasCompactSupport φ → tsupport φ ⊆ U → ∫ x, w x * Laplacian.laplacian φ x = 0

lemma integrable_kern_mul {U : Set (RN n)} {w : RN n → ℝ} (hw : LocallyIntegrableOn w U)
    {x : RN n} {t : ℝ} (ht : 0 < t) (hxU : closedBall x t ⊆ U) :
    Integrable (fun y => kern n t (x - y) * w y) := by
  have hK : IsCompact (closedBall x t) := isCompact_closedBall x t
  have h1 : IntegrableOn (fun y => kern n t (x - y) * w y) (closedBall x t) :=
    IntegrableOn.continuousOn_mul ((contDiff_kern t).continuous.comp
      (continuous_const.sub continuous_id)).continuousOn
      (hw.integrableOn_compact_subset hxU hK) hK
  refine (integrableOn_iff_integrable_of_support_subset ?_).mp h1
  intro y hy
  have : kern n t (x - y) ≠ 0 := left_ne_zero_of_mul hy
  have h := support_kern ht this
  rw [mem_ball, dist_zero_right] at h
  rw [mem_closedBall, dist_eq_norm, ← norm_neg, neg_sub]
  exact h.le

/-- `∫₀^R ρ^{n-1} β(ρ²/t²) dρ = t^n ∫₀¹ σ^{n-1} β(σ²) dσ` for `0 < t ≤ R`. -/
lemma prof_int (hn : 1 ≤ n) {t R : ℝ} (ht : 0 < t) (htR : t ≤ R) :
    ∫ ρ in (0 : ℝ)..R, ρ ^ (n - 1) * molProf (ρ ^ 2 / t ^ 2) =
      t ^ n * ∫ σ in (0 : ℝ)..1, σ ^ (n - 1) * molProf (σ ^ 2) := by
  have hc : Continuous fun σ : ℝ => σ ^ (n - 1) * molProf (σ ^ 2) :=
    (continuous_pow _).mul (contDiff_molProf.continuous.comp (continuous_pow 2))
  have h := intervalIntegral.integral_comp_mul_left (a := (0 : ℝ)) (b := R / t)
    (fun ρ => ρ ^ (n - 1) * molProf (ρ ^ 2 / t ^ 2)) (ne_of_gt ht)
  simp only [mul_zero, mul_div_cancel₀ _ ht.ne'] at h
  have e : ∀ σ : ℝ, (t * σ) ^ (n - 1) * molProf ((t * σ) ^ 2 / t ^ 2) =
      t ^ (n - 1) * (σ ^ (n - 1) * molProf (σ ^ 2)) := by
    intro σ
    rw [mul_pow, mul_pow, mul_div_cancel_left₀ _ (pow_ne_zero 2 ht.ne')]
    ring
  simp_rw [e] at h
  rw [intervalIntegral.integral_const_mul, smul_eq_mul] at h
  have h1t : 1 ≤ R / t := by rw [le_div_iff₀ ht, one_mul]; exact htR
  have hsplit : ∫ σ in (0 : ℝ)..R / t, σ ^ (n - 1) * molProf (σ ^ 2) =
      ∫ σ in (0 : ℝ)..1, σ ^ (n - 1) * molProf (σ ^ 2) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1)
      (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
    have : ∫ σ in (1 : ℝ)..R / t, σ ^ (n - 1) * molProf (σ ^ 2) = 0 := by
      rw [intervalIntegral.integral_of_le h1t]
      refine setIntegral_eq_zero_of_forall_eq_zero fun σ hσ => ?_
      rw [molProf_eq_zero (one_le_pow₀ hσ.1.le), mul_zero]
    rw [this, add_zero]
  rw [hsplit] at h
  have hpow : t ^ n = t * t ^ (n - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [hpow, mul_assoc, h, ← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul]

/-- **Mean value property of weakly harmonic functions.** If `w` is weakly harmonic on `U` and
`B̄(x, R) ⊆ U`, then `meanK n t w x = meanK n R w x` for `0 < t ≤ R`. -/
theorem meanK_const (hn : 1 ≤ n) {U : Set (RN n)} {w : RN n → ℝ} (hw : WeakHarmonic U w)
    {x : RN n} {t R : ℝ} (ht : 0 < t) (htR : t ≤ R) (hxU : closedBall x R ⊆ U) :
    meanK n t w x = meanK n R w x := by
  have hR : 0 < R := lt_of_lt_of_le ht htR
  set g : ℝ → ℝ := fun u => molProf (u / t ^ 2) / (t ^ n * kc n) -
    molProf (u / R ^ 2) / (R ^ n * kc n) with hgdef
  have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g :=
    ((contDiff_molProf.comp (contDiff_id.div_const _)).div_const _).sub
      ((contDiff_molProf.comp (contDiff_id.div_const _)).div_const _)
  have hsupp : ∀ u, R ^ 2 ≤ u → g u = 0 := by
    intro u hu
    have h1 : 1 ≤ u / t ^ 2 := by
      rw [le_div_iff₀ (by positivity), one_mul]
      exact le_trans (pow_le_pow_left₀ ht.le htR 2) hu
    have h2 : 1 ≤ u / R ^ 2 := by
      rw [le_div_iff₀ (by positivity), one_mul]; exact hu
    simp [hgdef, molProf_eq_zero h1, molProf_eq_zero h2]
  have hint : ∫ ρ in (0 : ℝ)..R, ρ ^ (n - 1) * g (ρ ^ 2) = 0 := by
    have hc1 : Continuous fun ρ : ℝ => ρ ^ (n - 1) * molProf (ρ ^ 2 / t ^ 2) :=
      (continuous_pow _).mul (contDiff_molProf.continuous.comp ((continuous_pow 2).div_const _))
    have hc2 : Continuous fun ρ : ℝ => ρ ^ (n - 1) * molProf (ρ ^ 2 / R ^ 2) :=
      (continuous_pow _).mul (contDiff_molProf.continuous.comp ((continuous_pow 2).div_const _))
    have e : ∀ ρ : ℝ, ρ ^ (n - 1) * g (ρ ^ 2) =
        (t ^ n * kc n)⁻¹ * (ρ ^ (n - 1) * molProf (ρ ^ 2 / t ^ 2)) -
          (R ^ n * kc n)⁻¹ * (ρ ^ (n - 1) * molProf (ρ ^ 2 / R ^ 2)) := by
      intro ρ; simp only [hgdef]; ring
    simp_rw [e]
    rw [intervalIntegral.integral_sub ((hc1.intervalIntegrable _ _).const_mul _)
        ((hc2.intervalIntegrable _ _).const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      prof_int hn ht htR, prof_int hn hR le_rfl]
    have := kc_pos (n := n)
    field_simp
    ring
  obtain ⟨ψ, hψ, hψc, hψs, hΔ⟩ := exists_radial_test hn hg hR hsupp hint x
  have h0 := hw.2 ψ hψ hψc (hψs.trans hxU)
  have e : ∀ y, w y * Laplacian.laplacian ψ y =
      kern n t (x - y) * w y - kern n R (x - y) * w y := by
    intro y
    rw [hΔ y, ← norm_neg (y - x), neg_sub]
    simp only [hgdef, kern]
    ring
  simp_rw [e] at h0
  rw [integral_sub (integrable_kern_mul hw.1 ht ((closedBall_subset_closedBall htR).trans hxU))
    (integrable_kern_mul hw.1 hR hxU)] at h0
  rw [meanK_eq, meanK_eq]
  linarith

/-! ### Lebesgue differentiation for the weighted means -/

/-- For a locally integrable `w`, `meanK n t w x → w x` as `t → 0⁺` for almost every `x`. -/
theorem ae_tendsto_meanK {w : RN n → ℝ} (hw : LocallyIntegrable w) :
    ∀ᵐ x, Tendsto (fun t => meanK n t w x) (𝓝[>] 0) (𝓝 (w x)) := by
  filter_upwards [(Besicovitch.vitaliFamily (volume : Measure (RN n))).ae_tendsto_average_norm_sub
    hw] with x₀ h₀
  have := h₀.comp (Besicovitch.tendsto_filterAt volume x₀)
  simp_rw [meanK_eq]
  set V : ℝ := volume.real (ball (0 : RN n) 1)
  have hV : 0 < V := by
    simp only [V, measureReal_def]
    exact ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne
  refine tendsto_integral_smul_of_tendsto_average_norm_sub (V / kc n) this ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun t => hw.integrableOn_isCompact (isCompact_closedBall _ _)
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    rw [← integral_kern (n := n) ht]
    have := integral_sub_left_eq_self (fun z => kern n t z) (volume : Measure (RN n)) x₀
    exact this.symm
  · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    intro y hy
    have h := support_kern ht hy
    rw [mem_ball, dist_zero_right] at h
    rw [mem_closedBall, dist_eq_norm, ← norm_neg, neg_sub]
    exact h.le
  · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    intro y
    rw [abs_of_nonneg (kern_nonneg ht _), Measure.addHaar_real_closedBall _ _ ht.le,
      finrank_euclideanSpace_fin]
    refine (kern_le ht _).trans (le_of_eq ?_)
    have := kc_pos (n := n)
    field_simp
    exact (div_self hV.ne').symm

end FourthRatio

end
