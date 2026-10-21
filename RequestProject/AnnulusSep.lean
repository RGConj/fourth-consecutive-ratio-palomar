module

public import RequestProject.AnnulusMem
public import RequestProject.BallIntegrals

/-!
# Separation of variables on the annulus

The annulus part of the separation-of-variables clause of the ball/annulus lemma of the paper:
with `ν = N/2 - 1`, `d = N - 1`, `R = j_{ν,1}/√a`, `R' = j_{ν,2}/√a`, `A = {R < |x - y| < R'}` and
`ρ(r) = r^{-ν} J_ν(√a r)`, the functions `ψ, ψ x₁/|x|, …, ψ x_N/|x|` (`ψ = -Φ(· - y)|_A`) span an
`(N+1)`-dimensional subspace of `H₀¹(A)` on which
`q(v,v) ≤ (a + d ∫_R^{R'} ρ² r^{d-2} / ∫_R^{R'} ρ² rᵈ) ‖v‖²`.

For `v = c₀ψ + ψ⟨c, x - y⟩/|x - y|` the radial symmetry lemmas give
`‖v‖² = (c₀² + |c|²/N) J₀` and `q(v,v) = (c₀² + |c|²/N) J₁ + |c|² (1 - 1/N) J₂` with
`J₀ = ∫_A φ²`, `J₁ = ∫_A φ'² = a J₀` (energy identity) and `J₂ = ∫_A φ²/r²`; polar coordinates
turn `J₂/J₀` into the one-dimensional ratio.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Function Set
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

variable {N : ℕ}

/-- `J₀ = ∫_A φ(|z|)² dz`. -/
def annJ0 (N : ℕ) (a : ℝ) : ℝ :=
  ∫ z : RN N, (Ioo (annR N a) (annR' N a)).indicator (fun r => radPhi N a r ^ 2) ‖z‖

/-- `J₁ = ∫_A φ'(|z|)² dz`. -/
def annJ1 (N : ℕ) (a : ℝ) : ℝ :=
  ∫ z : RN N, (Ioo (annR N a) (annR' N a)).indicator (fun r => radPhi1 N a r ^ 2) ‖z‖

/-- `J₂ = ∫_A φ(|z|)²/|z|² dz`. -/
def annJ2 (N : ℕ) (a : ℝ) : ℝ :=
  ∫ z : RN N, (Ioo (annR N a) (annR' N a)).indicator (fun r => radPhi N a r ^ 2 / r ^ 2) ‖z‖

/-! ### Integrability and radial integration of quadratic expressions -/

lemma integrable_annulus_radial {R R' : ℝ} {g : ℝ → ℝ} (hg : ContinuousOn g (Icc R R'))
    {P : RN N → ℝ} (hP : Continuous P) :
    Integrable (fun z : RN N => (Ioo R R').indicator g ‖z‖ * P z) := by
  have hcn : Continuous fun z : RN N => ‖z‖ := continuous_norm
  set K : Set (RN N) := (fun z => ‖z‖) ⁻¹' Icc R R'
  have hK : IsCompact K := (isCompact_closedBall (0 : RN N) R').of_isClosed_subset
    (isClosed_Icc.preimage hcn) (fun z hz => by simpa using hz.2)
  have hKc : ContinuousOn (fun z : RN N => g ‖z‖ * P z) K :=
    (hg.comp hcn.continuousOn (fun z hz => hz)).mul hP.continuousOn
  have hI : IntegrableOn (fun z : RN N => g ‖z‖ * P z) ((fun z => ‖z‖) ⁻¹' Ioo R R') :=
    (hKc.integrableOn_compact hK).mono_set (preimage_mono Ioo_subset_Icc_self)
  have hm : MeasurableSet ((fun z : RN N => ‖z‖) ⁻¹' Ioo R R') :=
    measurableSet_Ioo.preimage hcn.measurable
  refine ((integrable_indicator_iff hm).mpr hI).congr (Eventually.of_forall fun z => ?_)
  by_cases hz : ‖z‖ ∈ Ioo R R'
  · simp [indicator_of_mem hz, indicator_of_mem (show z ∈ (fun z : RN N => ‖z‖) ⁻¹' Ioo R R' from hz)]
  · simp [indicator_of_notMem hz,
      indicator_of_notMem (show z ∉ (fun z : RN N => ‖z‖) ⁻¹' Ioo R R' from hz)]

lemma integral_radial_quad (hN : 2 ≤ N) {R R' : ℝ} {g0 g1 g2 : ℝ → ℝ}
    (h0 : ContinuousOn g0 (Icc R R')) (h1 : ContinuousOn g1 (Icc R R'))
    (h2 : ContinuousOn g2 (Icc R R')) (c : RN N) :
    ∫ z : RN N, ((Ioo R R').indicator g0 ‖z‖ + (Ioo R R').indicator g1 ‖z‖ * ⟪c, z⟫ +
        (Ioo R R').indicator g2 ‖z‖ * ⟪c, z⟫ ^ 2) =
      (∫ z : RN N, (Ioo R R').indicator g0 ‖z‖) +
        ‖c‖ ^ 2 / N * ∫ z : RN N, (Ioo R R').indicator (fun r => g2 r * r ^ 2) ‖z‖ := by
  have i0 : Integrable (fun z : RN N => (Ioo R R').indicator g0 ‖z‖) := by
    simpa using integrable_annulus_radial h0 (continuous_const (y := (1 : ℝ)))
  have i1 : Integrable (fun z : RN N => (Ioo R R').indicator g1 ‖z‖ * ⟪c, z⟫) :=
    integrable_annulus_radial h1 (by fun_prop)
  have i2 : Integrable (fun z : RN N => (Ioo R R').indicator g2 ‖z‖ * ⟪c, z⟫ ^ 2) :=
    integrable_annulus_radial h2 (by fun_prop)
  have i2' : Integrable (fun z : RN N => (Ioo R R').indicator g2 ‖z‖ * ‖z‖ ^ 2) :=
    integrable_annulus_radial h2 (by fun_prop)
  have m2 : AEStronglyMeasurable (fun z : RN N => (Ioo R R').indicator g2 ‖z‖) volume := by
    simpa using (integrable_annulus_radial h2 (continuous_const (y := (1 : ℝ)))).aestronglyMeasurable
  have e1 : ∫ z : RN N, ((Ioo R R').indicator g0 ‖z‖ + (Ioo R R').indicator g1 ‖z‖ * ⟪c, z⟫ +
        (Ioo R R').indicator g2 ‖z‖ * ⟪c, z⟫ ^ 2) =
      (∫ z : RN N, ((Ioo R R').indicator g0 ‖z‖ + (Ioo R R').indicator g1 ‖z‖ * ⟪c, z⟫)) +
        ∫ z : RN N, (Ioo R R').indicator g2 ‖z‖ * ⟪c, z⟫ ^ 2 := integral_add (i0.add i1) i2
  have e2 : ∫ z : RN N, ((Ioo R R').indicator g0 ‖z‖ + (Ioo R R').indicator g1 ‖z‖ * ⟪c, z⟫) =
      (∫ z : RN N, (Ioo R R').indicator g0 ‖z‖) +
        ∫ z : RN N, (Ioo R R').indicator g1 ‖z‖ * ⟪c, z⟫ := integral_add i0 i1
  rw [e1, e2, integral_radial_mul_inner_eq_zero, integral_radial_inner_sq (by omega) i2' m2,
    add_zero]
  congr 2
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  by_cases hz : ‖z‖ ∈ Ioo R R' <;> simp [hz]

lemma annP1_sq (a c0 : ℝ) (c : RN N) {z : RN N} (hz : z ≠ 0) :
    annP1 N a c0 c z ^ 2 = c0 ^ 2 * radPhi N a ‖z‖ ^ 2 +
      2 * c0 * radPhi N a ‖z‖ ^ 2 / ‖z‖ * ⟪c, z⟫ + radPhi N a ‖z‖ ^ 2 / ‖z‖ ^ 2 * ⟪c, z⟫ ^ 2 := by
  have hr : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  simp only [annP1]
  field_simp
  ring

lemma norm_annP2_sq (a c0 : ℝ) (c : RN N) {z : RN N} (hz : z ≠ 0) :
    ‖annP2 N a c0 c z‖ ^ 2 =
      (c0 ^ 2 * radPhi1 N a ‖z‖ ^ 2 + ‖c‖ ^ 2 * (radPhi N a ‖z‖ ^ 2 / ‖z‖ ^ 2)) +
      2 * c0 * radPhi1 N a ‖z‖ ^ 2 / ‖z‖ * ⟪c, z⟫ +
      (radPhi1 N a ‖z‖ ^ 2 / ‖z‖ ^ 2 - radPhi N a ‖z‖ ^ 2 / ‖z‖ ^ 4) * ⟪c, z⟫ ^ 2 := by
  have hr : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  set β := (Real.sqrt a / 2) ^ ((N : ℝ) / 2 - 1) *
    (2 * besselSeriesD ((N : ℝ) / 2 - 1) a (‖z‖ ^ 2))
  have hg : gradPhi N a z = β • z := rfl
  have h1 : radPhi1 N a ‖z‖ = β * ‖z‖ := by simp only [radPhi1, β]; ring
  rw [h1]
  simp only [annP2, hg]
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, inner_neg_left,
    inner_neg_right, inner_sub_left, inner_sub_right, RCLike.conj_to_real,
    real_inner_self_eq_norm_sq, real_inner_comm z c]
  field_simp
  ring

/-- **Norms and energies of `c₀ψ + ψ⟨c, x - y⟩/|x - y|`.** -/
theorem annulus_l2_qf (hN : 2 ≤ N) {a : ℝ} (ha : 0 < a) (y : RN N) {v : Amb N} {c0 : ℝ}
    {c : RN N} (hv : IsAnnRep a y v c0 c) :
    l2 v v = (c0 ^ 2 + ‖c‖ ^ 2 / N) * annJ0 N a ∧
      qf v v = (c0 ^ 2 + ‖c‖ ^ 2 / N) * annJ1 N a + ‖c‖ ^ 2 * (1 - 1 / N) * annJ2 N a := by
  have hR : 0 < annR N a := div_pos (besselZero_props (hN_nu hN)).1 (Real.sqrt_pos.mpr ha)
  have hr0 : ∀ r ∈ Icc (annR N a) (annR' N a), r ≠ 0 := fun r hr => (hR.trans_le hr.1).ne'
  have hφ := (continuous_radPhi hN ha.le).continuousOn (s := Icc (annR N a) (annR' N a))
  have hφ1 := (continuous_radPhi1 hN ha.le).continuousOn (s := Icc (annR N a) (annR' N a))
  have hid : ContinuousOn (fun r : ℝ => r) (Icc (annR N a) (annR' N a)) := continuousOn_id
  have hzA : ∀ x, x ∈ annulus N a y → x - y ≠ 0 := fun x hx h => by
    have := hx.1; rw [h, norm_zero] at this; linarith
  have hJ0' : ∀ k : ℝ, ∫ z : RN N, (Ioo (annR N a) (annR' N a)).indicator (fun r => k * radPhi N a r ^ 2) ‖z‖ =
      k * annJ0 N a := fun k => by
    rw [annJ0, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    by_cases hz : ‖z‖ ∈ Ioo (annR N a) (annR' N a) <;> simp [hz]
  have i1 : Integrable (fun z : RN N => (Ioo (annR N a) (annR' N a)).indicator (fun r => radPhi1 N a r ^ 2) ‖z‖) := by
    simpa only [mul_one] using integrable_annulus_radial
      (g := fun r => radPhi1 N a r ^ 2) (hφ1.pow 2) (continuous_const (y := (1 : ℝ)))
  have i2 : Integrable (fun z : RN N => (Ioo (annR N a) (annR' N a)).indicator (fun r => radPhi N a r ^ 2 / r ^ 2) ‖z‖) := by
    simpa only [mul_one] using integrable_annulus_radial
      (g := fun r => radPhi N a r ^ 2 / r ^ 2) ((hφ.pow 2).div (hid.pow 2)
      (fun r hr => pow_ne_zero 2 (hr0 r hr))) (continuous_const (y := (1 : ℝ)))
  constructor
  · rw [l2, MeasureTheory.L2.inner_def]
    have e : ∫ x : RN N, ⟪(v.1 : RN N → ℝ) x, (v.1 : RN N → ℝ) x⟫ =
        ∫ z : RN N, ((Ioo (annR N a) (annR' N a)).indicator (fun r => c0 ^ 2 * radPhi N a r ^ 2) ‖z‖ +
          (Ioo (annR N a) (annR' N a)).indicator (fun r => 2 * c0 * radPhi N a r ^ 2 / r) ‖z‖ * ⟪c, z⟫ +
          (Ioo (annR N a) (annR' N a)).indicator (fun r => radPhi N a r ^ 2 / r ^ 2) ‖z‖ * ⟪c, z⟫ ^ 2) := by
      conv_rhs => rw [← integral_sub_right_eq_self _ y]
      refine integral_congr_ae ?_
      filter_upwards [hv.1] with x hx
      rw [hx, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
      by_cases hxA : x ∈ annulus N a y
      · have hI : ‖x - y‖ ∈ Ioo (annR N a) (annR' N a) := hxA
        simp only [indicator_of_mem hxA, indicator_of_mem hI]
        exact annP1_sq a c0 c (hzA x hxA)
      · have hI : ‖x - y‖ ∉ Ioo (annR N a) (annR' N a) := hxA
        simp [indicator_of_notMem hxA, indicator_of_notMem hI]
    rw [e, integral_radial_quad hN (g0 := fun r => c0 ^ 2 * radPhi N a r ^ 2)
      (g1 := fun r => 2 * c0 * radPhi N a r ^ 2 / r) (g2 := fun r => radPhi N a r ^ 2 / r ^ 2)
      (continuous_const.continuousOn.mul (hφ.pow 2))
      (((continuous_const.continuousOn.mul (hφ.pow 2))).div hid hr0)
      ((hφ.pow 2).div (hid.pow 2) (fun r hr => pow_ne_zero 2 (hr0 r hr))), hJ0']
    have e2 : ∫ z : RN N, (Ioo (annR N a) (annR' N a)).indicator (fun r => radPhi N a r ^ 2 / r ^ 2 * r ^ 2) ‖z‖ =
        annJ0 N a := by
      rw [annJ0]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      by_cases hz : ‖z‖ ∈ Ioo (annR N a) (annR' N a)
      · simp only [indicator_of_mem hz]
        have : ‖z‖ ≠ 0 := (hR.trans hz.1).ne'
        field_simp
      · simp [indicator_of_notMem hz]
    rw [e2]
    ring
  · rw [qf, MeasureTheory.L2.inner_def]
    have e : ∫ x : RN N, ⟪(v.2 : RN N → RN N) x, (v.2 : RN N → RN N) x⟫ =
        ∫ z : RN N, ((Ioo (annR N a) (annR' N a)).indicator
            (fun r => c0 ^ 2 * radPhi1 N a r ^ 2 + ‖c‖ ^ 2 * (radPhi N a r ^ 2 / r ^ 2)) ‖z‖ +
          (Ioo (annR N a) (annR' N a)).indicator (fun r => 2 * c0 * radPhi1 N a r ^ 2 / r) ‖z‖ * ⟪c, z⟫ +
          (Ioo (annR N a) (annR' N a)).indicator (fun r => radPhi1 N a r ^ 2 / r ^ 2 - radPhi N a r ^ 2 / r ^ 4) ‖z‖ *
            ⟪c, z⟫ ^ 2) := by
      conv_rhs => rw [← integral_sub_right_eq_self _ y]
      refine integral_congr_ae ?_
      filter_upwards [hv.2] with x hx
      rw [hx, real_inner_self_eq_norm_sq]
      by_cases hxA : x ∈ annulus N a y
      · have hI : ‖x - y‖ ∈ Ioo (annR N a) (annR' N a) := hxA
        simp only [indicator_of_mem hxA, indicator_of_mem hI]
        exact norm_annP2_sq a c0 c (hzA x hxA)
      · have hI : ‖x - y‖ ∉ Ioo (annR N a) (annR' N a) := hxA
        simp [indicator_of_notMem hxA, indicator_of_notMem hI]
    rw [e, integral_radial_quad hN
      (g0 := fun r => c0 ^ 2 * radPhi1 N a r ^ 2 + ‖c‖ ^ 2 * (radPhi N a r ^ 2 / r ^ 2))
      (g1 := fun r => 2 * c0 * radPhi1 N a r ^ 2 / r)
      (g2 := fun r => radPhi1 N a r ^ 2 / r ^ 2 - radPhi N a r ^ 2 / r ^ 4)
      ((continuous_const.continuousOn.mul (hφ1.pow 2)).add (continuous_const.continuousOn.mul
        ((hφ.pow 2).div (hid.pow 2) (fun r hr => pow_ne_zero 2 (hr0 r hr)))))
      (((continuous_const.continuousOn.mul (hφ1.pow 2))).div hid hr0)
      (((hφ1.pow 2).div (hid.pow 2) (fun r hr => pow_ne_zero 2 (hr0 r hr))).sub
        ((hφ.pow 2).div (hid.pow 4) (fun r hr => pow_ne_zero 4 (hr0 r hr))))]
    have e1 : ∫ z : RN N, (Ioo (annR N a) (annR' N a)).indicator
        (fun r => c0 ^ 2 * radPhi1 N a r ^ 2 + ‖c‖ ^ 2 * (radPhi N a r ^ 2 / r ^ 2)) ‖z‖ =
        c0 ^ 2 * annJ1 N a + ‖c‖ ^ 2 * annJ2 N a := by
      rw [annJ1, annJ2, ← integral_const_mul, ← integral_const_mul,
        ← integral_add (i1.const_mul _) (i2.const_mul _)]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      by_cases hz : ‖z‖ ∈ Ioo (annR N a) (annR' N a) <;> simp [hz]
    have e2 : ∫ z : RN N, (Ioo (annR N a) (annR' N a)).indicator
        (fun r => (radPhi1 N a r ^ 2 / r ^ 2 - radPhi N a r ^ 2 / r ^ 4) * r ^ 2) ‖z‖ =
        annJ1 N a - annJ2 N a := by
      rw [annJ1, annJ2, ← integral_sub i1 i2]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      by_cases hz : ‖z‖ ∈ Ioo (annR N a) (annR' N a)
      · simp only [indicator_of_mem hz]
        have : ‖z‖ ≠ 0 := (hR.trans hz.1).ne'
        field_simp
      · simp [indicator_of_notMem hz]
    rw [e1, e2]
    ring

lemma annR_pos (hN : 2 ≤ N) {a : ℝ} (ha : 0 < a) : 0 < annR N a :=
  div_pos (besselZero_props (hN_nu hN)).1 (Real.sqrt_pos.mpr ha)

lemma annR_lt (hN : 2 ≤ N) {a : ℝ} (ha : 0 < a) : annR N a < annR' N a :=
  div_lt_div_of_pos_right (besselZero_props (hN_nu hN)).2.1 (Real.sqrt_pos.mpr ha)

/-- Polar form of `J₀`, `J₁`, `J₂`, and the energy identity `J₁ = a J₀`. -/
lemma annJ_polar (hN : 2 ≤ N) {a : ℝ} (ha : 0 < a) :
    annJ0 N a = (N * volume.real (ball (0 : RN N) 1)) *
        ∫ r in annR N a..annR' N a, r ^ (N - 1) * radPhi N a r ^ 2 ∧
      annJ1 N a = a * annJ0 N a ∧
      annJ2 N a = (N * volume.real (ball (0 : RN N) 1)) *
        ∫ r in annR N a..annR' N a, r ^ (N - 1) * (radPhi N a r ^ 2 / r ^ 2) := by
  have hR := annR_pos hN ha
  have hRR := annR_lt hN ha
  have hν := hN_nu hN
  obtain ⟨-, -, hz1, hz2, -, -⟩ := besselZero_props hν
  refine ⟨integral_annulus_radial hN hR.le hRR.le _, ?_, integral_annulus_radial hN hR.le hRR.le _⟩
  rw [annJ1, annJ0, integral_annulus_radial hN hR.le hRR.le, integral_annulus_radial hN hR.le hRR.le,
    radial_energy hN ha.le (R := annR N a) (R' := annR' N a) (radPhi_zero ha hz1)
      (radPhi_zero ha hz2)]
  ring

lemma coef_eq_zero_of_mul {c0 s J0 n : ℝ} (hs : 0 ≤ s) (hn : 0 < n) (hJ : 0 < J0)
    (h : (c0 ^ 2 + s / n) * J0 = 0) : c0 = 0 ∧ s = 0 := by
  have h' : c0 ^ 2 + s / n = 0 := by
    rcases mul_eq_zero.mp h with h | h
    · exact h
    · exact absurd h hJ.ne'
  have h1 : 0 ≤ s / n := div_nonneg hs hn.le
  have hc : c0 ^ 2 = 0 := by nlinarith [sq_nonneg c0]
  refine ⟨pow_eq_zero_iff (two_ne_zero) |>.mp hc, ?_⟩
  have : s / n = 0 := by nlinarith [sq_nonneg c0]
  rcases div_eq_zero_iff.mp this with h | h
  · exact h
  · exact absurd h hn.ne'

lemma annulus_final_ineq {a c0 s n Ω I1 I2 : ℝ} (hn : 1 ≤ n) (hΩ : 0 < Ω)
    (hI1 : 0 ≤ I1) (hI2 : 0 < I2) :
    (c0 ^ 2 + s / n) * (a * (Ω * I2)) + s * (1 - 1 / n) * (Ω * I1) ≤
      (a + (n - 1) * I1 / I2) * ((c0 ^ 2 + s / n) * (Ω * I2)) := by
  have hn0 : 0 < n := by linarith
  have key : (a + (n - 1) * I1 / I2) * ((c0 ^ 2 + s / n) * (Ω * I2)) -
      ((c0 ^ 2 + s / n) * (a * (Ω * I2)) + s * (1 - 1 / n) * (Ω * I1)) =
      (n - 1) * I1 * Ω * c0 ^ 2 := by
    field_simp
    ring
  have : 0 ≤ (n - 1) * I1 * Ω * c0 ^ 2 := by
    have : 0 ≤ n - 1 := by linarith
    positivity
  linarith

/-- **Separation of variables on the annulus** (the annulus part of the ball/annulus external
lemma of the paper). -/
theorem annulus_sep (hN : 2 ≤ N) {a : ℝ} (ha : 0 < a) (y : RN N) :
    let ν : ℝ := (N : ℝ) / 2 - 1
    let d : ℝ := (N : ℝ) - 1
    let R := besselZero ν 1 / Real.sqrt a
    let R' := besselZero ν 2 / Real.sqrt a
    let ρ : ℝ → ℝ := fun r => r ^ (-ν) * besselJ ν (Real.sqrt a * r)
    ∃ V : Submodule ℝ (Amb N), V ≤ H {x | R < ‖x - y‖ ∧ ‖x - y‖ < R'} ∧
      Module.finrank ℝ V = N + 1 ∧
      ∀ v ∈ V, qf v v ≤ (a + d * (∫ r in R..R', ρ r ^ 2 * r ^ (d - 2)) /
        (∫ r in R..R', ρ r ^ 2 * r ^ d)) * l2 v v := by
  intro ν d R R' ρ
  change ∃ V : Submodule ℝ (Amb N), V ≤ H (annulus N a y) ∧ Module.finrank ℝ V = N + 1 ∧
    ∀ v ∈ V, qf v v ≤ (a + d * (∫ r in annR N a..annR' N a, ρ r ^ 2 * r ^ (d - 2)) /
        (∫ r in annR N a..annR' N a, ρ r ^ 2 * r ^ d)) * l2 v v
  clear_value R R'
  set R := annR N a
  set R' := annR' N a
  have hR := annR_pos hN ha
  have hRR := annR_lt hN ha
  have hν := hN_nu hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  -- the one-dimensional integrals
  have hρφ : ∀ r ∈ uIcc R R', ρ r = radPhi N a r := fun r hr => by
    rw [uIcc_of_le hRR.le] at hr
    exact (radPhi_eq_bessel hN ha (hR.trans_le hr.1)).symm
  set I1 := ∫ r in R..R', ρ r ^ 2 * r ^ (d - 2)
  set I2 := ∫ r in R..R', ρ r ^ 2 * r ^ d
  have hI2 : I2 = ∫ r in annR N a..annR' N a, r ^ (N - 1) * radPhi N a r ^ 2 := by
    refine intervalIntegral.integral_congr fun r hr => ?_
    have hr0 : 0 < r := hR.trans_le (by rw [uIcc_of_le hRR.le] at hr; exact hr.1)
    rw [hρφ r hr, show d = ((N - 1 : ℕ) : ℝ) by simp only [d]; push_cast [show 1 ≤ N by omega]; ring,
      Real.rpow_natCast]
    ring
  have hI1 : I1 = ∫ r in annR N a..annR' N a, r ^ (N - 1) * (radPhi N a r ^ 2 / r ^ 2) := by
    refine intervalIntegral.integral_congr fun r hr => ?_
    have hr0 : 0 < r := hR.trans_le (by rw [uIcc_of_le hRR.le] at hr; exact hr.1)
    rw [hρφ r hr, show d = ((N - 1 : ℕ) : ℝ) by simp only [d]; push_cast [show 1 ≤ N by omega]; ring,
      Real.rpow_sub hr0, Real.rpow_natCast, Real.rpow_two]
    ring
  have hρc : ContinuousOn ρ (Icc R R') :=
    ((continuous_radPhi hN ha.le).continuousOn).congr fun r hr =>
      hρφ r (by rw [uIcc_of_le hRR.le]; exact hr)
  have hρ0 : ∀ r ∈ Ioo R R', ρ r ≠ 0 := fun r hr => by
    rw [hρφ r (by rw [uIcc_of_le hRR.le]; exact Ioo_subset_Icc_self hr)]
    exact (radPhi_neg_annulus hN ha hr.1 hr.2).ne
  have h2N : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hdpos : 0 < d := by simp only [d]; linarith
  obtain ⟨hI2pos, -⟩ := annulus_integral_ineq (d := d) hR hRR hρc hρ0
  have hI1nn : 0 ≤ I1 := intervalIntegral.integral_nonneg hRR.le fun r hr => by
    have hr0 : 0 < r := hR.trans_le hr.1
    positivity
  set Ω := (N : ℝ) * volume.real (ball (0 : RN N) 1)
  have hΩ : 0 < Ω := by
    refine mul_pos (by positivity) ?_
    exact ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne
  obtain ⟨hJ0, hJ1, hJ2⟩ := annJ_polar hN ha
  rw [← hI2] at hJ0
  rw [← hI1] at hJ2
  have hJ0pos : 0 < annJ0 N a := by rw [hJ0]; exact mul_pos hΩ hI2pos
  -- the spanning family
  obtain ⟨ψ, hψH, hψr⟩ := exists_annulus_psi hN ha y
  set b := EuclideanSpace.basisFun (Fin N) ℝ
  have hw := fun i => exists_annulus_psi_mul hN ha y hψH hψr (b i)
  choose w hwH hwr using hw
  set f : Option (Fin N) → Amb N := fun o => o.elim ψ w
  have hrep : ∀ g : Option (Fin N) → ℝ,
      IsAnnRep a y (∑ o, g o • f o) (g none) (∑ i, g (some i) • b i) :=
    fun g => IsAnnRep.sum_family b hψr hwr g
  have hNpos : (0 : ℝ) < N := by linarith
  have hli : LinearIndependent ℝ f := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    obtain ⟨hl, -⟩ := annulus_l2_qf hN ha y (hrep g)
    rw [hg] at hl
    simp only [l2, Prod.fst_zero, inner_zero_left] at hl
    obtain ⟨h1, h2⟩ := coef_eq_zero_of_mul (sq_nonneg _) hNpos hJ0pos hl.symm
    have h2' : ∑ i, g (some i) • b.toBasis i = 0 := by
      rw [b.coe_toBasis]
      exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h2)
    have h3 := Fintype.linearIndependent_iff.mp b.toBasis.linearIndependent (fun i => g (some i)) h2'
    intro o
    cases o with
    | none => exact h1
    | some i => exact h3 i
  refine ⟨Submodule.span ℝ (range f), ?_, ?_, ?_⟩
  · rw [Submodule.span_le]
    rintro _ ⟨o, rfl⟩
    cases o with
    | none => exact hψH
    | some i => exact hwH i
  · rw [finrank_span_eq_card hli]
    simp
  · intro v hv
    obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hv
    have hrv : IsAnnRep a y v (g none) (∑ i, g (some i) • b i) := hg ▸ hrep g
    obtain ⟨hl, hq⟩ := annulus_l2_qf hN ha y hrv
    rw [hl, hq, hJ1, hJ0, hJ2]
    exact annulus_final_ineq hN1 hΩ hI1nn hI2pos

end FourthRatio

end
