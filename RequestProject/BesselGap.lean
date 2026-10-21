module

public import RequestProject.BesselZeros
public import RequestProject.BallIntegrals

/-!
# A gap inequality for the first Bessel zeros

`besselZero_sq_gap`: for `ν ≥ 0`, `j_{ν,1}² + (2ν + 1) < j_{ν+1,1}²`.

With `d = 2ν + 1` and `k = j_{ν+1,1}`, the function `g(r) = r F_{ν+1}(r)` (a multiple of
`r^{-ν} J_{ν+1}(r)`) solves `r² g'' + d r g' + (r² - d) g = 0` and vanishes at `r = 0` and `r = k`,
so integration by parts gives
`∫₀ᵏ rᵈ g'² + d ∫₀ᵏ rᵈ F_{ν+1}² = ∫₀ᵏ rᵈ g²`.
The Picone identity with the positive functions `ρ(r) = F_ν(β r)`, `β < j_{ν,1}/k`, gives
`∫₀ᵏ rᵈ g'² ≥ (j_{ν,1}/k)² ∫₀ᵏ rᵈ g²`, and `r² < k²` on `(0,k)` gives
`∫₀ᵏ rᵈ g² < k² ∫₀ᵏ rᵈ F_{ν+1}²`.  Together: `k² > j_{ν,1}² + d`.

This is the one-dimensional content of the degree-one separation-of-variables computation
for the ball in the ball–annulus lemma of the paper (`C_N a ≥ a + (N-1)/R²`).
-/

@[expose] public section

open Filter Topology Set MeasureTheory

noncomputable section

namespace FourthRatio

/-- `F'` for `F = besselF ν`. -/
def besselF1 (ν x : ℝ) : ℝ := 2 * x * besselSeries1 ν (x ^ 2)

/-- `F''` for `F = besselF ν`. -/
def besselF2 (ν x : ℝ) : ℝ := 2 * besselSeries1 ν (x ^ 2) + 4 * x ^ 2 * besselSeries2 ν (x ^ 2)

lemma hasDerivAt_besselF' {ν : ℝ} (hν : 0 ≤ ν) (x : ℝ) :
    HasDerivAt (besselF ν) (besselF1 ν x) x := hasDerivAt_besselF hν x

lemma hasDerivAt_besselF1' {ν : ℝ} (hν : 0 ≤ ν) (x : ℝ) :
    HasDerivAt (besselF1 ν) (besselF2 ν x) x := hasDerivAt_besselF1 hν x

lemma besselF_ode' {ν : ℝ} (hν : 0 ≤ ν) (x : ℝ) :
    x * besselF2 ν x + (2 * ν + 1) * besselF1 ν x + x * besselF ν x = 0 := by
  have := besselF_ode hν x
  unfold besselF1 besselF2
  linear_combination this

lemma hasDerivAt_rpow_d {d r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun x : ℝ => x ^ d) (d * r ^ d / r) r := by
  have := Real.hasDerivAt_rpow_const (p := d) (Or.inl hr.ne')
  rwa [Real.rpow_sub_one hr.ne', ← mul_div_assoc] at this

lemma continuousOn_rpow_d {d : ℝ} (hd : 0 < d) (s : Set ℝ) :
    ContinuousOn (fun x : ℝ => x ^ d) s :=
  fun r _ => (Real.continuousAt_rpow_const r d (Or.inr hd.le)).continuousWithinAt

/-- **Picone inequality.** If `ρ > 0` on `[0,k]` solves `r ρ'' + d ρ' + b r ρ = 0` and
`g(k) = 0`, then `b ∫₀ᵏ rᵈ g² ≤ ∫₀ᵏ rᵈ g'²`. -/
lemma picone_ineq {d k b : ℝ} (hd : 0 < d) (hk : 0 < k) {ρ ρ1 ρ2 g g1 : ℝ → ℝ}
    (hρ : ∀ r, HasDerivAt ρ (ρ1 r) r) (hρ1 : ∀ r, HasDerivAt ρ1 (ρ2 r) r)
    (hode : ∀ r, r * ρ2 r + d * ρ1 r + b * r * ρ r = 0)
    (hpos : ∀ r ∈ Icc 0 k, 0 < ρ r)
    (hg : ∀ r, HasDerivAt g (g1 r) r) (hg1c : Continuous g1) (hgk : g k = 0) :
    b * ∫ r in (0 : ℝ)..k, r ^ d * g r ^ 2 ≤ ∫ r in (0 : ℝ)..k, r ^ d * g1 r ^ 2 := by
  have hρc : Continuous ρ := continuous_iff_continuousAt.mpr fun r => (hρ r).continuousAt
  have hρ1c : Continuous ρ1 := continuous_iff_continuousAt.mpr fun r => (hρ1 r).continuousAt
  have hgc : Continuous g := continuous_iff_continuousAt.mpr fun r => (hg r).continuousAt
  have hpw := continuousOn_rpow_d hd (Icc 0 k)
  set P : ℝ → ℝ := fun r => r ^ d * ρ1 r * g r ^ 2 / ρ r with hP
  set S : ℝ → ℝ := fun r => r ^ d * (g1 r - g r * ρ1 r / ρ r) ^ 2 with hS
  set Q : ℝ → ℝ := fun r => r ^ d * g1 r ^ 2 - b * (r ^ d * g r ^ 2) - S r with hQ
  have hne : ∀ r ∈ Icc 0 k, ρ r ≠ 0 := fun r hr => (hpos r hr).ne'
  have hSc : ContinuousOn S (Icc 0 k) :=
    hpw.mul (((hg1c.continuousOn).sub ((hgc.mul hρ1c).continuousOn.div hρc.continuousOn hne)).pow 2)
  have hQc : ContinuousOn Q (Icc 0 k) :=
    ((hpw.mul (hg1c.pow 2).continuousOn).sub
      ((hpw.mul (hgc.pow 2).continuousOn).const_smul b)).sub hSc
  have hPc : ContinuousOn P (Icc 0 k) :=
    ((hpw.mul hρ1c.continuousOn).mul (hgc.pow 2).continuousOn).div hρc.continuousOn hne
  have hderiv : ∀ r ∈ Ioo 0 k, HasDerivAt P (Q r) r := by
    intro r hr
    have hr0 : 0 < r := hr.1
    have hρr : ρ r ≠ 0 := hne r (Ioo_subset_Icc_self hr)
    have h := (((hasDerivAt_rpow_d (d := d) hr0).mul (hρ1 r)).mul ((hg r).pow 2)).div (hρ r) hρr
    convert h using 1
    have ho := hode r
    have h2 : ρ2 r = -(d * ρ1 r + b * r * ρ r) / r := by
      field_simp; linarith
    simp only [hQ, hS, h2, Pi.mul_apply, Pi.pow_apply]
    field_simp
    ring
  have hint : IntervalIntegrable Q volume 0 k :=
    hQc.intervalIntegrable_of_Icc hk.le
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hk.le hPc hderiv hint
  have hP0 : P k - P 0 = 0 := by
    simp only [hP, hgk, Real.zero_rpow hd.ne']
    ring
  rw [hP0] at hFTC
  have hi1 : IntervalIntegrable (fun r => r ^ d * g1 r ^ 2) volume 0 k :=
    (hpw.mul (hg1c.pow 2).continuousOn).intervalIntegrable_of_Icc hk.le
  have hi2 : IntervalIntegrable (fun r => r ^ d * g r ^ 2) volume 0 k :=
    (hpw.mul (hgc.pow 2).continuousOn).intervalIntegrable_of_Icc hk.le
  have hi3 : IntervalIntegrable S volume 0 k := hSc.intervalIntegrable_of_Icc hk.le
  have hSnn : 0 ≤ ∫ r in (0 : ℝ)..k, S r := by
    refine intervalIntegral.integral_nonneg hk.le fun r hr => ?_
    have : 0 ≤ r ^ d := Real.rpow_nonneg hr.1 _
    simp only [hS]; positivity
  have hQeq : ∫ r in (0 : ℝ)..k, Q r = (∫ r in (0 : ℝ)..k, r ^ d * g1 r ^ 2) -
      b * (∫ r in (0 : ℝ)..k, r ^ d * g r ^ 2) - ∫ r in (0 : ℝ)..k, S r := by
    simp only [hQ]
    rw [intervalIntegral.integral_sub (hi1.sub (hi2.const_mul b)) hi3,
      intervalIntegral.integral_sub hi1 (hi2.const_mul b), intervalIntegral.integral_const_mul]
  linarith

/-- **Energy identity.** If `r F'' + (d+2) F' + r F = 0` and `F(k) = 0`, then with
`g = r F`: `∫₀ᵏ (rᵈ g'² + d rᵈ F² - rᵈ g²) = 0`. -/
lemma energy_id {d k : ℝ} (hd : 0 < d) (hk : 0 < k) {F F1 F2 : ℝ → ℝ}
    (hF : ∀ r, HasDerivAt F (F1 r) r) (hF1 : ∀ r, HasDerivAt F1 (F2 r) r)
    (hode : ∀ r, r * F2 r + (d + 2) * F1 r + r * F r = 0) (hFk : F k = 0) :
    ∫ r in (0 : ℝ)..k, (r ^ d * (F r + r * F1 r) ^ 2 + d * (r ^ d * F r ^ 2) -
      r ^ d * (r * F r) ^ 2) = 0 := by
  have hFc : Continuous F := continuous_iff_continuousAt.mpr fun r => (hF r).continuousAt
  have hF1c : Continuous F1 := continuous_iff_continuousAt.mpr fun r => (hF1 r).continuousAt
  have hpw := continuousOn_rpow_d hd (Icc 0 k)
  set E : ℝ → ℝ := fun r => r ^ d * (r * F r) * (F r + r * F1 r) with hE
  have hEc : ContinuousOn E (Icc 0 k) :=
    (hpw.mul (continuous_id.mul hFc).continuousOn).mul
      (hFc.add (continuous_id.mul hF1c)).continuousOn
  have hderiv : ∀ r ∈ Ioo 0 k, HasDerivAt E (r ^ d * (F r + r * F1 r) ^ 2 +
      d * (r ^ d * F r ^ 2) - r ^ d * (r * F r) ^ 2) r := by
    intro r hr
    have hr0 : 0 < r := hr.1
    have h := ((hasDerivAt_rpow_d (d := d) hr0).mul ((hasDerivAt_id r).mul (hF r))).mul
      ((hF r).add ((hasDerivAt_id r).mul (hF1 r)))
    convert h using 1
    · rfl
    · have ho := hode r
      have h2 : F2 r = -((d + 2) * F1 r + r * F r) / r := by
        field_simp; linarith
      simp only [h2, id, Pi.mul_apply, Pi.add_apply]
      field_simp
      ring
  have hint : IntervalIntegrable (fun r => r ^ d * (F r + r * F1 r) ^ 2 +
      d * (r ^ d * F r ^ 2) - r ^ d * (r * F r) ^ 2) volume 0 k := by
    refine ContinuousOn.intervalIntegrable_of_Icc hk.le ?_
    exact ((hpw.mul ((hFc.add (continuous_id.mul hF1c)).pow 2).continuousOn).add
      ((hpw.mul (hFc.pow 2).continuousOn).const_smul d)).sub
      (hpw.mul ((continuous_id.mul hFc).pow 2).continuousOn)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hk.le hEc hderiv hint]
  simp only [hE, hFk, Real.zero_rpow hd.ne']
  ring

/-- **Gap between the first zeros of `J_ν` and `J_{ν+1}`:** `j_{ν,1}² + (2ν + 1) < j_{ν+1,1}²`. -/
theorem besselZero_sq_gap {ν : ℝ} (hν : 0 ≤ ν) :
    besselZero ν 1 ^ 2 + (2 * ν + 1) < besselZero (ν + 1) 1 ^ 2 := by
  have hν' : 0 ≤ ν + 1 := by linarith
  obtain ⟨hj, -⟩ := besselZero_props hν
  obtain ⟨hk, -, hFk, -⟩ := besselZero_props hν'
  set j := besselZero ν 1 with hjdef
  set k := besselZero (ν + 1) 1 with hkdef
  set d : ℝ := 2 * ν + 1 with hddef
  have hd : 0 < d := by positivity
  set F := besselF (ν + 1)
  set F1 := besselF1 (ν + 1)
  have hF : ∀ r, HasDerivAt F (F1 r) r := hasDerivAt_besselF' hν'
  have hF1 : ∀ r, HasDerivAt F1 (besselF2 (ν + 1) r) r := hasDerivAt_besselF1' hν'
  have hFc : Continuous F := continuous_iff_continuousAt.mpr fun r => (hF r).continuousAt
  have hF1c : Continuous F1 := continuous_iff_continuousAt.mpr fun r => (hF1 r).continuousAt
  have hFk' : F k = 0 := hFk
  -- integrals
  set A := ∫ r in (0 : ℝ)..k, r ^ d * (r * F r) ^ 2 with hA
  set B := ∫ r in (0 : ℝ)..k, r ^ d * (F r + r * F1 r) ^ 2 with hB
  set C := ∫ r in (0 : ℝ)..k, r ^ d * F r ^ 2 with hC
  have hpw := continuousOn_rpow_d hd (Icc 0 k)
  have hiA : IntervalIntegrable (fun r => r ^ d * (r * F r) ^ 2) volume 0 k :=
    (hpw.mul ((continuous_id.mul hFc).pow 2).continuousOn).intervalIntegrable_of_Icc hk.le
  have hiB : IntervalIntegrable (fun r => r ^ d * (F r + r * F1 r) ^ 2) volume 0 k :=
    (hpw.mul ((hFc.add (continuous_id.mul hF1c)).pow 2).continuousOn).intervalIntegrable_of_Icc
      hk.le
  have hiC : IntervalIntegrable (fun r => r ^ d * F r ^ 2) volume 0 k :=
    (hpw.mul (hFc.pow 2).continuousOn).intervalIntegrable_of_Icc hk.le
  -- energy identity
  have hE : B + d * C - A = 0 := by
    have h := energy_id (d := d) hd hk hF hF1 (fun r => by
      have := besselF_ode' hν' r
      simp only [F1, F]
      rw [show d + 2 = 2 * (ν + 1) + 1 by simp only [hddef]; ring]
      exact this) hFk'
    rw [intervalIntegral.integral_sub (hiB.add (hiC.const_mul d)) hiA,
      intervalIntegral.integral_add hiB (hiC.const_mul d), intervalIntegral.integral_const_mul]
      at h
    exact h
  -- `A < k² C` and `0 < A`
  have hF0 : 0 < F 0 := besselF_zero_pos hν'
  obtain ⟨r0, hr0, hFr0⟩ : ∃ r0 ∈ Ioo 0 k, F r0 ≠ 0 := by
    have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < F r :=
      nhdsWithin_le_nhds (hFc.continuousAt.eventually (lt_mem_nhds hF0))
    obtain ⟨r, h1, h2⟩ := (hev.and (Ioo_mem_nhdsGT hk)).exists
    exact ⟨r, h2, h1.ne'⟩
  have hApos : 0 < A := by
    refine integral_pos_of_nonneg_of_pos_near hiA (fun r hr => ?_) hr0 ?_ ?_
    · have : 0 ≤ r ^ d := Real.rpow_nonneg hr.1.le _
      positivity
    · exact ((continuousOn_rpow_d hd univ).continuousAt univ_mem).mul
        ((continuous_id.mul hFc).pow 2).continuousAt
    · have : 0 < r0 ^ d := Real.rpow_pos_of_pos hr0.1 _
      have : r0 * F r0 ≠ 0 := mul_ne_zero hr0.1.ne' hFr0
      positivity
  have hAC : A < k ^ 2 * C := by
    have key : 0 < ∫ r in (0 : ℝ)..k, (k ^ 2 * (r ^ d * F r ^ 2) - r ^ d * (r * F r) ^ 2) := by
      have hpt : ∀ r, k ^ 2 * (r ^ d * F r ^ 2) - r ^ d * (r * F r) ^ 2 =
          r ^ d * F r ^ 2 * (k ^ 2 - r ^ 2) := fun r => by ring
      refine integral_pos_of_nonneg_of_pos_near ((hiC.const_mul _).sub hiA) (fun r hr => ?_)
        hr0 ?_ ?_
      · rw [hpt]
        have : 0 ≤ r ^ d := Real.rpow_nonneg hr.1.le _
        have : 0 ≤ k ^ 2 - r ^ 2 := by nlinarith [hr.2, hr.1]
        positivity
      · have hc := (continuousOn_rpow_d hd univ).continuousAt (x := r0) univ_mem
        exact (continuousAt_const.mul (hc.mul (hFc.pow 2).continuousAt)).sub
          (hc.mul ((continuous_id.mul hFc).pow 2).continuousAt)
      · rw [hpt]
        have : 0 < r0 ^ d := Real.rpow_pos_of_pos hr0.1 _
        have : 0 < k ^ 2 - r0 ^ 2 := by nlinarith [hr0.2, hr0.1]
        have : 0 < F r0 ^ 2 := by positivity
        positivity
    rw [intervalIntegral.integral_sub (hiC.const_mul _) hiA,
      intervalIntegral.integral_const_mul] at key
    linarith
  -- Picone: `(j/k)² A ≤ B`
  have hβ : 0 < j / k := div_pos hj hk
  have hPic : ∀ β ∈ Ioo 0 (j / k), β ^ 2 * A ≤ B := by
    intro β hβ'
    have hb0 : 0 < β := hβ'.1
    have h := picone_ineq (d := d) (b := β ^ 2) hd hk
      (ρ := fun r => besselF ν (β * r)) (ρ1 := fun r => β * besselF1 ν (β * r))
      (ρ2 := fun r => β ^ 2 * besselF2 ν (β * r)) (g := fun r => r * F r)
      (g1 := fun r => F r + r * F1 r)
      (fun r => by
        have := (hasDerivAt_besselF' hν (β * r)).comp r ((hasDerivAt_id r).const_mul β)
        convert this using 1
        · rfl
        · ring)
      (fun r => by
        have := ((hasDerivAt_besselF1' hν (β * r)).comp r
          ((hasDerivAt_id r).const_mul β)).const_mul β
        convert this using 1
        · rfl
        · ring)
      (fun r => by
        have := besselF_ode' hν (β * r)
        linear_combination β * this)
      (fun r hr => by
        refine besselF_pos_before hν (by positivity [hr.1]) ?_
        have h1 : β * r ≤ β * k := mul_le_mul_of_nonneg_left hr.2 hb0.le
        have h2 : β * k < j / k * k := mul_lt_mul_of_pos_right hβ'.2 hk
        rw [div_mul_cancel₀ _ hk.ne'] at h2
        linarith)
      (fun r => by
        have := (hasDerivAt_id r).mul (hF r)
        convert this using 1
        · rfl
        · simp)
      (hFc.add (continuous_id.mul hF1c))
      (by simp [hFk'])
    simp only [hA, hB]
    convert h using 2
  have hB' : (j / k) ^ 2 * A ≤ B := by
    have ht : Tendsto (fun β : ℝ => β ^ 2 * A) (𝓝[<] (j / k)) (𝓝 ((j / k) ^ 2 * A)) :=
      ((continuous_pow 2).mul continuous_const).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds
    refine le_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsLT hβ] with β hβ'
    exact hPic β hβ'
  -- conclusion
  have hk2 : 0 < k ^ 2 := by positivity
  have h1 : (j / k) ^ 2 * A * k ^ 2 = j ^ 2 * A := by
    field_simp
  have h3 : j ^ 2 * A + d * A < k ^ 2 * A := by
    have : d * A < d * (k ^ 2 * C) := mul_lt_mul_of_pos_left hAC hd
    nlinarith
  have h4 : (j ^ 2 + d) * A < k ^ 2 * A := by linarith
  exact lt_of_mul_lt_mul_right h4 hApos.le

end FourthRatio

end
