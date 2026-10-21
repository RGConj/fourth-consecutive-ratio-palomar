module

public import RequestProject.PPWABMono

/-!
# The gap identity of the ball for the Ashbaugh–Benguria profile

`∫_{B_R} B(|x|²) Φ² = (C_N - 1) a ∫_{B_R} G(|x|²) Φ²`, proved in polar coordinates: the radial
integrand is the derivative of `r^{N-1} g(r) g'(r) φ(r)²`, `g(r) = r h(r²)`, which vanishes at
`r = 0` and at `r = R`.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology

noncomputable section

namespace FourthRatio

variable {N : ℕ}

/-- The radial derivative identity, in abstract form. -/
lemma radial_key (n : ℕ) {A A1 A2 Q Q1 Q2 : ℝ → ℝ} {a C r : ℝ}
    (hA : ∀ s, HasDerivAt A (A1 s) s) (hA1 : ∀ s, HasDerivAt A1 (A2 s) s)
    (hQ : ∀ s, HasDerivAt Q (Q1 s) s) (hQ1 : ∀ s, HasDerivAt Q1 (Q2 s) s)
    (eA : ∀ s, 2 * ((n : ℝ) + 2) * A1 s + 4 * s * A2 s = -a * A s)
    (eQ : ∀ s, 2 * ((n : ℝ) + 4) * Q1 s + 4 * s * Q2 s = -(C * a) * Q s)
    (hr : r ≠ 0) (hAr : A (r ^ 2) ≠ 0) :
    HasDerivAt (fun u => u ^ (n + 1) * (u * Q (u ^ 2)) *
        (((Q (u ^ 2) + 2 * u ^ 2 * Q1 (u ^ 2)) * A (u ^ 2) - u * Q (u ^ 2) * (2 * u * A1 (u ^ 2))) /
          A (u ^ 2)))
      (r ^ (n + 1) * A (r ^ 2) ^ 2 *
        (((n : ℝ) + 2) * (Q (r ^ 2) / A (r ^ 2)) ^ 2 +
          4 * r ^ 2 * (Q (r ^ 2) / A (r ^ 2)) *
            ((Q1 (r ^ 2) * A (r ^ 2) - Q (r ^ 2) * A1 (r ^ 2)) / A (r ^ 2) ^ 2) +
          4 * (r ^ 2) ^ 2 * ((Q1 (r ^ 2) * A (r ^ 2) - Q (r ^ 2) * A1 (r ^ 2)) / A (r ^ 2) ^ 2) ^ 2 -
          (C - 1) * a * r ^ 2 * (Q (r ^ 2) / A (r ^ 2)) ^ 2)) r := by
  have hsq : HasDerivAt (fun u : ℝ => u ^ 2) (2 * r) r := by simpa using hasDerivAt_pow 2 r
  have dA := (hA (r ^ 2)).comp r hsq
  have dA1 := (hA1 (r ^ 2)).comp r hsq
  have dQ := (hQ (r ^ 2)).comp r hsq
  have dQ1 := (hQ1 (r ^ 2)).comp r hsq
  have dpow := hasDerivAt_pow (n + 1) r
  have dId := hasDerivAt_id r
  have h := (dpow.mul (dId.mul dQ)).mul
    ((((dQ.add ((hsq.const_mul 2).mul dQ1)).mul dA).sub
      ((dId.mul dQ).mul ((dId.const_mul 2).mul dA1))).div dA hAr)
  refine h.congr_deriv ?_
  have e1 := eA (r ^ 2)
  have e2 := eQ (r ^ 2)
  have hr2 : (r ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 hr
  have hA2 : A2 (r ^ 2) = (-a * A (r ^ 2) - 2 * ((n : ℝ) + 2) * A1 (r ^ 2)) / (4 * r ^ 2) := by
    field_simp; linarith
  have hQ2 : Q2 (r ^ 2) = (-(C * a) * Q (r ^ 2) - 2 * ((n : ℝ) + 4) * Q1 (r ^ 2)) / (4 * r ^ 2) := by
    field_simp; linarith
  simp only [Function.comp_apply, id, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.div_apply]
  rw [hA2, hQ2]
  push_cast
  field_simp
  ring

/-- Polar coordinates on a ball centred at `0`, for a radial integrand. -/
lemma radial_ball_integral (hN : 2 ≤ N) {R : ℝ} (hR : 0 ≤ R) (G : ℝ → ℝ) :
    ∫ x in ball (0 : RN N) R, G ‖x‖ =
      (N * volume.real (ball (0 : RN N) 1)) * ∫ r in 0..R, r ^ (N - 1) * G r := by
  haveI : Nontrivial (RN N) := by
    have : Nontrivial (Fin N) := Fin.nontrivial_iff_two_le.mpr hN
    infer_instance
  rw [← integral_annulus_radial hN le_rfl hR G, ← integral_indicator measurableSet_ball]
  apply integral_congr_ae
  have h0 : ∀ᵐ x : RN N ∂volume, x ≠ 0 := by simp [ae_iff, measure_singleton]
  filter_upwards [h0] with x hx
  have hx' : 0 < ‖x‖ := norm_pos_iff.mpr hx
  by_cases hb : ‖x‖ < R
  · rw [indicator_of_mem (by simpa using hb), indicator_of_mem (show ‖x‖ ∈ Ioo 0 R from ⟨hx', hb⟩)]
  · rw [indicator_of_notMem (by simpa using hb), indicator_of_notMem (fun (h : ‖x‖ ∈ Ioo 0 R) => hb h.2)]

variable {a η : ℝ}

/-- `h₁ = Q/A` and its derivative on `(0, R²)`. -/
lemma abH1_deriv_eq (hN : 2 ≤ N) (ha : 0 < a) (hη0 : 0 < η)
    (hη : ∀ s ∈ Icc 0 (annR N a ^ 2), abAt N a s ≤ -η) {s : ℝ} (hs : s ∈ Ioo 0 (annR N a ^ 2)) :
    deriv (abH1 N a η) s =
      (besselSeriesD ((N : ℝ) / 2) (CN N * a) s * abA N a s -
          abQ N a s * besselSeriesD ((N : ℝ) / 2 - 1) a s) / abA N a s ^ 2 := by
  have hev : abH1 N a η =ᶠ[𝓝 s] fun s => abQ N a s / abA N a s := by
    filter_upwards [Ioo_mem_nhds hs.1 hs.2] with u hu
    exact abH1_eq_div hN ha hη hη0 hu.1.le hu.2
  have hd : HasDerivAt (fun s => abQ N a s / abA N a s) _ s :=
    (hasDerivAt_abQ hN ha s).div (hasDerivAt_abA hN ha s) (abA_pos hN ha hs.1.le hs.2).ne'
  rw [hev.deriv_eq, hd.deriv]

/-- The radial integrand of the gap identity integrates to `0` over `[0, R]`. -/
lemma ab_radial_zero (hN : 2 ≤ N) (ha : 0 < a) (hη0 : 0 < η)
    (hη : ∀ s ∈ Icc 0 (annR N a ^ 2), abAt N a s ≤ -η) :
    ∫ r in (0 : ℝ)..annR N a, r ^ (N - 1) * abA N a (r ^ 2) ^ 2 *
      (abBs N a η (r ^ 2) - (CN N - 1) * a * r ^ 2 * abH1 N a η (r ^ 2) ^ 2) = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
  have hN' : 2 ≤ n + 2 := by omega
  have e1 : n + 2 - 1 = n + 1 := by omega
  rw [e1]
  set R := annR (n + 2) a with hRdef
  have hR : 0 < R := annR_pos hN ha
  set h := abH1 (n + 2) a η with hh
  have hc := contDiff_abH1 hN ha hη0
  have hcont : Continuous h := hc.continuous
  have hcont' : Continuous (deriv h) := hc.continuous_deriv (by simp)
  have hAc : Continuous (abA (n + 2) a) := continuous_iff_continuousAt.mpr fun s =>
    (hasDerivAt_abA hN ha s).continuousAt
  set F : ℝ → ℝ := fun r => r ^ (n + 1) * (r * h (r ^ 2)) *
    (h (r ^ 2) + 2 * r ^ 2 * deriv h (r ^ 2)) * abA (n + 2) a (r ^ 2) ^ 2 with hF
  have hFc : Continuous F := by simp only [hF]; fun_prop
  have hBc := continuous_abBs hN ha hη0
  have hTc : Continuous fun r : ℝ => r ^ (n + 1) * abA (n + 2) a (r ^ 2) ^ 2 *
      (abBs (n + 2) a η (r ^ 2) - (CN (n + 2) - 1) * a * r ^ 2 * h (r ^ 2) ^ 2) := by
    fun_prop
  have hderiv : ∀ r ∈ Ioo 0 R, HasDerivAt F (r ^ (n + 1) * abA (n + 2) a (r ^ 2) ^ 2 *
      (abBs (n + 2) a η (r ^ 2) - (CN (n + 2) - 1) * a * r ^ 2 * h (r ^ 2) ^ 2)) r := by
    intro r hr
    have hr0 : r ≠ 0 := hr.1.ne'
    have hsI : ∀ u ∈ Ioo 0 R, u ^ 2 ∈ Ioo 0 (annR (n + 2) a ^ 2) := fun u hu =>
      ⟨by have := hu.1; positivity, pow_lt_pow_left₀ hu.2 hu.1.le (by norm_num)⟩
    have hApos := abA_pos hN ha (hsI r hr).1.le (hsI r hr).2
    have eν : 2 * (((n + 2 : ℕ) : ℝ) / 2 - 1) + 2 = (n : ℝ) + 2 := by push_cast; ring
    have eμ : 2 * (((n + 2 : ℕ) : ℝ) / 2) + 2 = (n : ℝ) + 4 := by push_cast; ring
    have hk := radial_key n (A := abA (n + 2) a)
      (A1 := besselSeriesD (((n + 2 : ℕ) : ℝ) / 2 - 1) a)
      (A2 := besselSeriesDD (((n + 2 : ℕ) : ℝ) / 2 - 1) a) (Q := abQ (n + 2) a)
      (Q1 := besselSeriesD (((n + 2 : ℕ) : ℝ) / 2) (CN (n + 2) * a))
      (Q2 := besselSeriesDD (((n + 2 : ℕ) : ℝ) / 2) (CN (n + 2) * a)) (a := a) (C := CN (n + 2))
      (r := r) (hasDerivAt_abA hN ha)
      (fun s => hasDerivAt_besselSeries_deriv (hN_nu hN) ha.le s) (hasDerivAt_abQ hN ha)
      (fun s => hasDerivAt_besselSeries_deriv (by positivity) (CN_mul_nonneg hN ha) s)
      (fun s => by
        have := besselSeries_ode (hN_nu hN) ha.le s
        rw [eν] at this
        exact this)
      (fun s => by
        have := besselSeries_ode (ν := ((n + 2 : ℕ) : ℝ) / 2) (by positivity)
          (CN_mul_nonneg hN ha) s
        rw [eμ] at this
        exact this)
      hr0 hApos.ne'
    refine (hk.congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards [Ioo_mem_nhds hr.1 hr.2] with u hu
      have su := hsI u hu
      have hAu := (abA_pos hN ha su.1.le su.2).ne'
      simp only [hF, hh]
      rw [abH1_eq_div hN ha hη hη0 su.1.le su.2, abH1_deriv_eq hN ha hη0 hη su]
      field_simp
      ring
    · have su := hsI r hr
      simp only [hh]
      rw [abBs, abH1_eq_div hN ha hη hη0 su.1.le su.2, abH1_deriv_eq hN ha hη0 hη su]
      push_cast
      field_simp
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hR.le hFc.continuousOn hderiv
    (hTc.intervalIntegrable _ _)
  rw [hFTC]
  have hF0 : F 0 = 0 := by simp [hF]
  have hFR : F R = 0 := by simp [hF, hRdef, abA_R hN ha]
  rw [hF0, hFR, sub_zero]

/-- **Gap identity of the ball** for the Ashbaugh–Benguria profile. -/
theorem abProfile_ball_identity (hN : 2 ≤ N) (ha : 0 < a) (hη0 : 0 < η)
    (hη : ∀ s ∈ Icc 0 (annR N a ^ 2), abAt N a s ≤ -η) :
    ∫ x in ball (0 : RN N) (annR N a),
        (abProfile hN ha hη0 hη).Bw (‖x‖ ^ 2) * besselEntire N a x ^ 2 =
      (CN N - 1) * a * ∫ x in ball (0 : RN N) (annR N a),
        (abProfile hN ha hη0 hη).Gw (‖x‖ ^ 2) * besselEntire N a x ^ 2 := by
  set p := abProfile hN ha hη0 hη
  set R := annR N a with hRdef
  have hR : 0 < R := annR_pos hN ha
  set cE := (Real.sqrt a / 2) ^ ((N : ℝ) / 2 - 1) with hcE
  have hE : ∀ x : RN N, besselEntire N a x = cE * abA N a (‖x‖ ^ 2) := fun x => rfl
  simp only [hE]
  have h1 := radial_ball_integral hN hR.le (fun r => p.Bw (r ^ 2) * (cE * abA N a (r ^ 2)) ^ 2)
  have h2 := radial_ball_integral hN hR.le (fun r => p.Gw (r ^ 2) * (cE * abA N a (r ^ 2)) ^ 2)
  rw [h1, h2]
  have hBr : ∫ r in (0 : ℝ)..R, r ^ (N - 1) * (p.Bw (r ^ 2) * (cE * abA N a (r ^ 2)) ^ 2) =
      ∫ r in (0 : ℝ)..R, r ^ (N - 1) * (abBs N a η (r ^ 2) * (cE * abA N a (r ^ 2)) ^ 2) := by
    apply intervalIntegral.integral_congr_ae
    have hne : ∀ᵐ x : ℝ ∂volume, x ≠ R := by simp [ae_iff, measure_singleton]
    filter_upwards [hne] with r hr hrI
    rw [uIoc_of_le hR.le] at hrI
    have hlt : r ^ 2 < R ^ 2 :=
      pow_lt_pow_left₀ (lt_of_le_of_ne hrI.2 hr) hrI.1.le (by norm_num)
    rw [abProfile_Bw_eq hN ha hη0 hη hlt]
  have hGr : ∫ r in (0 : ℝ)..R, r ^ (N - 1) * (p.Gw (r ^ 2) * (cE * abA N a (r ^ 2)) ^ 2) =
      ∫ r in (0 : ℝ)..R, r ^ (N - 1) *
        (r ^ 2 * abH1 N a η (r ^ 2) ^ 2 * (cE * abA N a (r ^ 2)) ^ 2) := by
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le hR.le] at hr
    have hle : r ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hr.1 hr.2 2
    simp only
    rw [ABProfile.Gw, p.prof_of_le hle]
    rfl
  have hc := contDiff_abH1 hN ha hη0
  have hcont : Continuous (abH1 N a η) := hc.continuous
  have hAc : Continuous (abA N a) := continuous_iff_continuousAt.mpr fun s =>
    (hasDerivAt_abA hN ha s).continuousAt
  have hBc := continuous_abBs hN ha hη0
  have c1 : Continuous fun r : ℝ =>
      r ^ (N - 1) * (abBs N a η (r ^ 2) * (cE * abA N a (r ^ 2)) ^ 2) := by fun_prop
  have c2 : Continuous fun r : ℝ =>
      r ^ (N - 1) * (r ^ 2 * abH1 N a η (r ^ 2) ^ 2 * (cE * abA N a (r ^ 2)) ^ 2) := by fun_prop
  have hcore := ab_radial_zero hN ha hη0 hη
  have key : ∫ r in (0 : ℝ)..R,
      (r ^ (N - 1) * (abBs N a η (r ^ 2) * (cE * abA N a (r ^ 2)) ^ 2) -
        (CN N - 1) * a *
          (r ^ (N - 1) * (r ^ 2 * abH1 N a η (r ^ 2) ^ 2 * (cE * abA N a (r ^ 2)) ^ 2))) = 0 := by
    have e : (fun r : ℝ =>
        r ^ (N - 1) * (abBs N a η (r ^ 2) * (cE * abA N a (r ^ 2)) ^ 2) -
          (CN N - 1) * a *
            (r ^ (N - 1) * (r ^ 2 * abH1 N a η (r ^ 2) ^ 2 * (cE * abA N a (r ^ 2)) ^ 2))) =
        fun r => cE ^ 2 * (r ^ (N - 1) * abA N a (r ^ 2) ^ 2 *
          (abBs N a η (r ^ 2) - (CN N - 1) * a * r ^ 2 * abH1 N a η (r ^ 2) ^ 2)) := by
      funext r; ring
    rw [e, intervalIntegral.integral_const_mul, hcore, mul_zero]
  rw [intervalIntegral.integral_sub (c1.intervalIntegrable _ _)
    ((c2.intervalIntegrable _ _).const_mul _), intervalIntegral.integral_const_mul] at key
  rw [hBr, hGr]
  linear_combination ((N : ℝ) * volume.real (ball (0 : RN N) 1)) * key

/-- **The Ashbaugh–Benguria profile** (from the Bessel function lemmas `ABBesselLemmas`): there is a
profile at eigenvalue `a` with `G` nondecreasing, `B` nonincreasing, and the gap identity of the
ball. -/
theorem ab_profile_of (hN : 2 ≤ N) (hAB : ABBesselLemmas ((N : ℝ) / 2 - 1)) (ha : 0 < a) :
    ∃ p : ABProfile N a, MonotoneOn p.Gw (Ici 0) ∧ AntitoneOn p.Bw (Ici 0) ∧
      ∫ x in ball (0 : RN N) (annR N a), p.Bw (‖x‖ ^ 2) * besselEntire N a x ^ 2 =
        (CN N - 1) * a * ∫ x in ball (0 : RN N) (annR N a),
          p.Gw (‖x‖ ^ 2) * besselEntire N a x ^ 2 := by
  obtain ⟨η, hη0, hη⟩ := exists_eta hN ha
  exact ⟨abProfile hN ha hη0 hη, abProfile_Gw_mono hN hAB ha hη0 hη,
    abProfile_Bw_anti hN hAB ha hη0 hη, abProfile_ball_identity hN ha hη0 hη⟩

/-- `ab_profile_of` with the Bessel function lemmas `ab_bessel`. -/
theorem ab_profile (hN : 2 ≤ N) (ha : 0 < a) :
    ∃ p : ABProfile N a, MonotoneOn p.Gw (Ici 0) ∧ AntitoneOn p.Bw (Ici 0) ∧
      ∫ x in ball (0 : RN N) (annR N a), p.Bw (‖x‖ ^ 2) * besselEntire N a x ^ 2 =
        (CN N - 1) * a * ∫ x in ball (0 : RN N) (annR N a),
          p.Gw (‖x‖ ^ 2) * besselEntire N a x ^ 2 :=
  ab_profile_of hN (ab_bessel (hN_nu hN)) ha

end FourthRatio

end
