module

public import RequestProject.PPWABTools

/-!
# Construction of the Ashbaugh–Benguria profile

From the Bessel function lemmas `ab_bessel` we build an `ABProfile N a` whose weights
`G(s) = s h(s)²` and `B(s) = N h² + 4 s h h' + 4 s² h'²` are monotone, and prove the gap identity
of the ball `∫_{B_R} B(|x|²) Φ² = (C_N - 1) a ∫_{B_R} G(|x|²) Φ²` (`ab_profile`).

In the variable `s = |x|²`: `A(s) = F_ν(a s)` is the radial profile of `Φ = besselEntire N a`
(up to a positive constant) and `Q(s) = F_{ν+1}(C_N a s)` the radial factor of the degree-one
eigenfunctions of the ball `B_R`, `R = annR N a`.  Both vanish at `s = R²`; the inner piece of the
profile is `h₁ = Q / A`, extended analytically through `s = R²` by dividing out the common simple
zero.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology

noncomputable section

namespace FourthRatio

variable {N : ℕ}

/-- `A(s) = F_ν(a s)`. -/
def abA (N : ℕ) (a s : ℝ) : ℝ := besselSeries ((N : ℝ) / 2 - 1) a s

/-- `Q(s) = F_{ν+1}(C_N a s)`. -/
def abQ (N : ℕ) (a s : ℝ) : ℝ := besselSeries ((N : ℝ) / 2) (CN N * a) s

section basic

variable {a : ℝ}

lemma a_mul_annR_sq (ha : 0 < a) : a * annR N a ^ 2 = besselZero ((N : ℝ) / 2 - 1) 1 ^ 2 := by
  rw [annR, div_pow, Real.sq_sqrt ha.le]; field_simp

lemma CN_mul_nonneg (hN : 2 ≤ N) (ha : 0 < a) : 0 ≤ CN N * a :=
  mul_nonneg (zero_le_one.trans (CN_gt_one hN).le) ha.le

lemma CN_mul_pos (hN : 2 ≤ N) (ha : 0 < a) : 0 < CN N * a :=
  mul_pos (zero_lt_one.trans (CN_gt_one hN)) ha

lemma CN_mul_annR_sq (hN : 2 ≤ N) (ha : 0 < a) :
    CN N * a * annR N a ^ 2 = besselZero ((N : ℝ) / 2) 1 ^ 2 := by
  rw [← sqrt_CN_mul_annR hN ha, mul_pow, Real.sq_sqrt (CN_mul_nonneg hN ha)]

lemma abA_eq_besselF (ha : 0 < a) {s : ℝ} (hs : 0 ≤ s) :
    abA N a s = besselF ((N : ℝ) / 2 - 1) (Real.sqrt (a * s)) := by
  rw [abA, besselSeries_scale, besselF, Real.sq_sqrt (mul_nonneg ha.le hs)]

lemma abQ_eq_besselF (hN : 2 ≤ N) (ha : 0 < a) {s : ℝ} (hs : 0 ≤ s) :
    abQ N a s = besselF ((N : ℝ) / 2) (Real.sqrt (CN N * a * s)) := by
  rw [abQ, besselSeries_scale, besselF, Real.sq_sqrt (mul_nonneg (CN_mul_nonneg hN ha) hs)]

lemma abA_pos (hN : 2 ≤ N) (ha : 0 < a) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < annR N a ^ 2) :
    0 < abA N a s := by
  have hα := (besselZero_props (hN_nu hN)).1
  rw [abA_eq_besselF ha hs0]
  refine besselF_pos_before (hN_nu hN) (Real.sqrt_nonneg _) ?_
  rw [Real.sqrt_lt' hα, ← a_mul_annR_sq ha]
  exact mul_lt_mul_of_pos_left hs ha

lemma abQ_pos (hN : 2 ≤ N) (ha : 0 < a) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < annR N a ^ 2) :
    0 < abQ N a s := by
  have hν : (0 : ℝ) ≤ (N : ℝ) / 2 := by positivity
  have hβ := (besselZero_props hν).1
  rw [abQ_eq_besselF hN ha hs0]
  refine besselF_pos_before hν (Real.sqrt_nonneg _) ?_
  rw [Real.sqrt_lt' hβ, ← CN_mul_annR_sq hN ha]
  exact mul_lt_mul_of_pos_left hs (CN_mul_pos hN ha)

lemma abA_R (hN : 2 ≤ N) (ha : 0 < a) : abA N a (annR N a ^ 2) = 0 := by
  have h := besselZero_props (hN_nu hN)
  rw [abA_eq_besselF ha (sq_nonneg _), a_mul_annR_sq ha, Real.sqrt_sq h.1.le]
  exact h.2.2.1

lemma abQ_R (hN : 2 ≤ N) (ha : 0 < a) : abQ N a (annR N a ^ 2) = 0 := by
  have hν : (0 : ℝ) ≤ (N : ℝ) / 2 := by positivity
  have h := besselZero_props hν
  rw [abQ_eq_besselF hN ha (sq_nonneg _), CN_mul_annR_sq hN ha, Real.sqrt_sq h.1.le]
  exact h.2.2.1

lemma hasDerivAt_abA (hN : 2 ≤ N) (ha : 0 < a) (s : ℝ) :
    HasDerivAt (abA N a) (besselSeriesD ((N : ℝ) / 2 - 1) a s) s :=
  hasDerivAt_besselSeries (hN_nu hN) ha.le s

lemma hasDerivAt_abQ (hN : 2 ≤ N) (ha : 0 < a) (s : ℝ) :
    HasDerivAt (abQ N a) (besselSeriesD ((N : ℝ) / 2) (CN N * a) s) s :=
  hasDerivAt_besselSeries (by positivity) (CN_mul_nonneg hN ha) s

lemma analytic_abA (hN : 2 ≤ N) (ha : 0 < a) : AnalyticOnNhd ℝ (abA N a) univ :=
  fun s _ => analyticAt_besselSeries (hN_nu hN) ha.le s

lemma analytic_abQ (hN : 2 ≤ N) (ha : 0 < a) : AnalyticOnNhd ℝ (abQ N a) univ :=
  fun s _ => analyticAt_besselSeries (by positivity) (CN_mul_nonneg hN ha) s

lemma abA_D_neg (hN : 2 ≤ N) (ha : 0 < a) :
    besselSeriesD ((N : ℝ) / 2 - 1) a (annR N a ^ 2) < 0 :=
  besselSeriesD_neg (hN_nu hN) ha (pow_pos (annR_pos hN ha) 2)
    (fun s hs => abA_pos hN ha hs.1.le hs.2)

lemma abQ_D_neg (hN : 2 ≤ N) (ha : 0 < a) :
    besselSeriesD ((N : ℝ) / 2) (CN N * a) (annR N a ^ 2) < 0 :=
  besselSeriesD_neg (by positivity) (CN_mul_pos hN ha) (pow_pos (annR_pos hN ha) 2)
    (fun s hs => abQ_pos hN ha hs.1.le hs.2)

/-- `Ã = dslope A R²`, so that `A(s) = (s - R²) Ã(s)`. -/
def abAt (N : ℕ) (a : ℝ) : ℝ → ℝ := dslope (abA N a) (annR N a ^ 2)

/-- `Q̃ = dslope Q R²`. -/
def abQt (N : ℕ) (a : ℝ) : ℝ → ℝ := dslope (abQ N a) (annR N a ^ 2)

lemma abA_eq_mul (hN : 2 ≤ N) (ha : 0 < a) (s : ℝ) :
    abA N a s = (s - annR N a ^ 2) * abAt N a s := by
  have := sub_smul_dslope (abA N a) (annR N a ^ 2) s
  rw [abA_R hN ha, sub_zero, smul_eq_mul] at this
  rw [abAt, this]

lemma abQ_eq_mul (hN : 2 ≤ N) (ha : 0 < a) (s : ℝ) :
    abQ N a s = (s - annR N a ^ 2) * abQt N a s := by
  have := sub_smul_dslope (abQ N a) (annR N a ^ 2) s
  rw [abQ_R hN ha, sub_zero, smul_eq_mul] at this
  rw [abQt, this]

lemma abAt_R (hN : 2 ≤ N) (ha : 0 < a) :
    abAt N a (annR N a ^ 2) = besselSeriesD ((N : ℝ) / 2 - 1) a (annR N a ^ 2) := by
  rw [abAt, dslope_same, (hasDerivAt_abA hN ha _).deriv]

lemma abQt_R (hN : 2 ≤ N) (ha : 0 < a) :
    abQt N a (annR N a ^ 2) = besselSeriesD ((N : ℝ) / 2) (CN N * a) (annR N a ^ 2) := by
  rw [abQt, dslope_same, (hasDerivAt_abQ hN ha _).deriv]

lemma contDiff_abAt (hN : 2 ≤ N) (ha : 0 < a) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (abAt N a) :=
  contDiff_dslope (analytic_abA hN ha) _

lemma contDiff_abQt (hN : 2 ≤ N) (ha : 0 < a) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (abQt N a) :=
  contDiff_dslope (analytic_abQ hN ha) _

lemma abAt_neg (hN : 2 ≤ N) (ha : 0 < a) {s : ℝ} (hs : s ∈ Icc 0 (annR N a ^ 2)) :
    abAt N a s < 0 := by
  rcases hs.2.lt_or_eq with h | h
  · have e := abA_eq_mul hN ha s
    have hp := abA_pos hN ha hs.1 h
    rw [e] at hp
    have : s - annR N a ^ 2 < 0 := by linarith
    by_contra hc; push_neg at hc
    nlinarith
  · rw [h, abAt_R hN ha]; exact abA_D_neg hN ha

lemma exists_eta (hN : 2 ≤ N) (ha : 0 < a) :
    ∃ η, 0 < η ∧ ∀ s ∈ Icc 0 (annR N a ^ 2), abAt N a s ≤ -η := by
  obtain ⟨s0, hs0, hmax⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) (annR N a ^ 2))).exists_isMaxOn
    (nonempty_Icc.mpr (sq_nonneg _)) (contDiff_abAt hN ha).continuous.continuousOn
  refine ⟨-abAt N a s0, by linarith [abAt_neg hN ha hs0], fun s hs => ?_⟩
  have := hmax hs
  simp only [mem_setOf_eq] at this
  linarith

end basic

/-- The inner piece `h₁ = Q̃ / Ã` (with the denominator modified away from `[0, R²]` so that it
never vanishes). -/
def abH1 (N : ℕ) (a η s : ℝ) : ℝ := abQt N a s / -(smoothFloor η (-abAt N a s))

/-- The outer piece `h₂(s) = κ/√s` (modified on `s < R²` so as to be smooth). -/
def abH2 (N : ℕ) (a κ s : ℝ) : ℝ := κ / Real.sqrt (smoothFloor (annR N a ^ 2) s)

section profile

variable {a η : ℝ}

lemma contDiff_abH1 (hN : 2 ≤ N) (ha : 0 < a) (hη : 0 < η) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (abH1 N a η) := by
  refine (contDiff_abQt hN ha).div ((contDiff_smoothFloor η).comp (contDiff_abAt hN ha).neg).neg
    fun s => ?_
  have := smoothFloor_pos hη (-abAt N a s)
  show -(smoothFloor η (-abAt N a s)) ≠ 0
  linarith

lemma abH1_eq_tilde (hη : ∀ s ∈ Icc 0 (annR N a ^ 2), abAt N a s ≤ -η) (hη0 : 0 < η) {s : ℝ}
    (hs : s ∈ Icc 0 (annR N a ^ 2)) : abH1 N a η s = abQt N a s / abAt N a s := by
  rw [abH1, smoothFloor_of_le hη0 (by linarith [hη s hs]), neg_neg]

lemma abH1_eq_div (hN : 2 ≤ N) (ha : 0 < a)
    (hη : ∀ s ∈ Icc 0 (annR N a ^ 2), abAt N a s ≤ -η) (hη0 : 0 < η) {s : ℝ} (hs0 : 0 ≤ s)
    (hs : s < annR N a ^ 2) : abH1 N a η s = abQ N a s / abA N a s := by
  rw [abH1_eq_tilde hη hη0 ⟨hs0, hs.le⟩, abQ_eq_mul hN ha, abA_eq_mul hN ha,
    mul_div_mul_left _ _ (sub_ne_zero.mpr hs.ne)]

lemma abH1_R (hN : 2 ≤ N) (ha : 0 < a)
    (hη : ∀ s ∈ Icc 0 (annR N a ^ 2), abAt N a s ≤ -η) (hη0 : 0 < η) :
    abH1 N a η (annR N a ^ 2) = besselSeriesD ((N : ℝ) / 2) (CN N * a) (annR N a ^ 2) /
      besselSeriesD ((N : ℝ) / 2 - 1) a (annR N a ^ 2) := by
  rw [abH1_eq_tilde hη hη0 ⟨sq_nonneg _, le_rfl⟩, abQt_R hN ha, abAt_R hN ha]

lemma abH1_pos (hN : 2 ≤ N) (ha : 0 < a)
    (hη : ∀ s ∈ Icc 0 (annR N a ^ 2), abAt N a s ≤ -η) (hη0 : 0 < η) {s : ℝ} (hs0 : 0 ≤ s)
    (hs : s ≤ annR N a ^ 2) : 0 < abH1 N a η s := by
  rcases hs.lt_or_eq with h | h
  · rw [abH1_eq_div hN ha hη hη0 hs0 h]
    exact div_pos (abQ_pos hN ha hs0 h) (abA_pos hN ha hs0 h)
  · rw [h, abH1_R hN ha hη hη0]
    exact div_pos_of_neg_of_neg (abQ_D_neg hN ha) (abA_D_neg hN ha)

lemma contDiff_abH2 (hN : 2 ≤ N) (ha : 0 < a) (κ : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (abH2 N a κ) := by
  have hR2 : 0 < annR N a ^ 2 := pow_pos (annR_pos hN ha) 2
  exact contDiff_const.div ((contDiff_smoothFloor _).sqrt fun s => (smoothFloor_pos hR2 s).ne')
    fun s => (Real.sqrt_pos.mpr (smoothFloor_pos hR2 s)).ne'

/-- The Ashbaugh–Benguria profile. -/
def abProfile (hN : 2 ≤ N) (ha : 0 < a) (hη0 : 0 < η)
    (hη : ∀ s ∈ Icc 0 (annR N a ^ 2), abAt N a s ≤ -η) : ABProfile N a where
  h1 := abH1 N a η
  h2 := abH2 N a (annR N a * abH1 N a η (annR N a ^ 2))
  κ := annR N a * abH1 N a η (annR N a ^ 2)
  h1_smooth := contDiff_abH1 hN ha hη0
  h2_smooth := contDiff_abH2 hN ha _
  κ_pos := mul_pos (annR_pos hN ha) (abH1_pos hN ha hη hη0 (sq_nonneg _) le_rfl)
  h2_eq := fun s hs => by
    rw [abH2, smoothFloor_of_le (pow_pos (annR_pos hN ha) 2) hs]
  matching := by
    rw [abH2, smoothFloor_of_le (pow_pos (annR_pos hN ha) 2) le_rfl,
      Real.sqrt_sq (annR_pos hN ha).le, mul_div_cancel_left₀ _ (annR_pos hN ha).ne']
  h1_pos := fun s hs0 hs => abH1_pos hN ha hη hη0 hs0 hs

end profile

end FourthRatio

end
