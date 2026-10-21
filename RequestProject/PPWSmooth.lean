module

public import RequestProject.PPWProfile

/-!
# PPW: smoothing of the Ashbaugh–Benguria profile, gradients of radial vector fields

`profK k = h₁ + θ_k (h₂ - h₁)` with `θ_k(s) = smoothTransition((k+1)(s - R²))` is a smooth
approximation of the piecewise smooth profile `h`; it converges to `h` together with its
derivative away from `s = R²`, with bounds uniform in `k` on bounded sets.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

variable {N : ℕ}

/-- The smooth step `θ_k(s) = smoothTransition((k+1)(s - R2))`. -/
def stK (R2 : ℝ) (k : ℕ) (s : ℝ) : ℝ := Real.smoothTransition (((k : ℝ) + 1) * (s - R2))

/-- Its derivative. -/
def dstK (R2 : ℝ) (k : ℕ) (s : ℝ) : ℝ :=
  ((k : ℝ) + 1) * deriv Real.smoothTransition (((k : ℝ) + 1) * (s - R2))

lemma hasDerivAt_stK (R2 : ℝ) (k : ℕ) (s : ℝ) : HasDerivAt (stK R2 k) (dstK R2 k s) s := by
  have h1 : HasDerivAt (fun s : ℝ => ((k : ℝ) + 1) * (s - R2)) ((k : ℝ) + 1) s := by
    simpa using ((hasDerivAt_id s).sub_const R2).const_mul ((k : ℝ) + 1)
  have h2 := ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero
    (((k : ℝ) + 1) * (s - R2))).hasDerivAt
  have := h2.comp s h1
  rw [mul_comm] at this
  exact this

lemma contDiff_stK (R2 : ℝ) (k : ℕ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (stK R2 k) :=
  Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_id.sub contDiff_const))

lemma stK_of_le {R2 : ℝ} (k : ℕ) {s : ℝ} (hs : s ≤ R2) : stK R2 k s = 0 :=
  Real.smoothTransition.zero_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (by positivity)
    (by linarith))

lemma dstK_of_le {R2 : ℝ} (k : ℕ) {s : ℝ} (hs : s ≤ R2) : dstK R2 k s = 0 := by
  rw [dstK, deriv_smoothTransition_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (by positivity)
    (by linarith)), mul_zero]

lemma stK_eventually {R2 s : ℝ} (hs : R2 < s) :
    ∀ᶠ k : ℕ in atTop, stK R2 k s = 1 ∧ dstK R2 k s = 0 := by
  obtain ⟨n, hn⟩ := exists_nat_ge (1 / (s - R2))
  filter_upwards [eventually_ge_atTop n] with k hk
  have hpos : 0 < s - R2 := by linarith
  have h1 : 1 ≤ ((k : ℝ) + 1) * (s - R2) := by
    have : (1 / (s - R2)) ≤ (k : ℝ) + 1 := hn.trans (by exact_mod_cast Nat.le_succ_of_le hk)
    rw [div_le_iff₀ hpos] at this; linarith
  exact ⟨Real.smoothTransition.one_of_one_le h1, by
    rw [dstK, deriv_smoothTransition_of_one_le h1, mul_zero]⟩

lemma stK_mem (R2 : ℝ) (k : ℕ) (s : ℝ) : 0 ≤ stK R2 k s ∧ stK R2 k s ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

/-- A uniform bound for the derivative of the smooth step. -/
lemma exists_bound_deriv_smoothTransition :
    ∃ C, 0 ≤ C ∧ ∀ y, |deriv Real.smoothTransition y| ≤ C := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun y => ?_⟩
  by_cases h0 : y ≤ 0
  · rw [deriv_smoothTransition_of_nonpos h0, abs_zero]; exact le_max_right _ _
  by_cases h1 : 1 ≤ y
  · rw [deriv_smoothTransition_of_one_le h1, abs_zero]; exact le_max_right _ _
  push_neg at h0 h1
  exact (hC y ⟨h0.le, h1.le⟩).trans (le_max_left _ _)

/-- The derivative of the smooth step vanishes unless `0 < (k+1)(s - R2) < 1`. -/
lemma dstK_eq_zero_of {R2 : ℝ} (k : ℕ) {s : ℝ}
    (h : ((k : ℝ) + 1) * (s - R2) ≤ 0 ∨ 1 ≤ ((k : ℝ) + 1) * (s - R2)) : dstK R2 k s = 0 := by
  rcases h with h | h
  · rw [dstK, deriv_smoothTransition_of_nonpos h, mul_zero]
  · rw [dstK, deriv_smoothTransition_of_one_le h, mul_zero]

namespace ABProfile

variable {a : ℝ} (p : ABProfile N a)

/-- The smoothed profile. -/
def profK (k : ℕ) (s : ℝ) : ℝ := p.h1 s + stK (annR N a ^ 2) k s * (p.h2 s - p.h1 s)

/-- Its derivative. -/
def dprofK (k : ℕ) (s : ℝ) : ℝ :=
  deriv p.h1 s + dstK (annR N a ^ 2) k s * (p.h2 s - p.h1 s) +
    stK (annR N a ^ 2) k s * (deriv p.h2 s - deriv p.h1 s)

lemma hasDerivAt_h1 (s : ℝ) : HasDerivAt p.h1 (deriv p.h1 s) s :=
  ((p.h1_smooth.differentiable (by simp)) s).hasDerivAt

lemma hasDerivAt_h2 (s : ℝ) : HasDerivAt p.h2 (deriv p.h2 s) s :=
  ((p.h2_smooth.differentiable (by simp)) s).hasDerivAt

lemma hasDerivAt_profK (k : ℕ) (s : ℝ) : HasDerivAt (p.profK k) (p.dprofK k s) s := by
  have := (p.hasDerivAt_h1 s).add
    ((hasDerivAt_stK (annR N a ^ 2) k s).mul ((p.hasDerivAt_h2 s).sub (p.hasDerivAt_h1 s)))
  convert this using 1 <;> (try rfl) <;> (try (funext t; rfl)) <;>
    (dsimp only [dprofK, Pi.sub_apply]; ring)

lemma contDiff_profK (k : ℕ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (p.profK k) :=
  p.h1_smooth.add ((contDiff_stK _ k).mul (p.h2_smooth.sub p.h1_smooth))

lemma tendsto_profK {s : ℝ} (hs : s ≠ annR N a ^ 2) :
    Tendsto (fun k => p.profK k s) atTop (𝓝 (p.prof s)) ∧
      Tendsto (fun k => p.dprofK k s) atTop (𝓝 (p.dprof s)) := by
  rcases lt_or_gt_of_ne hs with h | h
  · have e1 : ∀ k, p.profK k s = p.prof s := fun k => by
      rw [profK, stK_of_le k h.le, zero_mul, add_zero, p.prof_of_le h.le]
    have e2 : ∀ k, p.dprofK k s = p.dprof s := fun k => by
      rw [dprofK, stK_of_le k h.le, dstK_of_le k h.le, zero_mul, zero_mul, add_zero, add_zero,
        dprof, if_pos h]
    simp only [e1, e2]
    exact ⟨tendsto_const_nhds, tendsto_const_nhds⟩
  · have hev := stK_eventually (R2 := annR N a ^ 2) h
    constructor
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev] with k hk
      rw [profK, hk.1, p.prof_of_lt h]; ring
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev] with k hk
      rw [dprofK, hk.1, hk.2, dprof, if_neg (not_lt.mpr h.le)]; ring

/-- Uniform bounds for the smoothed profile on `[0, S]`. -/
lemma exists_bound_profK (S : ℝ) :
    ∃ C, ∀ k s, 0 ≤ s → s ≤ S → |p.profK k s| ≤ C ∧ |p.dprofK k s| ≤ C := by
  set R2 := annR N a ^ 2 with hR2
  set d : ℝ → ℝ := fun s => p.h2 s - p.h1 s with hd
  have hdc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d := p.h2_smooth.sub p.h1_smooth
  have hdd : ∀ s, HasDerivAt d (deriv p.h2 s - deriv p.h1 s) s := fun s =>
    (p.hasDerivAt_h2 s).sub (p.hasDerivAt_h1 s)
  have hdc' : Continuous fun s => deriv p.h2 s - deriv p.h1 s :=
    (p.h2_smooth.continuous_deriv (by simp)).sub (p.h1_smooth.continuous_deriv (by simp))
  set T := max S (R2 + 1)
  obtain ⟨A1, hA1⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) T)).exists_bound_of_continuousOn
    p.h1_smooth.continuous.continuousOn
  obtain ⟨A2, hA2⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) T)).exists_bound_of_continuousOn
    hdc.continuous.continuousOn
  obtain ⟨A3, hA3⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) T)).exists_bound_of_continuousOn
    (p.h1_smooth.continuous_deriv (by simp)).continuousOn
  obtain ⟨A4, hA4⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) T)).exists_bound_of_continuousOn
    hdc'.continuousOn
  obtain ⟨Cd, hCd0, hCd⟩ := exists_bound_deriv_smoothTransition
  have hR20 : 0 ≤ R2 := sq_nonneg _
  refine ⟨A1 + A2 + A3 + Cd * A4 + A4, fun k s hs0 hsS => ?_⟩
  have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs0, hsS.trans (le_max_left _ _)⟩
  have b1 := hA1 s hsT
  have b2 := hA2 s hsT
  have b3 := hA3 s hsT
  have b4 := hA4 s hsT
  simp only [Real.norm_eq_abs] at b1 b2 b3 b4
  have hA40 : 0 ≤ A4 := (abs_nonneg _).trans b4
  have hA20 : 0 ≤ A2 := (abs_nonneg _).trans b2
  have hA30 : 0 ≤ A3 := (abs_nonneg _).trans b3
  obtain ⟨st0, st1⟩ := stK_mem R2 k s
  -- the middle term
  have hmid : |dstK R2 k s * d s| ≤ Cd * A4 := by
    by_cases hz : ((k : ℝ) + 1) * (s - R2) ≤ 0 ∨ 1 ≤ ((k : ℝ) + 1) * (s - R2)
    · rw [dstK_eq_zero_of k hz, zero_mul, abs_zero]; positivity
    push_neg at hz
    obtain ⟨hz1, hz2⟩ := hz
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hsR : R2 < s := by
      by_contra h; push_neg at h; nlinarith
    have hsR1 : s - R2 ≤ 1 := by
      have : ((k : ℝ) + 1) * (s - R2) ≥ 1 * (s - R2) := by
        apply mul_le_mul_of_nonneg_right _ (by linarith); linarith
      linarith
    -- mean value bound for `d` on `[R2, s]`
    have hmv : ‖d s - d R2‖ ≤ A4 * (s - R2) := by
      refine norm_image_sub_le_of_norm_deriv_le_segment'
        (f' := fun s => deriv p.h2 s - deriv p.h1 s)
        (fun y _ => (hdd y).hasDerivWithinAt) (fun y hy => ?_) s ⟨hsR.le, le_rfl⟩
      have : y ∈ Icc (0 : ℝ) T := ⟨hR20.trans hy.1, hy.2.le.trans (by
        have := le_max_right S (R2 + 1); linarith)⟩
      exact hA4 y this
    have hdR : d R2 = 0 := by simp only [d]; rw [p.matching]; ring
    rw [hdR, sub_zero, Real.norm_eq_abs] at hmv
    rw [dstK, abs_mul, abs_mul, abs_of_pos hk]
    calc ((k : ℝ) + 1) * |deriv Real.smoothTransition (((k : ℝ) + 1) * (s - R2))| * |d s|
        ≤ ((k : ℝ) + 1) * Cd * (A4 * (s - R2)) := by
          gcongr
          exact hCd _
      _ = Cd * A4 * (((k : ℝ) + 1) * (s - R2)) := by ring
      _ ≤ Cd * A4 * 1 := by gcongr
      _ = Cd * A4 := mul_one _
  constructor
  · rw [profK]
    calc |p.h1 s + stK R2 k s * (p.h2 s - p.h1 s)| ≤ |p.h1 s| + |stK R2 k s| * |d s| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ A1 + 1 * A2 := by
          gcongr
          · rw [abs_of_nonneg st0]; exact st1
      _ ≤ A1 + A2 + A3 + Cd * A4 + A4 := by nlinarith [mul_nonneg hCd0 hA40]
  · rw [dprofK]
    calc |deriv p.h1 s + dstK R2 k s * (p.h2 s - p.h1 s) +
          stK R2 k s * (deriv p.h2 s - deriv p.h1 s)|
        ≤ |deriv p.h1 s| + |dstK R2 k s * d s| + |stK R2 k s| * |deriv p.h2 s - deriv p.h1 s| := by
          rw [← abs_mul]
          exact (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
      _ ≤ A3 + Cd * A4 + 1 * A4 := by
          gcongr
          rw [abs_of_nonneg st0]; exact st1
      _ ≤ A1 + A2 + A3 + Cd * A4 + A4 := by
          have : 0 ≤ A1 := (abs_nonneg _).trans b1
          linarith

end ABProfile

/-- Gradient of the radial-times-linear function `x ↦ q(|x - c|²) ⟨x - c, e⟩`. -/
lemma gradient_radial_inner {q q' : ℝ → ℝ} (hq : ∀ s, HasDerivAt q (q' s) s) (c e x : RN N) :
    gradient (fun y => q (‖y - c‖ ^ 2) * ⟪y - c, e⟫) x =
      (q' (‖x - c‖ ^ 2) * 2 * ⟪x - c, e⟫) • (x - c) + q (‖x - c‖ ^ 2) • e := by
  have h0 : HasFDerivAt (fun y : RN N => y - c) (ContinuousLinearMap.id ℝ (RN N)) x :=
    (hasFDerivAt_id x).sub_const c
  have h1 := h0.norm_sq
  have h2 := (hq _).comp_hasFDerivAt x h1
  have h3 : HasFDerivAt (fun y : RN N => ⟪y - c, e⟫) ((innerSL ℝ e).comp
      (ContinuousLinearMap.id ℝ (RN N))) x := by
    have := ((innerSL ℝ e).hasFDerivAt (x := x - c)).comp x h0
    convert this using 1
    funext y; simp [real_inner_comm]
  have h4 := h2.mul h3
  have h5 : HasFDerivAt (fun y : RN N => q (‖y - c‖ ^ 2) * ⟪y - c, e⟫) _ x := h4
  rw [gradient, h5.fderiv]
  apply ext_inner_right ℝ
  intro v
  rw [InnerProductSpace.toDual_symm_apply]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, innerSL_apply_apply,
    inner_add_left, inner_smul_left, smul_eq_mul,
    Function.comp_apply, conj_trivial, nsmul_eq_mul]
  push_cast
  ring

lemma contDiff_radial_inner {q : ℝ → ℝ} (hq : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) q)
    (c e : RN N) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : RN N => q (‖y - c‖ ^ 2) * ⟪y - c, e⟫) :=
  (hq.comp ((contDiff_id.sub contDiff_const).norm_sq ℝ)).mul
    ((contDiff_id.sub contDiff_const).inner ℝ contDiff_const)

end FourthRatio

end
