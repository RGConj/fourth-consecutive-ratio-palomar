module

public import RequestProject.PPWProfile

/-!
# PPW: Weinberger's centring argument

For a nonnegative integrable weight `f` with bounded support there is a centre `c` with
`∫ h(|x - c|²) (x - c) f(x) dx = 0`: `c` is a minimum point of the coercive `C¹` function
`c ↦ ∫ Ψ(|x - c|²) f(x) dx`, `Ψ' = h/2`.  (No fixed point theorem is needed.)
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

variable {N : ℕ}

namespace ABProfile

variable {a : ℝ} (p : ABProfile N a)

/-- The potential `Ψ(s) = ∫₀ˢ h`. -/
def pot (s : ℝ) : ℝ := ∫ t in (0 : ℝ)..s, p.prof t

lemma hasDerivAt_pot (s : ℝ) : HasDerivAt p.pot (p.prof s) s :=
  intervalIntegral.integral_hasDerivAt_right (p.continuous_prof.intervalIntegrable _ _)
    (p.continuous_prof.stronglyMeasurableAtFilter _ _) p.continuous_prof.continuousAt

lemma continuous_pot : Continuous p.pot :=
  continuous_iff_continuousAt.2 fun s => (p.hasDerivAt_pot s).continuousAt

lemma pot_mono : MonotoneOn p.pot (Ici 0) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ici 0) p.continuous_pot.continuousOn
    (fun s _ => (p.hasDerivAt_pot s).differentiableAt.differentiableWithinAt) ?_
  intro s hs
  rw [interior_Ici] at hs
  rw [(p.hasDerivAt_pot s).deriv]
  exact (p.prof_pos (le_of_lt hs)).le

lemma pot_nonneg {s : ℝ} (hs : 0 ≤ s) : 0 ≤ p.pot s := by
  have := p.pot_mono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hs) hs
  simpa [pot] using this

lemma pot_lower (hR : 0 < annR N a) {s : ℝ} (hs : annR N a ^ 2 ≤ s) :
    2 * p.κ * (Real.sqrt s - annR N a) ≤ p.pot s := by
  set R := annR N a with hR_def
  have hR2 : 0 < R ^ 2 := by positivity
  have h1 : p.pot s - p.pot (R ^ 2) = ∫ t in R ^ 2..s, p.prof t := by
    simp only [pot]
    exact intervalIntegral.integral_interval_sub_left (p.continuous_prof.intervalIntegrable 0 s)
      (p.continuous_prof.intervalIntegrable 0 (R ^ 2))
  have hpos : ∀ t ∈ uIcc (R ^ 2) s, 0 < t := fun t ht => by
    rw [uIcc_of_le hs] at ht; exact lt_of_lt_of_le hR2 ht.1
  have h2 : ∫ t in R ^ 2..s, p.prof t = ∫ t in R ^ 2..s, p.κ / Real.sqrt t := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hs] at ht
    exact p.prof_tail ht.1
  have h3 : ∫ t in R ^ 2..s, p.κ / Real.sqrt t =
      2 * p.κ * Real.sqrt s - 2 * p.κ * Real.sqrt (R ^ 2) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t => 2 * p.κ * Real.sqrt t) (fun t ht => ?_) ?_
    · have ht0 := hpos t ht
      have := (Real.hasDerivAt_sqrt ht0.ne').const_mul (2 * p.κ)
      convert this using 1
      have : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
      field_simp
    · refine ContinuousOn.intervalIntegrable fun t ht => ?_
      exact (continuousAt_const.div Real.continuous_sqrt.continuousAt
        (Real.sqrt_pos.mpr (hpos t ht)).ne').continuousWithinAt
  rw [Real.sqrt_sq hR.le] at h3
  have := p.pot_nonneg hR2.le
  linarith

end ABProfile

/-- **Weinberger's centring lemma.** -/
theorem exists_center {a : ℝ} (p : ABProfile N a) (hR : 0 < annR N a) {f : RN N → ℝ}
    (hf : Integrable f) (hnn : ∀ x, 0 ≤ f x) {M : ℝ} (hM : ∀ᵐ x, M < ‖x‖ → f x = 0) :
    ∃ c : RN N, ∀ e : RN N, ∫ x, p.prof (‖x - c‖ ^ 2) * ⟪x - c, e⟫ * f x = 0 := by
  set M0 := max M 0 with hM0_def
  have hM00 : 0 ≤ M0 := le_max_right _ _
  have hsupp : ∀ᵐ x, f x = 0 ∨ ‖x‖ ≤ M0 := hM.mono fun x hx => by
    by_cases h : M < ‖x‖
    · exact Or.inl (hx h)
    · exact Or.inr ((not_lt.mp h).trans (le_max_left _ _))
  by_cases hF : ∫ x, f x = 0
  · have hf0 : f =ᵐ[volume] 0 := (integral_eq_zero_iff_of_nonneg hnn hf).mp hF
    refine ⟨0, fun e => integral_eq_zero_of_ae ?_⟩
    filter_upwards [hf0] with x hx
    simp [hx]
  have hFpos : 0 < ∫ x, f x := lt_of_le_of_ne (integral_nonneg hnn) (Ne.symm hF)
  have hcn : ∀ c : RN N, Continuous fun x : RN N => ‖x - c‖ ^ 2 := fun c =>
    (continuous_id.sub continuous_const).norm.pow 2
  -- pointwise bound of the potential on the support
  have hpotb : ∀ (c x : RN N) (L : ℝ), ‖x‖ ≤ M0 → M0 + ‖c‖ ≤ L →
      p.pot (‖x - c‖ ^ 2) ≤ p.pot (L ^ 2) := fun c x L hx hL => by
    refine p.pot_mono (mem_Ici.mpr (sq_nonneg _)) (mem_Ici.mpr (sq_nonneg _)) ?_
    have : ‖x - c‖ ≤ L := (norm_sub_le x c).trans (by linarith)
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  have hint : ∀ c : RN N, Integrable fun x => p.pot (‖x - c‖ ^ 2) * f x := fun c => by
    refine Integrable.mono' (hf.const_mul (p.pot ((M0 + ‖c‖) ^ 2)))
      (((p.continuous_pot.comp (hcn c)).aestronglyMeasurable).mul hf.aestronglyMeasurable) ?_
    filter_upwards [hsupp] with x hx
    rcases hx with hx | hx
    · simp [hx]
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (p.pot_nonneg (sq_nonneg _)),
        abs_of_nonneg (hnn x)]
      exact mul_le_mul_of_nonneg_right (hpotb c x _ hx le_rfl) (hnn x)
  set Φ : RN N → ℝ := fun c => ∫ x, p.pot (‖x - c‖ ^ 2) * f x with hΦ_def
  -- continuity on closed balls
  have hcont : ∀ ρ, ContinuousOn Φ (closedBall 0 ρ) := fun ρ => by
    refine continuousOn_of_dominated (bound := fun x => p.pot ((M0 + ρ) ^ 2) * f x)
      (fun c _ => (hint c).aestronglyMeasurable) (fun c hc => ?_)
      (hf.const_mul _) (Filter.Eventually.of_forall fun x => ?_)
    · have hc' : ‖c‖ ≤ ρ := by simpa using hc
      filter_upwards [hsupp] with x hx
      rcases hx with hx | hx
      · simp [hx]
      · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (p.pot_nonneg (sq_nonneg _)),
          abs_of_nonneg (hnn x)]
        exact mul_le_mul_of_nonneg_right (hpotb c x _ hx (by linarith)) (hnn x)
    · exact ((p.continuous_pot.comp ((continuous_const.sub continuous_id).norm.pow 2)).mul
        continuous_const).continuousOn
  -- coercivity
  set K0 := p.pot (M0 ^ 2) with hK0
  have hK00 : 0 ≤ K0 := p.pot_nonneg (sq_nonneg _)
  set ρ := M0 + annR N a + (K0 + 1) / (2 * p.κ) + 1 with hρ
  have hκ := p.κ_pos
  have hρ0 : 0 < ρ := by positivity
  have hΦ0 : Φ 0 ≤ K0 * ∫ x, f x := by
    rw [← integral_const_mul]
    refine integral_mono_ae (hint 0) (hf.const_mul _) ?_
    filter_upwards [hsupp] with x hx
    rcases hx with hx | hx
    · simp [hx]
    · exact mul_le_mul_of_nonneg_right (hpotb 0 x M0 hx (by simp)) (hnn x)
  have hfar : ∀ c : RN N, ρ ≤ ‖c‖ → (K0 + 1) * ∫ x, f x ≤ Φ c := fun c hc => by
    rw [← integral_const_mul]
    refine integral_mono_ae (hf.const_mul _) (hint c) ?_
    filter_upwards [hsupp] with x hx
    rcases hx with hx | hx
    · simp [hx]
    · refine mul_le_mul_of_nonneg_right ?_ (hnn x)
      have hxc : ρ - M0 ≤ ‖x - c‖ := by
        have := norm_sub_norm_le c x
        rw [norm_sub_rev] at this
        linarith
      have hRx : annR N a ≤ ‖x - c‖ := by
        have : 0 ≤ (K0 + 1) / (2 * p.κ) := by positivity
        linarith
      have hlow := p.pot_lower hR (pow_le_pow_left₀ hR.le hRx 2)
      rw [Real.sqrt_sq (norm_nonneg _)] at hlow
      have h2 : 2 * p.κ * ((K0 + 1) / (2 * p.κ)) = K0 + 1 := by field_simp
      nlinarith
  obtain ⟨c0, hc0, hmin⟩ := (isCompact_closedBall (0 : RN N) ρ).exists_isMinOn
    (nonempty_closedBall.mpr hρ0.le) (hcont ρ)
  have hglob : ∀ c, Φ c0 ≤ Φ c := fun c => by
    by_cases hc : ‖c‖ ≤ ρ
    · exact hmin (by simpa using hc)
    · have h1 := hfar c (le_of_lt (not_le.mp hc))
      have h2 : Φ c0 ≤ Φ 0 := hmin (mem_closedBall_self hρ0.le)
      linarith
  refine ⟨c0, fun e => ?_⟩
  -- the derivative of `t ↦ Φ (c0 + t e)` at `0`
  set L := M0 + ‖c0‖ + ‖e‖ with hL
  obtain ⟨Kp, hKp⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) (L ^ 2))).exists_bound_of_continuousOn
    p.continuous_prof.continuousOn
  set F : ℝ → RN N → ℝ := fun t x => p.pot (‖x - (c0 + t • e)‖ ^ 2) * f x with hF_def
  set F' : ℝ → RN N → ℝ := fun t x =>
    p.prof (‖x - (c0 + t • e)‖ ^ 2) * (2 * ⟪x - (c0 + t • e), -e⟫) * f x with hF'_def
  have hdiff : ∀ x t, HasDerivAt (fun t => F t x) (F' t x) t := fun x t => by
    have h1 : HasDerivAt (fun t : ℝ => x - (c0 + t • e)) (-e) t := by
      have := ((hasDerivAt_id t).smul_const e).const_add c0
      simpa using this.const_sub x
    have h2 := (p.hasDerivAt_pot _).comp t h1.norm_sq
    exact h2.mul_const (f x)
  have hcont' : ∀ t : ℝ, Continuous fun x : RN N => ‖x - (c0 + t • e)‖ ^ 2 := fun t =>
    (continuous_id.sub continuous_const).norm.pow 2
  have hbound : ∀ᵐ x, ∀ t ∈ ball (0 : ℝ) 1, ‖F' t x‖ ≤ Kp * (2 * L * ‖e‖) * f x := by
    filter_upwards [hsupp] with x hx t ht
    rcases hx with hx | hx
    · simp [F', hx]
    have ht' : |t| < 1 := by simpa [mem_ball, dist_zero_right] using ht
    have hn : ‖x - (c0 + t • e)‖ ≤ L := by
      calc ‖x - (c0 + t • e)‖ ≤ ‖x‖ + (‖c0‖ + |t| * ‖e‖) := by
            refine (norm_sub_le _ _).trans (add_le_add le_rfl ((norm_add_le _ _).trans ?_))
            rw [norm_smul, Real.norm_eq_abs]
        _ ≤ L := by nlinarith [norm_nonneg e, abs_nonneg t]
    have hpb : ‖p.prof (‖x - (c0 + t • e)‖ ^ 2)‖ ≤ Kp :=
      hKp _ ⟨sq_nonneg _, pow_le_pow_left₀ (norm_nonneg _) hn 2⟩
    have hib : |(2 : ℝ)| * |⟪x - (c0 + t • e), -e⟫| ≤ 2 * L * ‖e‖ := by
      rw [abs_two]
      have := abs_real_inner_le_norm (x - (c0 + t • e)) (-e)
      rw [norm_neg] at this
      nlinarith [norm_nonneg e]
    simp only [F', norm_mul, Real.norm_eq_abs] at hpb ⊢
    rw [abs_of_nonneg (hnn x)]
    have h0 : 0 ≤ |(2 : ℝ)| * |⟪x - (c0 + t • e), -e⟫| := by positivity
    have hK : 0 ≤ Kp := (abs_nonneg _).trans hpb
    exact mul_le_mul_of_nonneg_right (mul_le_mul hpb hib h0 hK) (hnn x)
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le (x₀ := (0 : ℝ))
    (F := F) (F' := F') (bound := fun x => Kp * (2 * L * ‖e‖) * f x)
    (ball_mem_nhds (0 : ℝ) one_pos)
    (Filter.Eventually.of_forall fun t =>
      ((p.continuous_pot.comp (hcont' t)).aestronglyMeasurable).mul hf.aestronglyMeasurable)
    (by simpa [F] using hint c0)
    ((((p.continuous_prof.comp (hcont' 0)).mul
      (continuous_const.mul ((continuous_id.sub continuous_const).inner continuous_const))
      ).aestronglyMeasurable).mul hf.aestronglyMeasurable)
    hbound (hf.const_mul _) (Filter.Eventually.of_forall fun x t _ => hdiff x t)
  have hlocmin : IsLocalMin (fun t : ℝ => ∫ x, F t x) 0 :=
    Filter.Eventually.of_forall fun t => by
      simp only [F, zero_smul, add_zero]
      exact hglob _
  have h0 := hlocmin.hasDerivAt_eq_zero hderiv.2
  have h1 : (∫ x, F' 0 x) = -2 * ∫ x, p.prof (‖x - c0‖ ^ 2) * ⟪x - c0, e⟫ * f x := by
    rw [← integral_const_mul]
    congr 1; funext x
    simp only [F', zero_smul, add_zero, inner_neg_right]
    ring
  rw [h1] at h0
  linarith

end FourthRatio

end
