module

public import RequestProject.WeylSmooth

/-!
# Analyticity from factorial derivative bounds

`analyticAt_of_iteratedFDeriv_bound`: a function which is smooth on a ball `B(x, ρ)` and whose
iterated derivatives satisfy `‖D^k f(y)‖ ≤ C K^k k!` on that ball is real analytic at `x`
(its Taylor series converges to it, by Taylor's formula with Lagrange remainder along segments).
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Function Set
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

/-- One-dimensional Taylor convergence on `[0, 1]` under factorial derivative bounds. -/
lemma taylor_tendsto_of_bound {φ : ℝ → ℝ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    {C q : ℝ} (hq0 : 0 ≤ q) (hq : q < 1)
    (hb : ∀ k : ℕ, ∀ t ∈ Icc (0 : ℝ) 1, |iteratedDeriv k φ t| ≤ C * q ^ k * k.factorial) :
    Tendsto (fun N => ∑ k ∈ Finset.range (N + 1), iteratedDeriv k φ 0 / k.factorial) atTop
      (𝓝 (φ 1)) := by
  have hU : UniqueDiffOn ℝ (Icc (0 : ℝ) 1) := uniqueDiffOn_Icc zero_lt_one
  have hwithin : ∀ k : ℕ, ∀ t ∈ Icc (0 : ℝ) 1,
      iteratedDerivWithin k φ (Icc 0 1) t = iteratedDeriv k φ t := fun k t ht =>
    iteratedDerivWithin_eq_iteratedDeriv hU (hφ.contDiffAt.of_le
      (WithTop.coe_le_coe.mpr le_top)) ht
  have hrem : ∀ N : ℕ, |φ 1 - ∑ k ∈ Finset.range (N + 1), iteratedDeriv k φ 0 / k.factorial| ≤
      C * q ^ (N + 1) := by
    intro N
    obtain ⟨ξ, hξ, heq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
      (f := φ) (x := 1) (x₀ := 0) (n := N)
      (ne_of_lt zero_lt_one) (hφ.contDiffOn.of_le (WithTop.coe_le_coe.mpr le_top))
    rw [uIoo_of_lt zero_lt_one] at hξ
    rw [uIcc_of_le zero_le_one] at heq
    rw [taylor_within_apply] at heq
    have hsum : ∑ k ∈ Finset.range (N + 1), ((k.factorial : ℝ)⁻¹ * (1 - 0) ^ k) •
        iteratedDerivWithin k φ (Icc 0 1) 0 =
        ∑ k ∈ Finset.range (N + 1), iteratedDeriv k φ 0 / k.factorial := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hwithin k 0 (left_mem_Icc.mpr zero_le_one), smul_eq_mul]
      simp [div_eq_inv_mul]
    rw [hsum] at heq
    rw [heq]
    simp only [sub_zero, one_pow, mul_one, abs_div, Nat.abs_cast]
    rw [div_le_iff₀ (by positivity)]
    exact hb (N + 1) ξ (Ioo_subset_Icc_self hξ)
  have hC : 0 ≤ C := by
    have := hb 0 0 (left_mem_Icc.mpr zero_le_one)
    simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one] at this
    exact le_trans (abs_nonneg _) this
  have hlim : Tendsto (fun N : ℕ => C * q ^ (N + 1)) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq).const_mul C
    rw [mul_zero] at this
    exact this.comp (tendsto_add_atTop_nat 1)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_) hlim
  rw [Real.norm_eq_abs, abs_sub_comm]
  exact hrem N

variable {n : ℕ}

lemma iteratedDeriv_line {F : RN n → ℝ} (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (x y : RN n) (k : ℕ) (t : ℝ) :
    iteratedDeriv k (fun t : ℝ => F (x + t • y)) t = iteratedFDeriv ℝ k F (x + t • y) (fun _ => y) := by
  set L : ℝ →L[ℝ] RN n := ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) y
  have hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => F (x + z)) :=
    hF.comp (contDiff_const.add contDiff_id)
  have e : (fun t : ℝ => F (x + t • y)) = (fun z => F (x + z)) ∘ L := by
    funext t; simp [L]
  rw [iteratedDeriv_eq_iteratedFDeriv, e, L.iteratedFDeriv_comp_right hG t
    (WithTop.coe_le_coe.mpr le_top), iteratedFDeriv_comp_add_left]
  simp [L]

/-- **Analyticity from factorial derivative bounds.** -/
theorem analyticAt_of_iteratedFDeriv_bound {f : RN n → ℝ} {x : RN n} {ρ C K : ℝ} (hρ : 0 < ρ)
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (ball x ρ))
    (hb : ∀ y ∈ ball x ρ, ∀ k : ℕ, ‖iteratedFDeriv ℝ k f y‖ ≤ C * K ^ k * k.factorial) :
    AnalyticAt ℝ f x := by
  set K' := max |K| 1
  have hK' : 1 ≤ K' := le_max_right _ _
  have hC : 0 ≤ C := by
    have := hb x (mem_ball_self hρ) 0
    simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one] at this
    exact le_trans (norm_nonneg _) this
  have hb' : ∀ y ∈ ball x ρ, ∀ k : ℕ, ‖iteratedFDeriv ℝ k f y‖ ≤ C * K' ^ k * k.factorial := by
    intro y hy k
    have hKk : K ^ k ≤ K' ^ k :=
      calc K ^ k ≤ |K| ^ k := by rw [← abs_pow]; exact le_abs_self _
        _ ≤ K' ^ k := pow_le_pow_left₀ (abs_nonneg _) (le_max_left _ _) k
    refine (hb y hy k).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKk hC) (by positivity)
  set δ := min (ρ / 2) (1 / (2 * K'))
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδρ : δ ≤ ρ / 2 := min_le_left _ _
  have hδK : K' * δ ≤ 1 / 2 := by
    have : δ ≤ 1 / (2 * K') := min_le_right _ _
    calc K' * δ ≤ K' * (1 / (2 * K')) := by gcongr
      _ = 1 / 2 := by field_simp
  -- a smooth global extension of `f` near `B̄(x, ρ/2)`
  obtain ⟨F, hF, -, -, V, hVo, hKV, hFV⟩ := exists_smooth_extension isOpen_ball
    (isCompact_closedBall x (ρ / 2)) (closedBall_subset_ball (by linarith)) hf
  have hiter : ∀ z ∈ closedBall x (ρ / 2), ∀ k, iteratedFDeriv ℝ k F z = iteratedFDeriv ℝ k f z := by
    intro z hz k
    have hev : F =ᶠ[𝓝 z] f := by
      filter_upwards [hVo.mem_nhds (hKV hz)] with w hw
      exact hFV w hw
    exact (hev.iteratedFDeriv ℝ k).eq_of_nhds
  set p : FormalMultilinearSeries ℝ (RN n) ℝ := fun k =>
    ((k.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ k f x
  have hp : ∀ k, ‖p k‖ ≤ C * K' ^ k := by
    intro k
    simp only [p, norm_smul, norm_inv, Real.norm_natCast]
    have := hb' x (mem_ball_self hρ) k
    rw [inv_mul_le_iff₀ (by positivity)]
    linarith
  refine ⟨p, ENNReal.ofReal δ, ?_⟩
  refine HasFPowerSeriesOnBall.mk ?_ (by simpa using hδ) fun {y} hy => ?_
  · have h := p.le_radius_of_bound C (r := ⟨δ, hδ.le⟩) fun k => by
      calc ‖p k‖ * (δ : ℝ) ^ k ≤ C * K' ^ k * δ ^ k := by gcongr; exact hp k
        _ = C * (K' * δ) ^ k := by rw [mul_pow]; ring
        _ ≤ C * 1 := by
            gcongr
            exact pow_le_one₀ (by positivity) (by linarith)
        _ = C := mul_one C
    rw [ENNReal.ofReal_eq_coe_nnreal hδ.le]
    exact h
  · have hy' : ‖y‖ < δ := by
      rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm_eq_enorm,
        ENNReal.ofReal_lt_ofReal_iff hδ] at hy
      exact hy
    have hseg : ∀ t ∈ Icc (0 : ℝ) 1, x + t • y ∈ closedBall x (ρ / 2) := by
      intro t ht
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg ht.1]
      nlinarith [norm_nonneg y, ht.2]
    set φ : ℝ → ℝ := fun t => F (x + t • y)
    have hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ :=
      hF.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
    set q := K' * ‖y‖
    have hq0 : 0 ≤ q := by positivity
    have hq1 : q < 1 := by
      calc q ≤ K' * δ := mul_le_mul_of_nonneg_left hy'.le (by linarith)
        _ < 1 := by linarith
    have hbφ : ∀ k : ℕ, ∀ t ∈ Icc (0 : ℝ) 1, |iteratedDeriv k φ t| ≤ C * q ^ k * k.factorial := by
      intro k t ht
      rw [iteratedDeriv_line hF, hiter _ (hseg t ht)]
      have h1 := (iteratedFDeriv ℝ k f (x + t • y)).le_opNorm (fun _ => y)
      have h2 := hb' (x + t • y) (closedBall_subset_ball (by linarith) (hseg t ht)) k
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
      rw [← Real.norm_eq_abs]
      calc ‖iteratedFDeriv ℝ k f (x + t • y) (fun _ => y)‖
          ≤ ‖iteratedFDeriv ℝ k f (x + t • y)‖ * ‖y‖ ^ k := h1
        _ ≤ C * K' ^ k * k.factorial * ‖y‖ ^ k := by gcongr
        _ = C * q ^ k * k.factorial := by simp only [q, mul_pow]; ring
    have hT := taylor_tendsto_of_bound hφ hq0 hq1 hbφ
    have hterm : ∀ k, iteratedDeriv k φ 0 / k.factorial = p k (fun _ => y) := by
      intro k
      rw [iteratedDeriv_line hF, zero_smul, add_zero, hiter x (mem_closedBall_self (by linarith))]
      simp only [p, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
      ring
    simp_rw [hterm] at hT
    have hφ1 : φ 1 = f (x + y) := by
      simp only [φ, one_smul]
      exact hFV _ (hKV (by simpa using hseg 1 ⟨zero_le_one, le_rfl⟩))
    rw [hφ1] at hT
    have hsumm : Summable fun k => p k (fun _ => y) := by
      refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hq0 hq1).mul_left C)
        fun k => ?_
      have h1 := (p k).le_opNorm (fun _ => y)
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
      calc ‖p k (fun _ => y)‖ ≤ ‖p k‖ * ‖y‖ ^ k := h1
        _ ≤ C * K' ^ k * ‖y‖ ^ k := by gcongr; exact hp k
        _ = C * q ^ k := by simp only [q, mul_pow]; ring
    rw [hsumm.hasSum_iff_tendsto_nat]
    exact (Filter.tendsto_add_atTop_iff_nat 1).mp hT

end FourthRatio

end
