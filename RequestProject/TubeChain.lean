module

public import RequestProject.TubeSpectral
public import RequestProject.BallSym

/-!
# Smooth domains shrinking onto a chain of collinear balls

For balls `B_r(sᵢ e₀)` with centres `sᵢ = 4 r i` (`i < m`) on the first coordinate axis we construct
smooth bounded domains `Ωₙ = {x : |x_⊥|² < Fₙ(x₀)}` (solids of revolution around the axis) that
contain the balls, lie in a fixed ball, and shrink onto the closed balls away from the axis.
Combined with `eigenvalue_tendsto_of_shrinking` this gives `λ_j(Ωₙ) → λ_j(⋃ᵢ Bᵢ)`.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Function
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

/-! ### A smooth upper approximation of the positive part -/

/-- `softPos δ u = (u + √(u² + δ²))/2`, a smooth function above `max u 0`. -/
def softPos (δ u : ℝ) : ℝ := (u + Real.sqrt (u ^ 2 + δ ^ 2)) / 2

lemma abs_lt_sqrt_sq_add {δ : ℝ} (hδ : 0 < δ) (u : ℝ) : |u| < Real.sqrt (u ^ 2 + δ ^ 2) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_lt_sqrt (sq_nonneg _) (by nlinarith)

lemma max_le_softPos {δ : ℝ} (hδ : 0 < δ) (u : ℝ) : max u 0 ≤ softPos δ u := by
  have h := abs_lt_sqrt_sq_add hδ u
  unfold softPos
  rcases le_total u 0 with hu | hu
  · rw [max_eq_right hu]; rw [abs_of_nonpos hu] at h; linarith
  · rw [max_eq_left hu]; rw [abs_of_nonneg hu] at h; linarith

lemma softPos_pos {δ : ℝ} (hδ : 0 < δ) (u : ℝ) : 0 < softPos δ u := by
  have h := abs_lt_sqrt_sq_add hδ u
  unfold softPos
  have := neg_abs_le u
  linarith

lemma softPos_le {δ : ℝ} (hδ : 0 ≤ δ) (u : ℝ) : softPos δ u ≤ max u 0 + δ / 2 := by
  have h : Real.sqrt (u ^ 2 + δ ^ 2) ≤ |u| + δ := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [abs_nonneg u, sq_abs u]
  unfold softPos
  rcases le_total u 0 with hu | hu
  · rw [max_eq_right hu]; rw [abs_of_nonpos hu] at h; linarith
  · rw [max_eq_left hu]; rw [abs_of_nonneg hu] at h; linarith

lemma tendsto_softPos (u : ℝ) :
    Tendsto (fun n : ℕ => softPos (1 / ((n : ℝ) + 1)) u) atTop (𝓝 (max u 0)) := by
  have h : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h2 : Tendsto (fun n : ℕ => softPos (1 / ((n : ℝ) + 1)) u) atTop
      (𝓝 ((u + Real.sqrt (u ^ 2 + 0 ^ 2)) / 2)) :=
    (tendsto_const_nhds.add ((Real.continuous_sqrt.tendsto _).comp
      (tendsto_const_nhds.add (h.pow 2)))).div_const 2
  convert h2 using 2
  rw [zero_pow two_ne_zero, add_zero, Real.sqrt_sq_eq_abs]
  rcases le_total u 0 with hu | hu
  · rw [max_eq_right hu, abs_of_nonpos hu]; ring
  · rw [max_eq_left hu, abs_of_nonneg hu]; ring

lemma contDiff_softPos {δ : ℝ} (hδ : 0 < δ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (softPos δ) := by
  unfold softPos
  exact (contDiff_id.add (((contDiff_id.pow 2).add contDiff_const).sqrt fun u => by
    positivity)).div_const 2

/-- The derivative of `softPos δ`. -/
def softPos' (δ u : ℝ) : ℝ := (1 + u / Real.sqrt (u ^ 2 + δ ^ 2)) / 2

lemma hasDerivAt_softPos {δ : ℝ} (hδ : 0 < δ) (u : ℝ) :
    HasDerivAt (softPos δ) (softPos' δ u) u := by
  have hpos : u ^ 2 + δ ^ 2 ≠ 0 := by positivity
  have h1 : HasDerivAt (fun u : ℝ => u ^ 2 + δ ^ 2) (2 * u) u := by
    simpa using (hasDerivAt_pow 2 u).add_const (δ ^ 2)
  have h2 := ((hasDerivAt_id u).add (h1.sqrt hpos)).div_const 2
  unfold softPos softPos'
  convert h2 using 1
  · rfl
  · field_simp [Real.sqrt_ne_zero'.mpr (by positivity : 0 < u ^ 2 + δ ^ 2)]

lemma softPos'_pos {δ : ℝ} (hδ : 0 < δ) (u : ℝ) : 0 < softPos' δ u := by
  have h := abs_lt_sqrt_sq_add hδ u
  have hs : 0 < Real.sqrt (u ^ 2 + δ ^ 2) := (abs_nonneg u).trans_lt h
  unfold softPos'
  have : -1 < u / Real.sqrt (u ^ 2 + δ ^ 2) := by
    rw [lt_div_iff₀ hs]
    have := neg_abs_le u
    linarith
  linarith

section Profile

variable (m : ℕ) (r : ℝ)

/-- Centres `sᵢ = 4 r i` on the axis. -/
def chainS (i : ℕ) : ℝ := 4 * r * i

/-- The ball profile `r² - (t - sᵢ)²`. -/
def chainU (i : ℕ) (t : ℝ) : ℝ := r ^ 2 - (t - chainS r i) ^ 2

/-- Midpoint of the chain. -/
def chainMid : ℝ := 2 * r * ((m : ℝ) - 1)

/-- Half-length of the chain. -/
def chainR : ℝ := 2 * r * ((m : ℝ) - 1) + r

/-- Smoothed upper envelope of the ball profiles. -/
def chainG (δ t : ℝ) : ℝ := ∑ i ∈ Finset.range m, softPos δ (chainU r i t)

/-- Size of the outer cut-off. -/
def chainL : ℝ := 3 * m * (r ^ 2 + 1)

/-- Outer cut-off, vanishing on the chain interval. -/
def chainK (t : ℝ) : ℝ := chainL m r * expNegInvGlue ((t - chainMid m r) ^ 2 - chainR m r ^ 2)

/-- The radius-squared profile of the approximating domains. -/
def chainF (δ t : ℝ) : ℝ := chainG m r δ t - chainK m r t

/-- The derivative of the profile. -/
def chainF' (δ t : ℝ) : ℝ :=
  (∑ i ∈ Finset.range m, softPos' δ (chainU r i t) * (-2 * (t - chainS r i))) -
    chainL m r * deriv expNegInvGlue ((t - chainMid m r) ^ 2 - chainR m r ^ 2) *
      (2 * (t - chainMid m r))

variable {m r}

lemma chainR_nonneg (hm : 1 ≤ m) (hr : 0 < r) : 0 ≤ chainR m r := by
  have : (1 : ℝ) ≤ m := by exact_mod_cast hm
  unfold chainR; nlinarith

lemma chainK_eq_zero {t : ℝ} (ht : (t - chainMid m r) ^ 2 ≤ chainR m r ^ 2) : chainK m r t = 0 := by
  unfold chainK; rw [expNegInvGlue.zero_of_nonpos (by linarith), mul_zero]

lemma chainL_nonneg : 0 ≤ chainL m r := by unfold chainL; positivity

lemma chainK_nonneg (t : ℝ) : 0 ≤ chainK m r t :=
  mul_nonneg chainL_nonneg (expNegInvGlue.nonneg _)

lemma chainG_pos (hm : 1 ≤ m) {δ : ℝ} (hδ : 0 < δ) (t : ℝ) : 0 < chainG m r δ t :=
  Finset.sum_pos (fun _ _ => softPos_pos hδ _) ⟨0, Finset.mem_range.mpr hm⟩

lemma chainG_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (t : ℝ) :
    chainG m r δ t ≤ m * (r ^ 2 + 1 / 2) := by
  unfold chainG
  calc _ ≤ ∑ _i ∈ Finset.range m, (r ^ 2 + 1 / 2) := Finset.sum_le_sum fun i _ => by
        refine (softPos_le hδ.le _).trans ?_
        have : max (chainU r i t) 0 ≤ r ^ 2 := max_le (by unfold chainU; nlinarith) (sq_nonneg _)
        linarith
    _ = _ := by simp; ring

lemma chainF_neg (hm : 1 ≤ m) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {t : ℝ}
    (ht : 1 ≤ (t - chainMid m r) ^ 2 - chainR m r ^ 2) : chainF m r δ t < 0 := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hψ : expNegInvGlue 1 ≤ expNegInvGlue ((t - chainMid m r) ^ 2 - chainR m r ^ 2) :=
    expNegInvGlue.monotone ht
  have h1 : expNegInvGlue 1 = Real.exp (-1) := by simp [expNegInvGlue]
  have he : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
  have he' : 1 / 3 < Real.exp (-1) := by
    rw [Real.exp_neg, one_div]
    exact inv_strictAnti₀ (Real.exp_pos 1) he
  have hG := chainG_le (m := m) (r := r) hδ hδ1 t
  have hL : chainL m r * (1 / 3) ≤ chainK m r t := by
    unfold chainK
    exact mul_le_mul_of_nonneg_left (by linarith) chainL_nonneg
  unfold chainF
  unfold chainL at hL
  have : (m : ℝ) * (r ^ 2 + 1 / 2) < 3 * m * (r ^ 2 + 1) * (1 / 3) := by nlinarith [sq_nonneg r]
  linarith

lemma hasDerivAt_chainF {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    HasDerivAt (chainF m r δ) (chainF' m r δ t) t := by
  have hU : ∀ i, HasDerivAt (chainU r i) (-2 * (t - chainS r i)) t := fun i => by
    have := ((hasDerivAt_id t).sub_const (chainS r i)).pow 2
    have := this.const_sub (r ^ 2)
    convert this using 1 <;> (try rfl) <;> simp [chainU] <;> ring
  have hG : HasDerivAt (chainG m r δ)
      (∑ i ∈ Finset.range m, softPos' δ (chainU r i t) * (-2 * (t - chainS r i))) t := by
    have := HasDerivAt.fun_sum (u := Finset.range m)
      (fun i _ => (hasDerivAt_softPos hδ (chainU r i t)).comp t (hU i))
    convert this using 1 <;> rfl
  have hq : HasDerivAt (fun t => (t - chainMid m r) ^ 2 - chainR m r ^ 2)
      (2 * (t - chainMid m r)) t := by
    have := (((hasDerivAt_id t).sub_const (chainMid m r)).pow 2).sub_const (chainR m r ^ 2)
    convert this using 1 <;> (try rfl) <;> simp <;> ring
  have hψ : HasDerivAt expNegInvGlue
      (deriv expNegInvGlue ((t - chainMid m r) ^ 2 - chainR m r ^ 2))
      ((t - chainMid m r) ^ 2 - chainR m r ^ 2) :=
    ((expNegInvGlue.contDiff (n := 1)).differentiable one_ne_zero _).hasDerivAt
  have hK : HasDerivAt (chainK m r) (chainL m r *
      (deriv expNegInvGlue ((t - chainMid m r) ^ 2 - chainR m r ^ 2) *
        (2 * (t - chainMid m r)))) t :=
    (hψ.comp t hq).const_mul _
  have := hG.sub hK
  unfold chainF' 
  convert this using 1
  · rfl
  · ring

lemma chainF'_pos (hm : 1 ≤ m) (hr : 0 < r) {δ : ℝ} (hδ : 0 < δ) {t : ℝ}
    (ht : t < chainMid m r - chainR m r) : 0 < chainF' m r δ t := by
  have hR := chainR_nonneg hm hr
  have hd : 0 ≤ deriv expNegInvGlue ((t - chainMid m r) ^ 2 - chainR m r ^ 2) :=
    expNegInvGlue.monotone.deriv_nonneg
  have hS : 0 < ∑ i ∈ Finset.range m, softPos' δ (chainU r i t) * (-2 * (t - chainS r i)) := by
    refine Finset.sum_pos (fun i _ => mul_pos (softPos'_pos hδ _) ?_) ⟨0, Finset.mem_range.mpr hm⟩
    have : chainMid m r - chainR m r = -r := by unfold chainMid chainR; ring
    have hs : 0 ≤ chainS r i := by unfold chainS; positivity
    linarith
  have hK : 0 ≤ chainL m r * deriv expNegInvGlue ((t - chainMid m r) ^ 2 - chainR m r ^ 2) *
      (-(2 * (t - chainMid m r))) :=
    mul_nonneg (mul_nonneg chainL_nonneg hd) (by linarith)
  unfold chainF'
  nlinarith

lemma chainF'_neg (hm : 1 ≤ m) (hr : 0 < r) {δ : ℝ} (hδ : 0 < δ) {t : ℝ}
    (ht : chainMid m r + chainR m r < t) : chainF' m r δ t < 0 := by
  have hR := chainR_nonneg hm hr
  have hd : 0 ≤ deriv expNegInvGlue ((t - chainMid m r) ^ 2 - chainR m r ^ 2) :=
    expNegInvGlue.monotone.deriv_nonneg
  have hS : 0 < ∑ i ∈ Finset.range m, softPos' δ (chainU r i t) * (2 * (t - chainS r i)) := by
    refine Finset.sum_pos (fun i hi => mul_pos (softPos'_pos hδ _) ?_) ⟨0, Finset.mem_range.mpr hm⟩
    have : chainMid m r + chainR m r = 4 * r * ((m : ℝ) - 1) + r := by
      unfold chainMid chainR; ring
    have hi' : (i : ℝ) ≤ (m : ℝ) - 1 := by
      have := Finset.mem_range.mp hi
      have : (i : ℝ) + 1 ≤ m := by exact_mod_cast this
      linarith
    have hs : chainS r i ≤ 4 * r * ((m : ℝ) - 1) := by
      unfold chainS; nlinarith
    linarith
  have hK : 0 ≤ chainL m r * deriv expNegInvGlue ((t - chainMid m r) ^ 2 - chainR m r ^ 2) *
      (2 * (t - chainMid m r)) :=
    mul_nonneg (mul_nonneg chainL_nonneg hd) (by linarith)
  have heq : ∑ i ∈ Finset.range m, softPos' δ (chainU r i t) * (-2 * (t - chainS r i)) =
      -∑ i ∈ Finset.range m, softPos' δ (chainU r i t) * (2 * (t - chainS r i)) := by
    rw [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun i _ => by ring
  unfold chainF'
  rw [heq]
  linarith

lemma chainF_pos_of_mem (hm : 1 ≤ m) {δ : ℝ} (hδ : 0 < δ) {t : ℝ}
    (ht : (t - chainMid m r) ^ 2 ≤ chainR m r ^ 2) : 0 < chainF m r δ t := by
  unfold chainF; rw [chainK_eq_zero ht, sub_zero]; exact chainG_pos hm hδ t

lemma sq_le_of_mem_Icc {t c R : ℝ} (h1 : c - R ≤ t) (h2 : t ≤ c + R) :
    (t - c) ^ 2 ≤ R ^ 2 := by
  have : |t - c| ≤ R := abs_le.mpr ⟨by linarith, by linarith⟩
  have h0 : 0 ≤ R := (abs_nonneg _).trans this
  calc (t - c) ^ 2 = |t - c| ^ 2 := (sq_abs _).symm
    _ ≤ R ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2

lemma chainF_deriv_ne_zero (hm : 1 ≤ m) (hr : 0 < r) {δ : ℝ} (hδ : 0 < δ) {t : ℝ}
    (ht : chainF m r δ t = 0) : chainF' m r δ t ≠ 0 := by
  rcases lt_or_ge t (chainMid m r - chainR m r) with h1 | h1
  · exact (chainF'_pos hm hr hδ h1).ne'
  rcases lt_or_ge (chainMid m r + chainR m r) t with h2 | h2
  · exact (chainF'_neg hm hr hδ h2).ne
  exact absurd ht (chainF_pos_of_mem hm hδ (sq_le_of_mem_Icc h1 h2)).ne'

lemma continuous_chainF {δ : ℝ} (hδ : 0 < δ) : Continuous (chainF m r δ) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_chainF hδ t).continuousAt

lemma chainF_strictMonoOn (hm : 1 ≤ m) (hr : 0 < r) {δ : ℝ} (hδ : 0 < δ) :
    StrictMonoOn (chainF m r δ) (Set.Iic (chainMid m r - chainR m r)) := by
  refine strictMonoOn_of_deriv_pos (convex_Iic _) (continuous_chainF hδ).continuousOn
    fun t ht => ?_
  rw [interior_Iic] at ht
  rw [(hasDerivAt_chainF hδ t).deriv]
  exact chainF'_pos hm hr hδ ht

lemma chainF_strictAntiOn (hm : 1 ≤ m) (hr : 0 < r) {δ : ℝ} (hδ : 0 < δ) :
    StrictAntiOn (chainF m r δ) (Set.Ici (chainMid m r + chainR m r)) := by
  refine strictAntiOn_of_deriv_neg (convex_Ici _) (continuous_chainF hδ).continuousOn
    fun t ht => ?_
  rw [interior_Ici] at ht
  rw [(hasDerivAt_chainF hδ t).deriv]
  exact chainF'_neg hm hr hδ ht

lemma chainF_pos_between (hm : 1 ≤ m) (hr : 0 < r) {δ : ℝ} (hδ : 0 < δ) {t₁ t₂ t₃ : ℝ}
    (h12 : t₁ ≤ t₂) (h23 : t₂ ≤ t₃) (h1 : 0 < chainF m r δ t₁) (h3 : 0 < chainF m r δ t₃) :
    0 < chainF m r δ t₂ := by
  rcases lt_or_ge t₂ (chainMid m r - chainR m r) with ha | ha
  · exact h1.trans_le ((chainF_strictMonoOn hm hr hδ).monotoneOn (Set.mem_Iic.mpr (by linarith))
      (Set.mem_Iic.mpr ha.le) h12)
  rcases lt_or_ge (chainMid m r + chainR m r) t₂ with hb | hb
  · exact h3.trans_le ((chainF_strictAntiOn hm hr hδ).antitoneOn (Set.mem_Ici.mpr hb.le)
      (Set.mem_Ici.mpr (by linarith)) h23)
  exact chainF_pos_of_mem hm hδ (sq_le_of_mem_Icc ha hb)

lemma chainU_le_chainF {δ : ℝ} (hδ : 0 < δ) {i : ℕ} (hi : i < m) {t : ℝ}
    (ht : (t - chainMid m r) ^ 2 ≤ chainR m r ^ 2) : chainU r i t ≤ chainF m r δ t := by
  unfold chainF; rw [chainK_eq_zero ht, sub_zero]
  unfold chainG
  calc chainU r i t ≤ softPos δ (chainU r i t) := (le_max_left _ _).trans (max_le_softPos hδ _)
    _ ≤ _ := Finset.single_le_sum (f := fun i => softPos δ (chainU r i t))
        (fun j _ => (softPos_pos hδ _).le) (Finset.mem_range.mpr hi)

lemma chainF_le_chainG (δ t : ℝ) : chainF m r δ t ≤ chainG m r δ t := by
  unfold chainF; linarith [chainK_nonneg (m := m) (r := r) t]

lemma tendsto_chainG (t : ℝ) : Tendsto (fun n : ℕ => chainG m r (1 / ((n : ℝ) + 1)) t) atTop
    (𝓝 (∑ i ∈ Finset.range m, max (chainU r i t) 0)) :=
  tendsto_finsetSum _ fun _ _ => tendsto_softPos _

lemma sum_max_chainU_lt (hr : 0 < r) {t y : ℝ} (hy : 0 < y) (h : ∀ i < m, chainU r i t < y) :
    ∑ i ∈ Finset.range m, max (chainU r i t) 0 < y := by
  by_cases hex : ∃ i ∈ Finset.range m, 0 < chainU r i t
  · obtain ⟨i, hi, hpos⟩ := hex
    rw [Finset.sum_eq_single i]
    · rw [max_eq_left hpos.le]; exact h i (Finset.mem_range.mp hi)
    · intro j _ hji
      refine max_eq_right (not_lt.mp fun hj => ?_)
      have h1 : (t - chainS r i) ^ 2 < r ^ 2 := by unfold chainU at hpos; linarith
      have h2 : (t - chainS r j) ^ 2 < r ^ 2 := by unfold chainU at hj; linarith
      have a1 := abs_lt_of_sq_lt_sq' h1 hr.le
      have a2 := abs_lt_of_sq_lt_sq' h2 hr.le
      have hij : (i : ℝ) ≠ j := fun e => hji (by exact_mod_cast e.symm)
      rcases lt_or_gt_of_ne hij with hl | hl
      · have : (i : ℝ) + 1 ≤ j := by
          have : i + 1 ≤ j := by exact_mod_cast hl
          exact_mod_cast this
        unfold chainS at a1 a2
        nlinarith [a1.1, a1.2, a2.1, a2.2]
      · have : (j : ℝ) + 1 ≤ i := by
          have : j + 1 ≤ i := by exact_mod_cast hl
          exact_mod_cast this
        unfold chainS at a1 a2
        nlinarith [a1.1, a1.2, a2.1, a2.2]
    · intro hi'; exact absurd hi hi'
  · push_neg at hex
    rw [Finset.sum_eq_zero fun i hi => max_eq_right (hex i hi)]
    exact hy

end Profile

section Domain

variable {N : ℕ} (m : ℕ) (r δ : ℝ) (e0 : RN N)

/-- The defining function of the approximating domain (a solid of revolution about `ℝ e₀`). -/
def chainRho (x : RN N) : ℝ := ‖x‖ ^ 2 - ⟪e0, x⟫ ^ 2 - chainF m r δ ⟪e0, x⟫

/-- The approximating domain `{x : |x_⊥|² < F(⟨e₀, x⟩)}`. -/
def chainDom : Set (RN N) := {x | chainRho m r δ e0 x < 0}

variable {m r δ e0}

lemma norm_sub_smul_sq (he0 : ‖e0‖ = 1) (x : RN N) (s : ℝ) :
    ‖x - s • e0‖ ^ 2 = (‖x‖ ^ 2 - ⟪e0, x⟫ ^ 2) + (⟪e0, x⟫ - s) ^ 2 := by
  rw [norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, he0, real_inner_comm,
    mul_one, sq_abs]
  ring

lemma perp_nonneg (he0 : ‖e0‖ = 1) (x : RN N) : 0 ≤ ‖x‖ ^ 2 - ⟪e0, x⟫ ^ 2 := by
  have := norm_sub_smul_sq he0 x ⟪e0, x⟫
  rw [sub_self, zero_pow two_ne_zero, add_zero] at this
  rw [← this]; positivity

lemma perp_ge_sq {e1 : RN N} (he0 : ‖e0‖ = 1) (he1 : ‖e1‖ = 1) (h01 : ⟪e0, e1⟫ = 0)
    (x : RN N) : ⟪e1, x⟫ ^ 2 ≤ ‖x‖ ^ 2 - ⟪e0, x⟫ ^ 2 := by
  have h := norm_nonneg (x - ⟪e0, x⟫ • e0 - ⟪e1, x⟫ • e1)
  have h2 : ‖x - ⟪e0, x⟫ • e0 - ⟪e1, x⟫ • e1‖ ^ 2 = ‖x‖ ^ 2 - ⟪e0, x⟫ ^ 2 - ⟪e1, x⟫ ^ 2 := by
    rw [@norm_sub_sq_real, norm_sub_smul_sq he0, sub_self, inner_sub_left, inner_smul_left,
      inner_smul_right, inner_smul_right, norm_smul, Real.norm_eq_abs, he1, h01,
      real_inner_comm x e1]
    simp only [RCLike.conj_to_real, mul_zero, sub_zero, mul_one, sq_abs]
    ring
  nlinarith [sq_nonneg ‖x - ⟪e0, x⟫ • e0 - ⟪e1, x⟫ • e1‖]

lemma contDiff_chainF (hδ : 0 < δ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (chainF m r δ) := by
  have hU : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (chainU r i) := fun i => by
    unfold chainU; fun_prop
  have hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (chainG m r δ) := by
    unfold chainG
    exact ContDiff.sum fun i _ => (contDiff_softPos hδ).comp (hU i)
  have hK : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (chainK m r) := by
    unfold chainK
    exact contDiff_const.mul (expNegInvGlue.contDiff.comp (by fun_prop))
  exact hG.sub hK

lemma contDiff_chainRho (hδ : 0 < δ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (chainRho m r δ e0) := by
  unfold chainRho
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : RN N => ⟪e0, x⟫) :=
    (innerSL ℝ e0).contDiff
  exact ((contDiff_norm_sq ℝ).sub (h1.pow 2)).sub ((contDiff_chainF hδ).comp h1)

lemma hasFDerivAt_chainRho (hδ : 0 < δ) (x : RN N) :
    HasFDerivAt (chainRho m r δ e0)
      (2 • innerSL ℝ x - (2 * ⟪e0, x⟫ + chainF' m r δ ⟪e0, x⟫) • innerSL ℝ e0) x := by
  have h1 : HasFDerivAt (fun x : RN N => ⟪e0, x⟫) (innerSL ℝ e0) x :=
    (innerSL ℝ e0).hasFDerivAt
  have h2 := (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have h3 := h1.pow 2
  have h4 := (hasDerivAt_chainF (m := m) (r := r) hδ ⟪e0, x⟫).comp_hasFDerivAt x h1
  have := (h2.sub h3).sub h4
  unfold chainRho
  refine this.congr_fderiv ?_
  ext w
  simp [innerSL]
  ring

lemma chainRho_regular (hm : 1 ≤ m) (hr : 0 < r) (hδ : 0 < δ) (he0 : ‖e0‖ = 1) (x : RN N)
    (hx : chainRho m r δ e0 x = 0) : fderiv ℝ (chainRho m r δ e0) x ≠ 0 := by
  rw [(hasFDerivAt_chainRho hδ x).fderiv]
  intro h0
  have ha := congrArg (fun L : RN N →L[ℝ] ℝ => L e0) h0
  have hb := congrArg (fun L : RN N →L[ℝ] ℝ => L (x - ⟪e0, x⟫ • e0)) h0
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, innerSL_apply_apply,
    ContinuousLinearMap.zero_apply, smul_eq_mul, real_inner_self_eq_norm_sq, he0, nsmul_eq_mul,
    Nat.cast_ofNat, one_pow, mul_one] at ha hb
  have hee : ⟪e0, e0⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he0]; norm_num
  have hxe : ⟪x, e0⟫ = ⟪e0, x⟫ := real_inner_comm _ _
  rw [inner_sub_right, inner_sub_right, inner_smul_right, inner_smul_right,
    real_inner_self_eq_norm_sq, hee, hxe] at hb
  rw [hxe] at ha
  have hF' : chainF' m r δ ⟪e0, x⟫ = 0 := by linarith
  have hP : ‖x‖ ^ 2 - ⟪e0, x⟫ ^ 2 = 0 := by nlinarith
  have hF : chainF m r δ ⟪e0, x⟫ = 0 := by unfold chainRho at hx; linarith
  exact chainF_deriv_ne_zero hm hr hδ hF hF'

lemma hasSmoothBoundary_chainDom (hm : 1 ≤ m) (hr : 0 < r) (hδ : 0 < δ) (he0 : ‖e0‖ = 1) :
    HasSmoothBoundary (chainDom m r δ e0) :=
  ⟨chainRho m r δ e0, contDiff_chainRho hδ, rfl, chainRho_regular hm hr hδ he0⟩

end Domain

section Domain2

variable {N : ℕ} {m : ℕ} {r δ : ℝ} {e0 : RN N}

lemma inner_self_unit (he0 : ‖e0‖ = 1) : ⟪e0, e0⟫ = 1 := by
  rw [real_inner_self_eq_norm_sq, he0]; norm_num

lemma chainS_mem (hr : 0 < r) {i : ℕ} (hi : i < m) :
    0 ≤ chainS r i ∧ chainS r i ≤ 4 * r * ((m : ℝ) - 1) := by
  have hi' : (i : ℝ) ≤ (m : ℝ) - 1 := by
    have : (i : ℝ) + 1 ≤ m := by exact_mod_cast hi
    linarith
  unfold chainS
  exact ⟨by positivity, by nlinarith⟩

lemma ball_subset_chainDom (hδ : 0 < δ) (he0 : ‖e0‖ = 1) (hr : 0 < r) {i : ℕ} (hi : i < m) :
    ball (chainS r i • e0) r ⊆ chainDom m r δ e0 := by
  intro x hx
  rw [mem_ball, dist_eq_norm] at hx
  have h2 : ‖x - chainS r i • e0‖ ^ 2 < r ^ 2 := pow_lt_pow_left₀ hx (norm_nonneg _) two_ne_zero
  rw [norm_sub_smul_sq he0] at h2
  have hP := perp_nonneg he0 x
  have ha : (⟪e0, x⟫ - chainS r i) ^ 2 < r ^ 2 := by linarith
  have ha' := abs_lt_of_sq_lt_sq' ha hr.le
  obtain ⟨hs0, hs1⟩ := chainS_mem hr hi
  have hmem : (⟪e0, x⟫ - chainMid m r) ^ 2 ≤ chainR m r ^ 2 := by
    refine sq_le_of_mem_Icc ?_ ?_
    · have : chainMid m r - chainR m r = -r := by unfold chainMid chainR; ring
      linarith [ha'.1]
    · have : chainMid m r + chainR m r = 4 * r * ((m : ℝ) - 1) + r := by
        unfold chainMid chainR; ring
      linarith [ha'.2]
  have hU := chainU_le_chainF (m := m) hδ hi hmem
  unfold chainU at hU
  show chainRho m r δ e0 x < 0
  unfold chainRho
  linarith

/-- Radius of a ball containing all the approximating domains. -/
def chainBig (m : ℕ) (r : ℝ) : ℝ :=
  m * (r ^ 2 + 1 / 2) + (|chainMid m r| + chainR m r + 1) + 1

lemma chainDom_subset_ball (hm : 1 ≤ m) (hr : 0 < r) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (he0 : ‖e0‖ = 1) : chainDom m r δ e0 ⊆ ball 0 (chainBig m r) := by
  intro x hx
  change chainRho m r δ e0 x < 0 at hx
  unfold chainRho at hx
  have hP := perp_nonneg he0 x
  have hR := chainR_nonneg hm hr
  set a := ⟪e0, x⟫
  have hFa : 0 < chainF m r δ a := by linarith
  have hnear : (a - chainMid m r) ^ 2 < (chainR m r + 1) ^ 2 := by
    by_contra h
    push_neg at h
    have : 1 ≤ (a - chainMid m r) ^ 2 - chainR m r ^ 2 := by nlinarith
    exact absurd (chainF_neg hm hδ hδ1 this) (not_lt.mpr hFa.le)
  have habs := abs_lt_of_sq_lt_sq' hnear (by linarith)
  set T := |chainMid m r| + chainR m r + 1
  have hT : |a| < T := by
    have := le_abs_self (chainMid m r)
    have := neg_abs_le (chainMid m r)
    rw [abs_lt]; constructor <;> linarith [habs.1, habs.2]
  have hT0 : 0 < T := (abs_nonneg a).trans_lt hT
  have ha2 : a ^ 2 < T ^ 2 := by
    rw [← sq_abs]; exact pow_lt_pow_left₀ hT (abs_nonneg _) two_ne_zero
  set A := (m : ℝ) * (r ^ 2 + 1 / 2)
  have hA : 0 ≤ A := by positivity
  have hG : chainG m r δ a ≤ A := chainG_le (m := m) (r := r) hδ hδ1 a
  have hFG := chainF_le_chainG (m := m) (r := r) δ a
  have h3 : ‖x‖ ^ 2 < A + T ^ 2 := by linarith
  have hx2 : ‖x‖ ^ 2 < (A + T + 1) ^ 2 := by nlinarith [mul_nonneg hA hT0.le, sq_nonneg A]
  rw [mem_ball, dist_zero_right]
  have := abs_lt_of_sq_lt_sq' hx2 (by positivity)
  have hB : chainBig m r = A + T + 1 := rfl
  rw [hB]
  linarith [this.2]

lemma isOpen_chainDom (hδ : 0 < δ) : IsOpen (chainDom m r δ e0) :=
  isOpen_lt (contDiff_chainRho hδ).continuous continuous_const

lemma axis_mem_chainDom (he0 : ‖e0‖ = 1) {t : ℝ} (ht : 0 < chainF m r δ t) :
    t • e0 ∈ chainDom m r δ e0 := by
  show chainRho m r δ e0 (t • e0) < 0
  unfold chainRho
  rw [inner_smul_right, inner_self_unit he0, mul_one, norm_smul, he0, mul_one, Real.norm_eq_abs,
    sq_abs]
  linarith

lemma joinedIn_chainDom (hm : 1 ≤ m) (hr : 0 < r) (hδ : 0 < δ) (he0 : ‖e0‖ = 1) {x : RN N}
    (hx : x ∈ chainDom m r δ e0) : JoinedIn (chainDom m r δ e0) x (chainMid m r • e0) := by
  have hx' : chainRho m r δ e0 x < 0 := hx
  unfold chainRho at hx'
  have hP := perp_nonneg he0 x
  set a := ⟪e0, x⟫ with ha_def
  have hFa : 0 < chainF m r δ a := by linarith
  have hFm : 0 < chainF m r δ (chainMid m r) :=
    chainF_pos_of_mem hm hδ (by rw [sub_self, zero_pow two_ne_zero]; positivity)
  have hee := inner_self_unit he0
  refine (JoinedIn.of_segment_subset (y := a • e0) ?_).trans (JoinedIn.of_segment_subset ?_)
  · rintro y ⟨α, β, hα, hβ, hαβ, rfl⟩
    show chainRho m r δ e0 (α • x + β • (a • e0)) < 0
    unfold chainRho
    have hy0 : ⟪e0, α • x + β • (a • e0)⟫ = a := by
      rw [inner_add_right, inner_smul_right, inner_smul_right, inner_smul_right, hee, ← ha_def]
      have : β = 1 - α := by linarith
      subst this; ring
    have hyx : α • x + β • (a • e0) - a • e0 = α • (x - a • e0) := by
      have : β = 1 - α := by linarith
      subst this
      rw [smul_sub, sub_smul, one_smul]; abel
    have h1 := norm_sub_smul_sq he0 (α • x + β • (a • e0)) a
    rw [hy0, sub_self, zero_pow two_ne_zero, add_zero, hyx, norm_smul, mul_pow,
      norm_sub_smul_sq he0, ← ha_def, sub_self, zero_pow two_ne_zero, add_zero] at h1
    rw [hy0]
    have hα1 : α ≤ 1 := by linarith
    have : ‖α‖ ^ 2 ≤ 1 := by
      rw [Real.norm_eq_abs, sq_abs]; nlinarith
    nlinarith
  · rintro y ⟨α, β, hα, hβ, hαβ, rfl⟩
    rw [smul_smul, smul_smul, ← add_smul]
    refine axis_mem_chainDom he0 ?_
    rcases le_total a (chainMid m r) with h | h
    · have h1 := mul_nonneg hβ (sub_nonneg.mpr h)
      have h2 := mul_nonneg hα (sub_nonneg.mpr h)
      have hα' : α = 1 - β := by linarith
      subst hα'
      exact chainF_pos_between hm hr hδ (t₁ := a) (t₃ := chainMid m r) (by nlinarith)
        (by nlinarith) hFa hFm
    · have h1 := mul_nonneg hβ (sub_nonneg.mpr h)
      have h2 := mul_nonneg hα (sub_nonneg.mpr h)
      have hα' : α = 1 - β := by linarith
      subst hα'
      exact chainF_pos_between hm hr hδ (t₁ := chainMid m r) (t₃ := a) (by nlinarith)
        (by nlinarith) hFm hFa

lemma isDomain_chainDom (hm : 1 ≤ m) (hr : 0 < r) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (he0 : ‖e0‖ = 1) : IsDomain (chainDom m r δ e0) := by
  have hFm : 0 < chainF m r δ (chainMid m r) :=
    chainF_pos_of_mem hm hδ (by rw [sub_self, zero_pow two_ne_zero]; positivity)
  have hz := axis_mem_chainDom (m := m) (r := r) (δ := δ) he0 hFm
  refine ⟨⟨isOpen_chainDom hδ, ⟨_, hz⟩,
    isBounded_ball.subset (chainDom_subset_ball hm hr hδ hδ1 he0)⟩, ?_⟩
  refine (isPathConnected_iff.mpr ⟨⟨_, hz⟩, fun x hx y hy => ?_⟩).isConnected
  exact (joinedIn_chainDom hm hr hδ he0 hx).trans (joinedIn_chainDom hm hr hδ he0 hy).symm

lemma chainDom_eventually_not_mem (hr : 0 < r) (he0 : ‖e0‖ = 1) {x : RN N}
    (hP : 0 < ‖x‖ ^ 2 - ⟪e0, x⟫ ^ 2) (hx : ∀ i < m, x ∉ closedBall (chainS r i • e0) r) :
    ∀ᶠ n : ℕ in atTop, x ∉ chainDom m r (1 / ((n : ℝ) + 1)) e0 := by
  have hu : ∀ i < m, chainU r i ⟪e0, x⟫ < ‖x‖ ^ 2 - ⟪e0, x⟫ ^ 2 := by
    intro i hi
    have h := hx i hi
    rw [mem_closedBall, dist_eq_norm, not_le] at h
    have h2 : r ^ 2 < ‖x - chainS r i • e0‖ ^ 2 := pow_lt_pow_left₀ h hr.le two_ne_zero
    rw [norm_sub_smul_sq he0] at h2
    unfold chainU; linarith
  have hlt := sum_max_chainU_lt hr hP hu
  filter_upwards [(tendsto_chainG (m := m) (r := r) ⟪e0, x⟫).eventually (gt_mem_nhds hlt)]
    with n hn hmem
  have h1 : chainRho m r (1 / ((n : ℝ) + 1)) e0 x < 0 := hmem
  unfold chainRho at h1
  have := chainF_le_chainG (m := m) (r := r) (1 / ((n : ℝ) + 1)) ⟪e0, x⟫
  linarith

end Domain2

section Main

variable {N : ℕ}

/-- **Shrinking tubes for a chain of collinear balls.**  For congruent balls of radius `r`
centred at `4 r i e₀` (`i < m`, `e₀` a unit vector) there are smooth bounded domains `Ωₙ`
containing the balls with `λ_j(Ωₙ) → λ_j(⋃ᵢ Bᵢ)` for every `j`. -/
theorem chain_tubes (hN : 2 ≤ N) {m : ℕ} (hm : 1 ≤ m) {r : ℝ} (hr : 0 < r) {e0 e1 : RN N}
    (he0 : ‖e0‖ = 1) (he1 : ‖e1‖ = 1) (h01 : ⟪e0, e1⟫ = 0)
    (hdisj : Pairwise (Disjoint on fun i : Fin m => closedBall ((4 * r * ((i : ℕ) : ℝ)) • e0) r)) :
    ∃ Ω : ℕ → Set (RN N), (∀ n, IsDomain (Ω n) ∧ HasSmoothBoundary (Ω n) ∧
        (⋃ i : Fin m, ball ((4 * r * ((i : ℕ) : ℝ)) • e0) r) ⊆ Ω n) ∧
      ∀ j, Tendsto (fun n => eigenvalue (Ω n) j) atTop
        (𝓝 (eigenvalue (⋃ i : Fin m, ball ((4 * r * ((i : ℕ) : ℝ)) • e0) r) j)) := by
  set δ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hδ_def
  have hδ : ∀ n, 0 < δ n := fun n => by positivity
  have hδ1 : ∀ n, δ n ≤ 1 := fun n => by
    simp only [hδ_def]
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hU : ∀ n, (⋃ i : Fin m, ball ((4 * r * ((i : ℕ) : ℝ)) • e0) r) ⊆
      chainDom m r (δ n) e0 :=
    fun n => Set.iUnion_subset fun i => ball_subset_chainDom (hδ n) he0 hr i.isLt
  refine ⟨fun n => chainDom m r (δ n) e0, fun n => ⟨isDomain_chainDom hm hr (hδ n) (hδ1 n) he0,
    hasSmoothBoundary_chainDom hm hr (hδ n) he0, hU n⟩, fun j => ?_⟩
  have hR := chainR_nonneg hm hr
  have hB : 0 < chainBig m r := by unfold chainBig; positivity
  have hD₀ : IsAdmissible (ball (0 : RN N) (chainBig m r)) :=
    ⟨isOpen_ball, ⟨0, mem_ball_self hB⟩, isBounded_ball⟩
  refine eigenvalue_tendsto_of_shrinking hN hm _ hr hdisj hD₀ _
    (fun n => (isDomain_chainDom hm hr (hδ n) (hδ1 n) he0).1) hU
    (fun n => chainDom_subset_ball hm hr (hδ n) (hδ1 n) he0) ?_ j
  have he1' : e1 ≠ 0 := by
    intro h; rw [h, norm_zero] at he1; exact zero_ne_one he1
  filter_upwards [ae_inner_ne_zero 0 he1'] with x hx1 hx
  rw [sub_zero] at hx1
  have hP : 0 < ‖x‖ ^ 2 - ⟪e0, x⟫ ^ 2 :=
    (pow_two_pos_of_ne_zero hx1).trans_le (perp_ge_sq he0 he1 h01 x)
  refine chainDom_eventually_not_mem hr he0 hP fun i hi hmem => hx ?_
  exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hmem⟩

end Main

end FourthRatio

end
