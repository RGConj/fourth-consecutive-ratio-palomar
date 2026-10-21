module

public import RequestProject.BesselEntire

/-!
# Zeros of the Bessel function `J_ν`

From the series definition of `J_ν` (`ν ≥ 0`) alone we prove the one-dimensional Bessel facts
used in the ball/annulus lemma:

* `besselZero_props` — `0 < j_{ν,1} < j_{ν,2}`, both are zeros of `J_ν`, and `J_ν` does not
  vanish on `(0, j_{ν,1})` and `(j_{ν,1}, j_{ν,2})`;
* `besselJ_neg_between` — `J_ν < 0` on `(j_{ν,1}, j_{ν,2})`;
* `besselZero_lt_succ` — `j_{ν,1} < j_{ν+1,1}`, hence `C_N > 1` (`CN_gt_one`).

The existence of zeros is proved by a Sturm comparison argument (with `sin((x - α)/2)`) on
intervals of length `2π`; the zeros are isolated because `x ↦ x^{-ν} J_ν(x)` is entire and
nonzero at `0`; the sign change at `j_{ν,1}` and the interlacing come from the identities
`(s^{ν+1} g')' = -s^ν g/4` and `(s^{ν+1} g_{ν+1})' = s^ν g_ν` for the entire series `g`.
-/

@[expose] public section

open Filter Topology Set Nat

noncomputable section

namespace FourthRatio

/-! ### The entire function `F(x) = g(x²)` -/

/-- First derivative series `g'`. -/
def besselSeries1 (ν s : ℝ) : ℝ := ∑' m : ℕ, ((m : ℝ) + 1) * besselCoef ν 1 (m + 1) * s ^ m

/-- Second derivative series `g''`. -/
def besselSeries2 (ν s : ℝ) : ℝ :=
  ∑' m : ℕ, ((m : ℝ) + 1) * (((m + 1 : ℕ) : ℝ) + 1) * besselCoef ν 1 (m + 1 + 1) * s ^ m

/-- `F(x) = g(x²)`, so that `J_ν(x) = (x/2)^ν F(x)` for `x > 0`. -/
def besselF (ν x : ℝ) : ℝ := besselSeries ν 1 (x ^ 2)

lemma besselJ_eq_besselF (ν : ℝ) {t : ℝ} (ht : 0 < t) :
    besselJ ν t = (t / 2) ^ ν * besselF ν t := by
  unfold besselJ besselF besselSeries
  rw [← tsum_mul_left]
  congr 1; funext m
  have hb : 0 < t / 2 := by positivity
  rw [Real.rpow_add hb, show (2 * (m : ℝ)) = ((2 * m : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast]
  unfold besselCoef
  rw [pow_mul, div_pow t 2 2]
  simp only [one_div]
  ring

lemma hasDerivAt_besselF {ν : ℝ} (hν : 0 ≤ ν) (x : ℝ) :
    HasDerivAt (besselF ν) (2 * x * besselSeries1 ν (x ^ 2)) x := by
  have h := (hasDerivAt_besselSeries hν zero_le_one (x ^ 2)).comp x (hasDerivAt_pow 2 x)
  convert h using 1
  · rfl
  · simp [besselSeries1, Function.comp_def]
    ring

lemma hasDerivAt_besselF1 {ν : ℝ} (hν : 0 ≤ ν) (x : ℝ) :
    HasDerivAt (fun x => 2 * x * besselSeries1 ν (x ^ 2))
      (2 * besselSeries1 ν (x ^ 2) + 4 * x ^ 2 * besselSeries2 ν (x ^ 2)) x := by
  have h := (hasDerivAt_besselSeries_deriv hν zero_le_one (x ^ 2)).comp x (hasDerivAt_pow 2 x)
  have h2 := ((hasDerivAt_id x).const_mul 2).mul h
  convert h2 using 1
  · rfl
  · simp [besselSeries1, besselSeries2, Function.comp_def]
    ring

lemma besselF_ode {ν : ℝ} (hν : 0 ≤ ν) (x : ℝ) :
    x * (2 * besselSeries1 ν (x ^ 2) + 4 * x ^ 2 * besselSeries2 ν (x ^ 2)) +
      2 * (ν + 1 / 2) * (2 * x * besselSeries1 ν (x ^ 2)) + x * besselF ν x = 0 := by
  have h := besselSeries_ode hν zero_le_one (x ^ 2)
  unfold besselF besselSeries1 besselSeries2
  linear_combination x * h

lemma besselF_analytic {ν : ℝ} (hν : 0 ≤ ν) : AnalyticOnNhd ℝ (besselF ν) univ := by
  intro x _
  exact (analyticAt_besselSeries hν zero_le_one _).comp (analyticAt_id.pow 2)

lemma besselF_zero_pos {ν : ℝ} (hν : 0 ≤ ν) : 0 < besselF ν 0 := by
  unfold besselF
  rw [zero_pow two_ne_zero, besselSeries_zero]
  exact inv_pos.mpr (Real.Gamma_pos_of_pos (by linarith))

/-! ### Sturm comparison -/

lemma sturm_pos_false (m : ℝ) (F F1 F2 : ℝ → ℝ) (hF : ∀ x > 0, HasDerivAt F (F1 x) x)
    (hF1 : ∀ x > 0, HasDerivAt F1 (F2 x) x)
    (hode : ∀ x > 0, x * F2 x + 2 * m * F1 x + x * F x = 0) {α : ℝ} (hα : 1 ≤ α)
    (hA : 2 * |m * (m - 1)| ≤ α) (hpos : ∀ x ∈ Icc α (α + 2 * Real.pi), 0 < F x) : False := by
  set β := α + 2 * Real.pi with hβ
  have hα0 : 0 < α := by linarith
  have hαβ : α ≤ β := by have := Real.pi_pos; linarith
  set s : ℝ → ℝ := fun x => Real.sin ((x - α) / 2) with hs_def
  set c : ℝ → ℝ := fun x => Real.cos ((x - α) / 2) / 2 with hc_def
  set K : ℝ → ℝ := fun x => F1 x * s x - F x * c x + m * F x * s x / x with hK_def
  set H : ℝ → ℝ := fun x => x ^ m * K x with hH_def
  set H' : ℝ → ℝ := fun x => -(x ^ m * F x * s x * (3 / 4 - m * (m - 1) / x ^ 2)) with hH'_def
  have hderiv : ∀ x > 0, HasDerivAt H (H' x) x := by
    intro x hx
    have hs : HasDerivAt s (c x) x := by
      have := (((hasDerivAt_id x).sub_const α).div_const 2).sin
      convert this using 1
      · rfl
      · dsimp [c]
        ring
    have hc : HasDerivAt c (-(s x) / 4) x := by
      have := ((((hasDerivAt_id x).sub_const α).div_const 2).cos).div_const 2
      convert this using 1
      · rfl
      · dsimp [s]
        ring
    have hK : HasDerivAt K (F2 x * s x + F1 x * c x - (F1 x * c x + F x * (-(s x) / 4)) +
        ((m * F1 x * s x + m * F x * c x) * x - m * F x * s x * 1) / x ^ 2) x := by
      have := (((hF1 x hx).mul hs).sub ((hF x hx).mul hc)).add
        ((((hF x hx).const_mul m).mul hs).div (hasDerivAt_id x) hx.ne')
      convert this using 1 <;> rfl
    have hp : HasDerivAt (fun x : ℝ => x ^ m) (m * x ^ (m - 1)) x :=
      Real.hasDerivAt_rpow_const (Or.inl hx.ne')
    have := hp.mul hK
    convert this using 1
    rw [Real.rpow_sub_one hx.ne']
    have hF2 : F2 x = -(2 * m * F1 x + x * F x) / x := by
      field_simp; linarith [hode x hx]
    simp only [H', K]
    rw [hF2]; field_simp; ring
  have hanti : AntitoneOn H (Icc α β) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := H') (convex_Icc _ _) ?_ ?_ ?_
    · intro x hx
      exact (hderiv x (by linarith [hx.1])).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (hderiv x (by linarith [hx.1])).hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hx0 : 0 < x := by linarith [hx.1]
      have hFx := hpos x ⟨hx.1.le, hx.2.le⟩
      have hsx : 0 ≤ s x := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hx.1])
        (by linarith [hx.2])
      have hm : m * (m - 1) / x ^ 2 ≤ 1 / 2 := by
        rw [div_le_iff₀ (by positivity)]
        have h1 := le_abs_self (m * (m - 1))
        nlinarith [hx.1]
      have hxm : 0 < x ^ m := Real.rpow_pos_of_pos hx0 m
      have : 0 ≤ x ^ m * F x * s x * (3 / 4 - m * (m - 1) / x ^ 2) := by
        have := mul_nonneg (mul_pos hxm hFx).le hsx
        exact mul_nonneg this (by linarith)
      simp only [H']; linarith
  have hle := hanti ⟨le_rfl, hαβ⟩ ⟨hαβ, le_rfl⟩ hαβ
  have hHα : H α = -(α ^ m * F α / 2) := by
    simp only [H, K, s, c, sub_self, zero_div, Real.sin_zero, Real.cos_zero]; ring
  have hHβ : H β = β ^ m * F β / 2 := by
    have : (β - α) / 2 = Real.pi := by rw [hβ]; ring
    simp only [H, K, s, c, this, Real.sin_pi, Real.cos_pi]; ring
  have h1 := mul_pos (Real.rpow_pos_of_pos hα0 m) (hpos α ⟨le_rfl, hαβ⟩)
  have h2 := mul_pos (Real.rpow_pos_of_pos (by linarith : 0 < β) m) (hpos β ⟨hαβ, le_rfl⟩)
  rw [hHα, hHβ] at hle
  linarith

lemma sturm_zero (m : ℝ) (F F1 F2 : ℝ → ℝ) (hF : ∀ x > 0, HasDerivAt F (F1 x) x)
    (hF1 : ∀ x > 0, HasDerivAt F1 (F2 x) x)
    (hode : ∀ x > 0, x * F2 x + 2 * m * F1 x + x * F x = 0) {α : ℝ} (hα : 1 ≤ α)
    (hA : 2 * |m * (m - 1)| ≤ α) : ∃ x ∈ Icc α (α + 2 * Real.pi), F x = 0 := by
  by_contra hno
  push_neg at hno
  have hαβ : α ≤ α + 2 * Real.pi := by have := Real.pi_pos; linarith
  have hcont : ∀ x ∈ Icc α (α + 2 * Real.pi), ContinuousOn F (Icc α x) := fun x hx y hy =>
    (hF y (by linarith [hy.1])).continuousAt.continuousWithinAt
  rcases lt_or_gt_of_ne (hno α ⟨le_rfl, hαβ⟩) with hneg | hposα
  · refine sturm_pos_false m (fun x => -F x) (fun x => -F1 x) (fun x => -F2 x)
      (fun x hx => (hF x hx).neg) (fun x hx => (hF1 x hx).neg)
      (fun x hx => by linear_combination -hode x hx) hα hA ?_
    intro x hx
    by_contra h
    push_neg at h
    have hFx : 0 < F x := lt_of_le_of_ne (by linarith) (hno x hx).symm
    obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc hx.1 (hcont x hx) ⟨hneg.le, hFx.le⟩
    exact hno z ⟨hz.1, hz.2.trans hx.2⟩ hz0
  · refine sturm_pos_false m F F1 F2 hF hF1 hode hα hA ?_
    intro x hx
    by_contra h
    push_neg at h
    have hFx : F x < 0 := lt_of_le_of_ne h (hno x hx)
    obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc' hx.1 (hcont x hx) ⟨hFx.le, hposα.le⟩
    exact hno z ⟨hz.1, hz.2.trans hx.2⟩ hz0

lemma besselF_zeros_unbounded {ν : ℝ} (hν : 0 ≤ ν) (b : ℝ) : ∃ x, b < x ∧ besselF ν x = 0 := by
  set m := ν + 1 / 2
  set α := max (max 1 (2 * |m * (m - 1)|)) (b + 1)
  obtain ⟨x, hx, hx0⟩ := sturm_zero m (besselF ν) (fun x => 2 * x * besselSeries1 ν (x ^ 2))
    (fun x => 2 * besselSeries1 ν (x ^ 2) + 4 * x ^ 2 * besselSeries2 ν (x ^ 2))
    (fun x _ => hasDerivAt_besselF hν x) (fun x _ => hasDerivAt_besselF1 hν x)
    (fun x _ => besselF_ode hν x) (α := α) (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_trans (le_max_right _ _) (le_max_left _ _))
  exact ⟨x, by linarith [hx.1, le_max_right (max 1 (2 * |m * (m - 1)|)) (b + 1)], hx0⟩

/-! ### The next zero -/

lemma next_zero (f : ℝ → ℝ) (hf : AnalyticOnNhd ℝ f univ) (h0 : f 0 ≠ 0)
    (hunb : ∀ b, ∃ x, b < x ∧ f x = 0) (c : ℝ) :
    c < sInf {x | c < x ∧ f x = 0} ∧ f (sInf {x | c < x ∧ f x = 0}) = 0 ∧
      ∀ x, c < x → x < sInf {x | c < x ∧ f x = 0} → f x ≠ 0 := by
  rcases (hf c (mem_univ c)).eventually_eq_zero_or_eventually_ne_zero with h | h
  · exact absurd (hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (mem_univ c) h (mem_univ 0)) h0
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.mp h
  set S := {x | c < x ∧ f x = 0}
  have hlow : ∀ x ∈ S, c + δ ≤ x := by
    rintro x ⟨hcx, hfx⟩
    by_contra hlt
    push_neg at hlt
    exact hball ⟨by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith,
      ne_of_gt hcx⟩ hfx
  obtain ⟨x0, hx0, hfx0⟩ := hunb c
  have hne : S.Nonempty := ⟨x0, hx0, hfx0⟩
  have hbdd : BddBelow S := ⟨c, fun x hx => hx.1.le⟩
  have hge : c + δ ≤ sInf S := le_csInf hne hlow
  have hfc : Continuous f := continuousOn_univ.mp hf.continuousOn
  have hclosed : IsClosed {x | c + δ ≤ x ∧ f x = 0} :=
    (isClosed_le continuous_const continuous_id).inter (isClosed_eq hfc continuous_const)
  have hmem := closure_minimal
    (show S ⊆ {x | c + δ ≤ x ∧ f x = 0} from fun x hx => ⟨hlow x hx, hx.2⟩) hclosed
    (csInf_mem_closure hne hbdd)
  refine ⟨by linarith, hmem.2, fun x hcx hxs hfx => ?_⟩
  have := csInf_le hbdd ⟨hcx, hfx⟩
  linarith

lemma besselZero_succ_eq {ν : ℝ} (k : ℕ) (hk : 0 ≤ besselZero ν k) :
    besselZero ν (k + 1) = sInf {x | besselZero ν k < x ∧ besselF ν x = 0} := by
  rw [besselZero]
  congr 1; ext x
  simp only [mem_setOf_eq]
  constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨h1, ?_⟩
  · have hx : 0 < x := by linarith
    rw [besselJ_eq_besselF ν hx] at h2
    exact (mul_eq_zero.mp h2).resolve_left (Real.rpow_pos_of_pos (by linarith) _).ne'
  · rw [besselJ_eq_besselF ν (by linarith), h2, mul_zero]

/-- `0 < j_{ν,1} < j_{ν,2}`, both are zeros, and there are no zeros in between. -/
theorem besselZero_props {ν : ℝ} (hν : 0 ≤ ν) :
    0 < besselZero ν 1 ∧ besselZero ν 1 < besselZero ν 2 ∧
      besselF ν (besselZero ν 1) = 0 ∧ besselF ν (besselZero ν 2) = 0 ∧
      (∀ x, 0 < x → x < besselZero ν 1 → besselF ν x ≠ 0) ∧
      (∀ x, besselZero ν 1 < x → x < besselZero ν 2 → besselF ν x ≠ 0) := by
  have hF := besselF_analytic hν
  have h0 := (besselF_zero_pos hν).ne'
  have hunb := besselF_zeros_unbounded hν
  have e1 := besselZero_succ_eq (ν := ν) 0 le_rfl
  rw [show besselZero ν 0 = 0 from rfl] at e1
  obtain ⟨a1, b1, c1⟩ := next_zero _ hF h0 hunb 0
  rw [← e1] at a1 b1 c1
  have e2 := besselZero_succ_eq (ν := ν) 1 a1.le
  obtain ⟨a2, b2, c2⟩ := next_zero _ hF h0 hunb (besselZero ν 1)
  rw [← e2] at a2 b2 c2
  exact ⟨a1, a2, b1, b2, c1, c2⟩

/-! ### Signs -/

lemma pos_of_euler {ν b : ℝ} (hν : 0 ≤ ν) (hb : 0 < b) (q q' r : ℝ → ℝ)
    (hq : ∀ s, HasDerivAt q (q' s) s) (hrel : ∀ s, (ν + 1) * q s + s * q' s = r s)
    (hr : ∀ s ∈ Ioo 0 b, 0 < r s) : 0 < q b := by
  set Q : ℝ → ℝ := fun s => s ^ (ν + 1) * q s with hQ
  have hmono : StrictMonoOn Q (Icc 0 b) := by
    refine strictMonoOn_of_hasDerivWithinAt_pos (f' := fun s => s ^ ν * r s) (convex_Icc _ _)
      ?_ ?_ ?_
    · intro s _
      exact ((Real.continuousAt_rpow_const _ _ (Or.inr (by linarith))).mul
        (hq s).continuousAt).continuousWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      have hs0 : 0 < s := hs.1
      have := (Real.hasDerivAt_rpow_const (p := ν + 1) (Or.inl hs0.ne')).mul (hq s)
      convert this.hasDerivWithinAt using 1
      show s ^ ν * r s = _
      rw [← hrel s, show ν + 1 - 1 = ν by ring, Real.rpow_add_one hs0.ne']
      ring
    · intro s hs
      rw [interior_Icc] at hs
      exact mul_pos (Real.rpow_pos_of_pos hs.1 _) (hr s hs)
  have h := hmono ⟨le_rfl, hb.le⟩ ⟨hb.le, le_rfl⟩ hb
  simp only [Q, Real.zero_rpow (by linarith : ν + 1 ≠ 0), zero_mul] at h
  exact pos_of_mul_pos_right h (Real.rpow_pos_of_pos hb _).le

lemma besselF_pos_before {ν : ℝ} (hν : 0 ≤ ν) {x : ℝ} (hx0 : 0 ≤ x)
    (hx : x < besselZero ν 1) : 0 < besselF ν x := by
  obtain ⟨-, -, -, -, c1, -⟩ := besselZero_props hν
  have h0 := besselF_zero_pos hν
  by_contra hneg
  push_neg at hneg
  have hcont : ContinuousOn (besselF ν) (Icc 0 x) :=
    ((besselF_analytic hν).continuousOn).mono (subset_univ _)
  obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc' hx0 hcont ⟨hneg, h0.le⟩
  have hz0' : z ≠ 0 := by rintro rfl; exact h0.ne' hz0
  exact c1 z (lt_of_le_of_ne hz.1 (Ne.symm hz0')) (lt_of_le_of_lt hz.2 hx) hz0

lemma eventually_lt_of_hasDerivAt_neg {f : ℝ → ℝ} {f' a : ℝ} (h : HasDerivAt f f' a)
    (h' : f' < 0) : ∀ᶠ x in 𝓝[>] a, f x < f a := by
  have h2 := (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl a)).mp
    (h.hasDerivWithinAt (s := Ioi a))
  filter_upwards [h2.eventually (gt_mem_nhds h'), self_mem_nhdsWithin] with x hx hxa
  rw [slope_def_field] at hx
  have hxa' : 0 < x - a := sub_pos.mpr hxa
  by_contra hge
  push_neg at hge
  have : 0 ≤ (f x - f a) / (x - a) := div_nonneg (by linarith) hxa'.le
  linarith

/-- `J_ν < 0` on `(j_{ν,1}, j_{ν,2})`. -/
theorem besselJ_neg_between {ν : ℝ} (hν : 0 ≤ ν) {s : ℝ} (hs1 : besselZero ν 1 < s)
    (hs2 : s < besselZero ν 2) : besselJ ν s < 0 := by
  obtain ⟨a1, a2, b1, b2, c1, c2⟩ := besselZero_props hν
  set j1 := besselZero ν 1
  have hpos_g : ∀ t ∈ Ioo 0 (j1 ^ 2), 0 < besselSeries ν 1 t / 4 := by
    intro t ht
    have hst : Real.sqrt t < j1 := by
      rw [Real.sqrt_lt' a1]; exact ht.2
    have := besselF_pos_before hν (Real.sqrt_nonneg t) hst
    unfold besselF at this
    rw [Real.sq_sqrt ht.1.le] at this
    positivity
  have hg1 : 0 < -besselSeries1 ν (j1 ^ 2) :=
    pos_of_euler hν (by positivity) (fun s => -besselSeries1 ν s)
      (fun s => -besselSeries2 ν s) (fun s => besselSeries ν 1 s / 4)
      (fun s => (hasDerivAt_besselSeries_deriv hν zero_le_one s).neg)
      (fun s => by
        have := besselSeries_ode hν zero_le_one s
        unfold besselSeries1 besselSeries2
        linear_combination (-1 / 4 : ℝ) * this) hpos_g
  have hd : 2 * j1 * besselSeries1 ν (j1 ^ 2) < 0 := by nlinarith
  have hev := eventually_lt_of_hasDerivAt_neg (hasDerivAt_besselF hν j1) hd
  rw [b1] at hev
  obtain ⟨t, htlt, ht⟩ := (hev.and (Ioo_mem_nhdsGT hs1)).exists
  have hFs : besselF ν s < 0 := by
    by_contra hge
    push_neg at hge
    have hFs' : 0 < besselF ν s := lt_of_le_of_ne hge (c2 s hs1 hs2).symm
    have hcont : ContinuousOn (besselF ν) (Icc t s) :=
      ((besselF_analytic hν).continuousOn).mono (subset_univ _)
    obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc ht.2.le hcont ⟨htlt.le, hFs'.le⟩
    exact c2 z (lt_of_lt_of_le ht.1 hz.1) (lt_of_le_of_lt hz.2 hs2) hz0
  rw [besselJ_eq_besselF ν (by linarith)]
  exact mul_neg_of_pos_of_neg (Real.rpow_pos_of_pos (by linarith) _) hFs

/-- The recursion `(ν+1) g_{ν+1}(s) + s g_{ν+1}'(s) = g_ν(s)`, i.e. `(s^{ν+1} g_{ν+1})' = s^ν g_ν`. -/
lemma besselSeries_succ_rel {ν : ℝ} (hν : 0 ≤ ν) (s : ℝ) :
    (ν + 1) * besselSeries (ν + 1) 1 s + s * besselSeries1 (ν + 1) s = besselSeries ν 1 s := by
  have hν' : 0 ≤ ν + 1 := by linarith
  set c := besselCoef (ν + 1) 1 with hc_def
  have hc := besselCoef_bound hν' zero_le_one
  have hd := derivCoef_bound c hc
  have hsC := summable_powSeries c hc s
  have hsD := summable_powSeries _ hd s
  have hshift : Summable (fun m : ℕ => ((m + 1 : ℕ) : ℝ) * c (m + 1) * s ^ (m + 1)) :=
    (hsD.mul_left s).congr (fun m => by push_cast; ring)
  have hn : Summable (fun n : ℕ => (n : ℝ) * c n * s ^ n) := (summable_nat_add_iff 1).mp hshift
  have heq : s * besselSeries1 (ν + 1) s = ∑' n : ℕ, (n : ℝ) * c n * s ^ n := by
    rw [tsum_eq_zero_add' (f := fun n : ℕ => (n : ℝ) * c n * s ^ n) hshift, besselSeries1,
      ← tsum_mul_left]
    simp only [CharP.cast_eq_zero, zero_mul, zero_add]
    congr 1; funext m; push_cast; ring
  rw [heq, besselSeries, besselSeries, ← tsum_mul_left, ← (hsC.mul_left _).tsum_add hn]
  congr 1; funext n
  have hpos : 0 < (n : ℝ) + ν + 1 := by positivity
  have hg : Real.Gamma ((n : ℝ) + (ν + 1) + 1) = ((n : ℝ) + ν + 1) * Real.Gamma (n + ν + 1) := by
    rw [show (n : ℝ) + (ν + 1) + 1 = ((n : ℝ) + ν + 1) + 1 by ring,
      Real.Gamma_add_one hpos.ne']
  have hgm : 0 < Real.Gamma (n + ν + 1) := Real.Gamma_pos_of_pos hpos
  simp only [hc_def, besselCoef]
  rw [hg]
  have hf : (0 : ℝ) < n ! := by positivity
  field_simp
  ring

/-- Interlacing: `j_{ν,1} < j_{ν+1,1}`. -/
theorem besselZero_lt_succ {ν : ℝ} (hν : 0 ≤ ν) : besselZero ν 1 < besselZero (ν + 1) 1 := by
  have hν' : 0 ≤ ν + 1 := by linarith
  obtain ⟨a1, -⟩ := besselZero_props hν
  obtain ⟨a1', -, b1', -⟩ := besselZero_props hν'
  by_contra hle
  push_neg at hle
  have : 0 < besselSeries (ν + 1) 1 (besselZero (ν + 1) 1 ^ 2) := by
    refine pos_of_euler hν (by positivity) (besselSeries (ν + 1) 1) (besselSeries1 (ν + 1))
      (besselSeries ν 1) (hasDerivAt_besselSeries hν' zero_le_one)
      (besselSeries_succ_rel hν) ?_
    intro t ht
    have hst : Real.sqrt t < besselZero ν 1 := by
      rw [Real.sqrt_lt' a1]
      exact lt_of_lt_of_le ht.2 (pow_le_pow_left₀ a1'.le hle 2)
    have := besselF_pos_before hν (Real.sqrt_nonneg t) hst
    unfold besselF at this
    rwa [Real.sq_sqrt ht.1.le] at this
  exact this.ne' b1'

/-- `C_N > 1`. -/
theorem CN_gt_one {N : ℕ} (hN : 2 ≤ N) : 1 < CN N := by
  have hν : 0 ≤ (N : ℝ) / 2 - 1 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hlt := besselZero_lt_succ hν
  rw [show (N : ℝ) / 2 - 1 + 1 = (N : ℝ) / 2 by ring] at hlt
  have a1 := (besselZero_props hν).1
  unfold CN
  rw [one_lt_div (by positivity)]
  exact pow_lt_pow_left₀ hlt a1.le two_ne_zero

end FourthRatio

end
