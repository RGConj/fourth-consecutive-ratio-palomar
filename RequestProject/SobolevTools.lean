module

public import RequestProject.External

/-!
# Elementary Sobolev tools for the model of `H₀¹(D)`

Auxiliary material used in the proof of the membership part of Lemma 3.1:
* dominated convergence in `L²`;
* the test graph is a linear subspace, so `H_D` is the closure of the test graph itself;
* a family of smooth truncation functions `Gfun n` approximating `t ↦ max t 0`.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Function
open scoped RealInnerProductSpace ENNReal

noncomputable section

namespace FourthRatio

variable {N : ℕ}

/-! ### `L²` estimates -/

lemma Lp2_norm_sq_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : Lp E 2 (volume : Measure (RN N))) :
    ‖f‖ ^ 2 = ∫ x, ‖(f : RN N → E) x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp

lemma Lp2_tendsto_of_dominated {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {u : ℕ → Lp E 2 (volume : Measure (RN N))} {w : Lp E 2 (volume : Measure (RN N))}
    {g : RN N → ℝ} (hg : MemLp g 2 volume)
    (hb : ∀ n, ∀ᵐ x, ‖(u n : RN N → E) x‖ ≤ g x)
    (hlim : ∀ᵐ x, Tendsto (fun n => (u n : RN N → E) x) atTop (𝓝 ((w : RN N → E) x))) :
    Tendsto u atTop (𝓝 w) := by
  have hw : ∀ᵐ x, ‖(w : RN N → E) x‖ ≤ g x := by
    filter_upwards [hlim, ae_all_iff.mpr hb] with x h1 h2
    exact le_of_tendsto' (h1.norm) h2
  have hsq : Tendsto (fun n => ∫ x, ‖(u n : RN N → E) x - (w : RN N → E) x‖ ^ 2) atTop
      (𝓝 (∫ _x : RN N, (0 : ℝ))) := by
    refine tendsto_integral_of_dominated_convergence (fun x => 4 * g x ^ 2) (fun n => ?_)
      (hg.integrable_sq.const_mul 4) (fun n => ?_) ?_
    · exact (((Lp.aestronglyMeasurable (u n)).sub (Lp.aestronglyMeasurable w)).norm.pow 2)
    · filter_upwards [hb n, hw] with x h1 h2
      have h0 : 0 ≤ g x := (norm_nonneg _).trans h1
      have := norm_sub_le ((u n : RN N → E) x) ((w : RN N → E) x)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      nlinarith [norm_nonneg ((u n : RN N → E) x - (w : RN N → E) x)]
    · filter_upwards [hlim] with x h
      have : Tendsto (fun n => (u n : RN N → E) x - (w : RN N → E) x) atTop (𝓝 0) := by
        simpa using h.sub_const ((w : RN N → E) x)
      simpa using (this.norm.pow 2)
  simp only [integral_zero] at hsq
  have heq : ∀ n, ‖u n - w‖ ^ 2 = ∫ x, ‖(u n : RN N → E) x - (w : RN N → E) x‖ ^ 2 := by
    intro n
    rw [Lp2_norm_sq_eq]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub (u n) w] with x hx
    rw [hx, Pi.sub_apply]
  have h2 : Tendsto (fun n => ‖u n - w‖ ^ 2) atTop (𝓝 0) := by
    simpa only [heq] using hsq
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h3 := (Real.continuous_sqrt.tendsto 0).comp h2
  simp only [Function.comp_def, Real.sqrt_zero] at h3
  refine h3.congr fun n => ?_
  exact Real.sqrt_sq (norm_nonneg _)

lemma Lp2_norm_le_add {E F G : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedAddCommGroup G] (f : Lp E 2 (volume : Measure (RN N)))
    (g : Lp F 2 (volume : Measure (RN N))) (h : Lp G 2 (volume : Measure (RN N)))
    {C C' : ℝ} (hC : 0 ≤ C) (hC' : 0 ≤ C')
    (hb : ∀ᵐ x, ‖(f : RN N → E) x‖ ≤ C * ‖(g : RN N → F) x‖ + C' * ‖(h : RN N → G) x‖) :
    ‖f‖ ≤ C * ‖g‖ + C' * ‖h‖ := by
  have key : eLpNorm (f : RN N → E) 2 volume ≤
      eLpNorm (fun x => C * ‖(g : RN N → F) x‖) 2 volume +
        eLpNorm (fun x => C' * ‖(h : RN N → G) x‖) 2 volume := by
    refine le_trans ?_ (eLpNorm_add_le (by norm_num))
    refine eLpNorm_mono_ae (Lp.aestronglyMeasurable f) ?_
    filter_upwards [hb] with x hx
    simp only [Pi.add_apply, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity)]
    exact hx
  have e1 : eLpNorm (fun x => C * ‖(g : RN N → F) x‖) 2 volume =
      ENNReal.ofReal C * eLpNorm (g : RN N → F) 2 volume := by
    rw [show (fun x => C * ‖(g : RN N → F) x‖) = C • (fun x => ‖(g : RN N → F) x‖) from rfl,
      eLpNorm_const_smul, eLpNorm_norm _ (Lp.aestronglyMeasurable g), Real.enorm_eq_ofReal hC]
  have e2 : eLpNorm (fun x => C' * ‖(h : RN N → G) x‖) 2 volume =
      ENNReal.ofReal C' * eLpNorm (h : RN N → G) 2 volume := by
    rw [show (fun x => C' * ‖(h : RN N → G) x‖) = C' • (fun x => ‖(h : RN N → G) x‖) from rfl,
      eLpNorm_const_smul, eLpNorm_norm _ (Lp.aestronglyMeasurable h), Real.enorm_eq_ofReal hC']
  rw [e1, e2] at key
  rw [Lp.norm_def, Lp.norm_def, Lp.norm_def]
  have hfin1 := Lp.eLpNorm_ne_top g
  have hfin2 := Lp.eLpNorm_ne_top h
  calc (eLpNorm (f : RN N → E) 2 volume).toReal
      ≤ (ENNReal.ofReal C * eLpNorm (g : RN N → F) 2 volume +
          ENNReal.ofReal C' * eLpNorm (h : RN N → G) 2 volume).toReal :=
        ENNReal.toReal_mono (by finiteness) key
    _ = C * (eLpNorm (g : RN N → F) 2 volume).toReal +
          C' * (eLpNorm (h : RN N → G) 2 volume).toReal := by
        rw [ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_mul,
          ENNReal.toReal_mul, ENNReal.toReal_ofReal hC, ENNReal.toReal_ofReal hC']

/- The fact that the test graph is a subspace (`mem_testGraph_of_mem_span`,
`exists_seq_testGraph`, `mem_H_of_tendsto`) is in `RequestProject/TestPair.lean`. -/

/-! ### Smooth truncations -/

/-- `stepDeriv s = st(s) + s st'(s)` where `st` is the smooth transition function. -/
def stepDeriv (s : ℝ) : ℝ :=
  Real.smoothTransition s + s * deriv Real.smoothTransition s

/-- Smooth truncation `G_n(t) = (t - ε) st((t - ε)/ε)`, `ε = 1/(n+1)`. It vanishes for
`t ≤ ε` and approximates `max t 0`. -/
def Gfun (n : ℕ) (t : ℝ) : ℝ :=
  (t - 1 / ((n : ℝ) + 1)) * Real.smoothTransition (((n : ℝ) + 1) * t - 1)

/-- The derivative of `Gfun n`. -/
def dGfun (n : ℕ) (t : ℝ) : ℝ := stepDeriv (((n : ℝ) + 1) * t - 1)

lemma deriv_smoothTransition_of_nonpos {s : ℝ} (hs : s ≤ 0) :
    deriv Real.smoothTransition s = 0 := by
  apply IsLocalMin.deriv_eq_zero
  exact Eventually.of_forall fun y => by
    rw [Real.smoothTransition.zero_of_nonpos hs]; exact Real.smoothTransition.nonneg y

lemma deriv_smoothTransition_of_one_le {s : ℝ} (hs : 1 ≤ s) :
    deriv Real.smoothTransition s = 0 := by
  apply IsLocalMax.deriv_eq_zero
  exact Eventually.of_forall fun y => by
    rw [Real.smoothTransition.one_of_one_le hs]; exact Real.smoothTransition.le_one y

lemma stepDeriv_of_nonpos {s : ℝ} (hs : s ≤ 0) : stepDeriv s = 0 := by
  simp [stepDeriv, Real.smoothTransition.zero_of_nonpos hs, deriv_smoothTransition_of_nonpos hs]

lemma stepDeriv_of_one_le {s : ℝ} (hs : 1 ≤ s) : stepDeriv s = 1 := by
  simp [stepDeriv, Real.smoothTransition.one_of_one_le hs, deriv_smoothTransition_of_one_le hs]

lemma continuous_stepDeriv : Continuous stepDeriv := by
  have h : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  exact Real.smoothTransition.continuous.add (continuous_id.mul h)

lemma contDiff_Gfun (n : ℕ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gfun n) := by
  unfold Gfun
  exact (contDiff_id.sub contDiff_const).mul
    (Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const))

lemma hasDerivAt_Gfun (n : ℕ) (t : ℝ) : HasDerivAt (Gfun n) (dGfun n t) t := by
  have hst : HasDerivAt Real.smoothTransition
      (deriv Real.smoothTransition (((n : ℝ) + 1) * t - 1)) (((n : ℝ) + 1) * t - 1) :=
    ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero _).hasDerivAt
  have h1 : HasDerivAt (fun t : ℝ => ((n : ℝ) + 1) * t - 1) ((n : ℝ) + 1) t := by
    simpa using ((hasDerivAt_id t).const_mul ((n : ℝ) + 1)).sub_const 1
  have h2 := ((hasDerivAt_id t).sub_const (1 / ((n : ℝ) + 1))).mul (hst.comp t h1)
  convert h2 using 1
  · rfl
  · simp only [dGfun, stepDeriv, id, Function.comp]
    have : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp

lemma continuous_dGfun (n : ℕ) : Continuous (dGfun n) :=
  continuous_stepDeriv.comp ((continuous_const.mul continuous_id).sub continuous_const)

lemma exists_bound_stepDeriv : ∃ C : ℝ, 1 ≤ C ∧ ∀ s, |stepDeriv s| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    continuous_stepDeriv.continuousOn
  refine ⟨max C 1, le_max_right _ _, fun s => ?_⟩
  rcases le_or_gt s 0 with h | h
  · rw [stepDeriv_of_nonpos h]; simp
  rcases le_or_gt 1 s with h' | h'
  · rw [stepDeriv_of_one_le h']; simp
  exact (hC s ⟨h.le, h'.le⟩).trans (le_max_left _ _)

lemma Gfun_eq_zero_iff (n : ℕ) (t : ℝ) : Gfun n t = 0 ↔ t ≤ 1 / ((n : ℝ) + 1) := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  constructor
  · intro h
    by_contra h'
    push_neg at h'
    have h1 : 0 < t - 1 / ((n : ℝ) + 1) := by linarith
    have h2 : 0 < ((n : ℝ) + 1) * t - 1 := by
      rw [div_lt_iff₀ hn] at h'; linarith
    have := mul_pos h1 (Real.smoothTransition.pos_of_pos h2)
    rw [Gfun] at h; linarith
  · intro h
    have h2 : ((n : ℝ) + 1) * t - 1 ≤ 0 := by
      rw [le_div_iff₀ hn] at h; linarith
    simp [Gfun, Real.smoothTransition.zero_of_nonpos h2]

lemma dGfun_eq_zero (n : ℕ) {t : ℝ} (ht : t ≤ 1 / ((n : ℝ) + 1)) : dGfun n t = 0 := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  apply stepDeriv_of_nonpos
  rw [le_div_iff₀ hn] at ht; linarith

lemma Gfun_nonneg (n : ℕ) (t : ℝ) : 0 ≤ Gfun n t := by
  rcases le_or_gt t (1 / ((n : ℝ) + 1)) with h | h
  · rw [(Gfun_eq_zero_iff n t).mpr h]
  · exact mul_nonneg (by linarith) (Real.smoothTransition.nonneg _)

lemma Gfun_le_max (n : ℕ) (t : ℝ) : Gfun n t ≤ max t 0 := by
  rcases le_or_gt t (1 / ((n : ℝ) + 1)) with h | h
  · rw [(Gfun_eq_zero_iff n t).mpr h]; exact le_max_right _ _
  · have h0 : 0 < 1 / ((n : ℝ) + 1) := by positivity
    calc Gfun n t ≤ (t - 1 / ((n : ℝ) + 1)) * 1 :=
          mul_le_mul_of_nonneg_left (Real.smoothTransition.le_one _) (by linarith)
      _ ≤ max t 0 := by rw [mul_one]; linarith [le_max_left t 0]

lemma abs_Gfun_le (n : ℕ) (t : ℝ) : |Gfun n t| ≤ |t| := by
  rw [abs_of_nonneg (Gfun_nonneg n t)]
  exact (Gfun_le_max n t).trans (max_le (le_abs_self t) (abs_nonneg t))

lemma Gfun_lipschitz_aux {C : ℝ} (hC : ∀ s, |stepDeriv s| ≤ C) (n : ℕ) (a b : ℝ) :
    |Gfun n a - Gfun n b| ≤ C * |a - b| := by
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := Gfun n) (f' := dGfun n)
    (s := Set.univ) (fun x _ => (hasDerivAt_Gfun n x).hasDerivWithinAt)
    (fun x _ => by rw [Real.norm_eq_abs]; exact hC _) convex_univ (Set.mem_univ b)
    (Set.mem_univ a)
  simpa [Real.norm_eq_abs] using this

lemma eventually_one_le (t : ℝ) (ht : 0 < t) :
    ∀ᶠ n : ℕ in atTop, 1 ≤ ((n : ℝ) + 1) * t - 1 := by
  obtain ⟨m, hm⟩ := exists_nat_gt (2 / t)
  filter_upwards [eventually_ge_atTop m] with n hn
  have : 2 / t < (n : ℝ) + 1 := by
    have : (m : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  rw [div_lt_iff₀ ht] at this
  linarith

lemma tendsto_Gfun (t : ℝ) : Tendsto (fun n => Gfun n t) atTop (𝓝 (max t 0)) := by
  rcases le_or_gt t 0 with h | h
  · rw [max_eq_right h]
    have : ∀ n : ℕ, Gfun n t = 0 := fun n =>
      (Gfun_eq_zero_iff n t).mpr (h.trans (by positivity))
    simp [this]
  · rw [max_eq_left h.le]
    have h1 : Tendsto (fun n : ℕ => t - 1 / ((n : ℝ) + 1)) atTop (𝓝 (t - 0)) :=
      tendsto_const_nhds.sub tendsto_one_div_add_atTop_nhds_zero_nat
    rw [sub_zero] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_one_le t h] with n hn
    simp [Gfun, Real.smoothTransition.one_of_one_le hn]

lemma tendsto_dGfun (t : ℝ) :
    Tendsto (fun n => dGfun n t) atTop (𝓝 (if 0 < t then 1 else 0)) := by
  rcases le_or_gt t 0 with h | h
  · rw [if_neg (not_lt.mpr h)]
    have : ∀ n : ℕ, dGfun n t = 0 := fun n => dGfun_eq_zero n (h.trans (by positivity))
    simp [this]
  · rw [if_pos h]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_one_le t h] with n hn
    exact (stepDeriv_of_one_le hn).symm

/-- A uniform bound for the derivatives of the truncations. -/
def Cstep : ℝ := exists_bound_stepDeriv.choose

lemma one_le_Cstep : 1 ≤ Cstep := exists_bound_stepDeriv.choose_spec.1

lemma abs_dGfun_le (n : ℕ) (t : ℝ) : |dGfun n t| ≤ Cstep :=
  exists_bound_stepDeriv.choose_spec.2 _

lemma Gfun_lipschitz (n : ℕ) (a b : ℝ) : |Gfun n a - Gfun n b| ≤ Cstep * |a - b| :=
  Gfun_lipschitz_aux exists_bound_stepDeriv.choose_spec.2 n a b

end FourthRatio

end
