module

public import RequestProject.SobolevSmoothChain

/-! # Positive parts above a nonnegative threshold in H₀¹ -/

@[expose] public section
open MeasureTheory Metric Filter Topology Function
open scoped RealInnerProductSpace ENNReal
noncomputable section
namespace FourthRatio
variable {N : ℕ}

lemma upperPart_abs_le (a t : ℝ) (ha : 0 ≤ a) : |max (t - a) 0| ≤ |t| := by
  rw [abs_of_nonneg (le_max_right _ _)]
  apply max_le
  · linarith [le_abs_self t]
  · exact abs_nonneg _

def shiftedGChain (a : ℝ) (ha : 0 ≤ a) (n : ℕ) : SmoothScalarChain where
  toFun := fun t => Gfun n (t - a)
  derivFun := fun t => dGfun n (t - a)
  smooth := (contDiff_Gfun n).comp (contDiff_id.sub contDiff_const)
  zero := by
    apply (Gfun_eq_zero_iff n (0 - a)).mpr
    have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  hasDeriv := fun t => by simpa only [Function.comp_def, id_eq, mul_one] using (hasDerivAt_Gfun n (t - a)).comp t ((hasDerivAt_id t).sub_const a)
  deriv_continuous := (continuous_dGfun n).comp (continuous_id.sub continuous_const)
  bound := Cstep
  bound_nonneg := zero_le_one.trans one_le_Cstep
  lipschitz := fun s t => by
    have h := Gfun_lipschitz n (s - a) (t - a)
    simpa only [sub_sub_sub_cancel_right] using h
  deriv_bound := fun t => abs_dGfun_le n (t - a)

lemma upperPart_memLp_fun (a : ℝ) (ha : 0 ≤ a) (f : L2 N) :
    MemLp (fun x => max ((f : RN N → ℝ) x - a) 0) 2 volume := by
  apply (Lp.memLp f).of_le
  · exact (((continuous_id.sub continuous_const).max continuous_const).comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable f))
  · exact Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using upperPart_abs_le a ((f : RN N → ℝ) x) ha

lemma upperPart_multiplier_measurable (a : ℝ) (f : L2 N) :
    AEStronglyMeasurable (fun x => if a < (f : RN N → ℝ) x then (1 : ℝ) else 0) volume := by
  have hm : Measurable (fun t : ℝ => if a < t then (1 : ℝ) else 0) :=
    Measurable.ite measurableSet_Ioi measurable_const measurable_const
  exact (hm.comp_aemeasurable (Lp.aestronglyMeasurable f).aemeasurable).aestronglyMeasurable

lemma upperPart_memLp_grad (a : ℝ) (p : Amb N) :
    MemLp (fun x => (if a < (p.1 : RN N → ℝ) x then (1 : ℝ) else 0) •
      (p.2 : RN N → RN N) x) 2 volume := by
  apply (Lp.memLp p.2).of_le ((upperPart_multiplier_measurable a p.1).smul (Lp.aestronglyMeasurable p.2))
  apply Eventually.of_forall
  intro x
  change ‖(if a < (p.1 : RN N → ℝ) x then (1 : ℝ) else 0) • (p.2 : RN N → RN N) x‖ ≤ ‖(p.2 : RN N → RN N) x‖
  split_ifs <;> simp

def upperPartPair (a : ℝ) (ha : 0 ≤ a) (p : Amb N) : Amb N :=
  (MemLp.toLp _ (upperPart_memLp_fun a ha p.1), MemLp.toLp _ (upperPart_memLp_grad a p))

lemma upperPartPair_fst_ae (a : ℝ) (ha : 0 ≤ a) (p : Amb N) :
    ((upperPartPair a ha p).1 : RN N → ℝ) =ᵐ[volume]
      fun x => max ((p.1 : RN N → ℝ) x - a) 0 :=
  MemLp.coeFn_toLp (upperPart_memLp_fun a ha p.1)

lemma upperPartPair_snd_ae (a : ℝ) (ha : 0 ≤ a) (p : Amb N) :
    ((upperPartPair a ha p).2 : RN N → RN N) =ᵐ[volume]
      fun x => (if a < (p.1 : RN N → ℝ) x then (1 : ℝ) else 0) • (p.2 : RN N → RN N) x :=
  MemLp.coeFn_toLp (upperPart_memLp_grad a p)

lemma tendsto_shiftedGChain_upperPart (a : ℝ) (ha : 0 ≤ a) (p : Amb N) :
    Tendsto (fun n => chainPair (shiftedGChain a ha n) p) atTop (𝓝 (upperPartPair a ha p)) := by
  have hC : 0 ≤ Cstep := zero_le_one.trans one_le_Cstep
  have hf : Tendsto (fun n => (chainPair (shiftedGChain a ha n) p).1) atTop
      (𝓝 (upperPartPair a ha p).1) := by
    refine Lp2_tendsto_of_dominated (g := fun x => ‖(p.1 : RN N → ℝ) x‖) (Lp.memLp p.1).norm
      (fun n => ?_) ?_
    · filter_upwards [chainPair_fst_ae (shiftedGChain a ha n) p] with x hx
      rw [hx, Real.norm_eq_abs, Real.norm_eq_abs]
      change |Gfun n ((p.1 : RN N → ℝ) x - a)| ≤ |(p.1 : RN N → ℝ) x|
      rw [abs_of_nonneg (Gfun_nonneg n _)]
      exact (Gfun_le_max n _).trans (by
        simpa only [abs_of_nonneg (le_max_right ((p.1 : RN N → ℝ) x - a) 0)] using upperPart_abs_le a ((p.1 : RN N → ℝ) x) ha)
    · filter_upwards [ae_all_iff.mpr (fun n => chainPair_fst_ae (shiftedGChain a ha n) p),
        upperPartPair_fst_ae a ha p] with x hx hp
      simp only [hx, hp]
      exact tendsto_Gfun _
  have hs : Tendsto (fun n => (chainPair (shiftedGChain a ha n) p).2) atTop
      (𝓝 (upperPartPair a ha p).2) := by
    refine L2v_mul_tendsto (a := fun n x => dGfun n ((p.1 : RN N → ℝ) x - a))
      (b := fun x => if a < (p.1 : RN N → ℝ) x then 1 else 0) hC
      (fun n => (continuous_dGfun n).comp_aestronglyMeasurable
        ((Lp.aestronglyMeasurable p.1).sub aestronglyMeasurable_const))
      (upperPart_multiplier_measurable a p.1) (fun n x => abs_dGfun_le n _)
      (fun x => ?_) tendsto_const_nhds
      (fun n => chainPair_snd_ae (shiftedGChain a ha n) p) (upperPartPair_snd_ae a ha p) ?_
    · split_ifs <;> simp only [abs_one, abs_zero] <;> linarith [one_le_Cstep]
    · apply Eventually.of_forall
      intro x
      have h := (tendsto_dGfun ((p.1 : RN N → ℝ) x - a)).smul_const ((p.2 : RN N → RN N) x)
      simpa only [sub_pos] using h
  exact hf.prodMk_nhds hs

theorem upperPartPair_mem_H (a : ℝ) (ha : 0 ≤ a) {D : Set (RN N)} {p : Amb N}
    (hp : p ∈ H D) : upperPartPair a ha p ∈ H D :=
  mem_H_of_tendsto (fun n => chainPair_mem_H (shiftedGChain a ha n) hp)
    (tendsto_shiftedGChain_upperPart a ha p)

end FourthRatio
end
