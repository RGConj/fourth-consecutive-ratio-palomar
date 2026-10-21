module

public import RequestProject.SharpLevelSobolevSigned
public import RequestProject.LevelVolumeLsc
public import RequestProject.L2FiniteMass
public import RequestProject.TestPair
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! # The sharp level-volume inequality on the graph closure H₀¹

Only finiteness and measurability of the domain are used in the limit step.
No regularity of its boundary is required.
-/

@[expose] public section
open Set Filter MeasureTheory Topology Metric
open scoped ENNReal RealInnerProductSpace
noncomputable section
namespace FourthRatio

/-- The sharp integrated superlevel-volume bound for actual elements of the
project's graph-closure Sobolev space. -/
theorem sharp_level_volume_gradient_bound_H {N : ℕ} (hN : 2 ≤ N)
    {D : Set (RN N)} (hD : MeasurableSet D) (hfin : volume D ≠ ∞)
    {p : Amb N} (hp : p ∈ H D) :
    (∫⁻ t in Ioi (0 : ℝ),
      (N : ℝ≥0∞) * volume {x | t < (p.1 : RN N → ℝ) x} ^ (1 - (N : ℝ)⁻¹) *
        volume (ball (0 : RN N) 1) ^ (N : ℝ)⁻¹) ≤
      ENNReal.ofReal (∫ x, ‖(p.2 : RN N → RN N) x‖) := by
  obtain ⟨q, hq, hlim⟩ := exists_seq_testGraph hp
  have hqH : ∀ n, q n ∈ H D := fun n => testGraph_subset_H D (hq n)
  choose φ hφ hc hs hf hg using hq
  have hfirst : Tendsto (fun n => (q n).1) atTop (𝓝 p.1) :=
    continuous_fst.tendsto p |>.comp hlim
  obtain ⟨η, hη, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hfirst).exists_seq_tendsto_ae
  have hconv : ∀ᵐ x ∂volume,
      Tendsto (fun n => φ (η n) x) atTop (𝓝 ((p.1 : RN N → ℝ) x)) := by
    filter_upwards [hae, ae_all_iff.mpr (fun n => hf (η n))] with x hx hfx
    exact hx.congr fun n => hfx n
  have hpN : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hp1 : 1 < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hinv : (N : ℝ)⁻¹ < 1 := (inv_lt_one₀ hpN).mpr hp1
  have hexp : 0 < 1 - (N : ℝ)⁻¹ := by linarith
  have hvol : volume (ball (0 : RN N) 1) ^ (N : ℝ)⁻¹ ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) measure_ball_ne_top
  have hlsc := level_volume_lintegral_le_liminf (Lp.aestronglyMeasurable p.1).aemeasurable
    (fun n => (hφ (η n)).continuous.aemeasurable) hconv hexp (by simp : (N : ℝ≥0∞) ≠ ∞) hvol
  have hvanish : ∀ (v : Amb N), v ∈ H D →
      ∀ᵐ x ∂volume, x ∉ D → (v.2 : RN N → RN N) x = 0 := by
    intro v hv
    have hvz := (mem_vanishOn.mp (H_le_vanishOn D hv)).2
    rw [EventuallyEq, ae_restrict_iff' hD.compl] at hvz
    exact hvz
  have hgrad := tendsto_integral_norm_L2_of_support hD hfin
    ((continuous_snd.tendsto p |>.comp hlim).comp hη.tendsto_atTop)
    (fun n => hvanish (q (η n)) (hqH (η n))) (hvanish p hp)
  have hgradφ : Tendsto (fun n => ∫ x, ‖gradient (φ (η n)) x‖) atTop
      (𝓝 (∫ x, ‖(p.2 : RN N → RN N) x‖)) := by
    have heq : ∀ n, (∫ x, ‖(q (η n)).2 x‖) = ∫ x, ‖gradient (φ (η n)) x‖ := by
      intro n
      apply integral_congr_ae
      exact (hg (η n)).mono fun x hx => congrArg norm hx
    simpa only [Function.comp_def, heq] using hgrad
  calc
    _ ≤ liminf (fun n => ∫⁻ t in Ioi (0 : ℝ),
        (N : ℝ≥0∞) * volume {x | t < φ (η n) x} ^ (1 - (N : ℝ)⁻¹) *
        volume (ball (0 : RN N) 1) ^ (N : ℝ)⁻¹) atTop := hlsc
    _ ≤ liminf (fun n => ENNReal.ofReal (∫ x, ‖gradient (φ (η n)) x‖)) atTop := by
      refine liminf_le_liminf ?_ (by isBoundedDefault) (by isBoundedDefault)
      exact Eventually.of_forall fun n =>
        sharp_level_volume_gradient_bound_signed hN ((hφ (η n)).of_le (by simp)) (hc (η n))
    _ = _ := (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hgradφ).liminf_eq

end FourthRatio
end
