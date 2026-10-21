module

public import RequestProject.EigenSlab
public import RequestProject.SharpLevelSobolevH

/-! # The sharp lower bound for the gradient mass of a level slab -/

@[expose] public section
open Set MeasureTheory Filter Topology Metric
open scoped RealInnerProductSpace ENNReal
noncomputable section
namespace FourthRatio
variable {N : ℕ}

lemma clipValue_eq_height_of_ge {a b t : ℝ} (hab : a ≤ b) (hbt : b ≤ t) :
    clipValue a b t = b - a := by
  rw [clipValue_eq_min hab]
  apply min_eq_right
  exact (by linarith : b - a ≤ t - a).trans (le_max_left _ _)

/-- Sharp Sobolev gives the correct dimensional constant times slab height
and a power of the closed upper-level volume. -/
theorem level_slab_gradient_lower_bound (hN : 2 ≤ N)
    {D : Set (RN N)} (hD : MeasurableSet D) (hfin : volume D ≠ ∞)
    {p : Amb N} (hp : p ∈ H D)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a < b) :
    ENNReal.ofReal (b - a) * ((N : ℝ≥0∞) *
      volume {x | b ≤ (p.1 : RN N → ℝ) x} ^ (1 - (N : ℝ)⁻¹) *
        volume (ball (0 : RN N) 1) ^ (N : ℝ)⁻¹) ≤
      ENNReal.ofReal (∫ x in eigenSlab p a b, ‖(p.2 : RN N → RN N) x‖) := by
  let w := clipPair a b ha hb p
  have hw : w ∈ H D := clipPair_mem_H a b ha hb hp
  have hwp := sharp_level_volume_gradient_bound_H hN hD hfin hw
  have hnorm : (∫ x, ‖(w.2 : RN N → RN N) x‖) =
      ∫ x in eigenSlab p a b, ‖(p.2 : RN N → RN N) x‖ :=
    clipPair_norm_integral a b ha hb hab.le hp
  rw [hnorm] at hwp
  have hpN : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hp1 : 1 < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hexp : 0 < 1 - (N : ℝ)⁻¹ := by
    have := (inv_lt_one₀ hpN).mpr hp1
    linarith
  let C : ℝ≥0∞ := (N : ℝ≥0∞) *
    volume {x | b ≤ (p.1 : RN N → ℝ) x} ^ (1 - (N : ℝ)⁻¹) *
      volume (ball (0 : RN N) 1) ^ (N : ℝ)⁻¹
  calc
    _ = ∫⁻ t in Ioo (0 : ℝ) (b - a), C := by
      simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero]
      exact mul_comm _ _
    _ ≤ ∫⁻ t in Ioo (0 : ℝ) (b - a), (N : ℝ≥0∞) *
        volume {x | t < (w.1 : RN N → ℝ) x} ^ (1 - (N : ℝ)⁻¹) *
          volume (ball (0 : RN N) 1) ^ (N : ℝ)⁻¹ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      have hvol : volume {x | b ≤ (p.1 : RN N → ℝ) x} ≤
          volume {x | t < (w.1 : RN N → ℝ) x} := by
        apply measure_mono_ae
        filter_upwards [clipPair_fst_ae a b ha hb p] with x hx hxb
        change t < (w.1 : RN N → ℝ) x
        rw [hx, clipValue_eq_height_of_ge hab.le hxb]
        exact ht.2
      exact mul_le_mul_left (mul_le_mul_right ((ENNReal.rpow_le_rpow_iff hexp).mpr hvol) N) _
    _ ≤ ∫⁻ t in Ioi (0 : ℝ), (N : ℝ≥0∞) *
        volume {x | t < (w.1 : RN N → ℝ) x} ^ (1 - (N : ℝ)⁻¹) *
          volume (ball (0 : RN N) 1) ^ (N : ℝ)⁻¹ :=
      lintegral_mono_set (fun t ht => ht.1)
    _ ≤ _ := hwp

end FourthRatio
end
