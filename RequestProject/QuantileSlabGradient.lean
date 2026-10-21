module

public import RequestProject.LevelSlabSobolev
public import RequestProject.QuantileThresholds

/-! # The sharp gradient bound at actual volume-coordinate quantiles -/

@[expose] public section
open Set MeasureTheory Filter Topology Metric
open scoped ENNReal RealInnerProductSpace
noncomputable section
namespace FourthRatio
variable {N : ℕ}

/-- The sharp lower gradient estimate at two actual quantile levels, in the
volume coordinate used by Talenti's inequality. -/
theorem quantile_slab_gradient_bound (hN : 2 ≤ N)
    {D : Set (RN N)} (hD : MeasurableSet D) (hfin : volume D ≠ ∞)
    {p : Amb N} (hp : p ∈ H D)
    {s₁ s₂ : ℝ} (hs₁ : 0 < s₁) (hs₂ : 0 < s₂)
    (hq : decreasingProfile volume (p.1 : RN N → ℝ) s₂ <
      decreasingProfile volume (p.1 : RN N → ℝ) s₁) :
    (decreasingProfile volume (p.1 : RN N → ℝ) s₁ -
      decreasingProfile volume (p.1 : RN N → ℝ) s₂) *
      ((N : ℝ) * s₁ ^ (1 - (N : ℝ)⁻¹) *
        volume.real (ball (0 : RN N) 1) ^ (N : ℝ)⁻¹) ≤
      ∫ x in eigenSlab p
        (decreasingProfile volume (p.1 : RN N → ℝ) s₂)
        (decreasingProfile volume (p.1 : RN N → ℝ) s₁), ‖(p.2 : RN N → RN N) x‖ := by
  let a := decreasingProfile volume (p.1 : RN N → ℝ) s₂
  let b := decreasingProfile volume (p.1 : RN N → ℝ) s₁
  have ha : 0 ≤ a := decreasingProfile_nonneg _ _ _
  have hb : 0 ≤ b := decreasingProfile_nonneg _ _ _
  have hpi := (integrable_components_of_mem_H hD hfin hp).1
  have hB := decreasingProfile_closed_tail_ge hpi hs₁ (ha.trans_lt hq)
  have hpN : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hp1 : 1 < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hexp : 0 < 1 - (N : ℝ)⁻¹ := by
    have := (inv_lt_one₀ hpN).mpr hp1
    linarith
  have hlow := level_slab_gradient_lower_bound hN hD hfin hp a b ha hb hq
  have hpow : ENNReal.ofReal s₁ ^ (1 - (N : ℝ)⁻¹) ≤
      volume {x | b ≤ (p.1 : RN N → ℝ) x} ^ (1 - (N : ℝ)⁻¹) :=
    (ENNReal.rpow_le_rpow_iff hexp).mpr hB
  have hmono : ENNReal.ofReal (b - a) * ((N : ℝ≥0∞) *
      ENNReal.ofReal s₁ ^ (1 - (N : ℝ)⁻¹) * volume (ball (0 : RN N) 1) ^ (N : ℝ)⁻¹) ≤
      ENNReal.ofReal (∫ x in eigenSlab p a b, ‖(p.2 : RN N → RN N) x‖) := by
    refine le_trans ?_ hlow
    exact mul_le_mul_right (mul_le_mul_left (mul_le_mul_right hpow N) _) _
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmono
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ← ENNReal.toReal_rpow] at hreal
  rw [ENNReal.toReal_ofReal (show 0 ≤ b - a from sub_nonneg.mpr hq.le),
    ENNReal.toReal_ofReal hs₁.le,
    ENNReal.toReal_ofReal (show 0 ≤ ∫ x in eigenSlab p a b, ‖(p.2 : RN N → RN N) x‖ from
      integral_nonneg (fun x => norm_nonneg ((p.2 : RN N → RN N) x)))] at hreal
  exact hreal

end FourthRatio
end
