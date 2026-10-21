module

public import RequestProject.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! # Exact measure transport to the radial volume coordinate -/

@[expose] public section
open Set MeasureTheory Filter Topology Metric
open scoped ENNReal RealInnerProductSpace
noncomputable section
namespace FourthRatio

variable {N : ℕ}

def radialUnitVolume (N : ℕ) : ℝ := volume.real (ball (0 : RN N) 1)
def radialVolume (N : ℕ) (x : RN N) : ℝ := radialUnitVolume N * ‖x‖ ^ N

lemma radialUnitVolume_pos (hN : 2 ≤ N) : 0 < radialUnitVolume N := by
  haveI : Nontrivial (Fin N) := Fin.nontrivial_iff_two_le.mpr hN
  exact ENNReal.toReal_pos (measure_ball_pos volume (0 : RN N) (by norm_num)).ne' measure_ball_ne_top

lemma continuous_radialVolume (N : ℕ) : Continuous (radialVolume N) :=
  continuous_const.mul (continuous_norm.pow N)

lemma radialVolume_nonneg (hN : 2 ≤ N) (x : RN N) : 0 ≤ radialVolume N x :=
  mul_nonneg (radialUnitVolume_pos hN).le (pow_nonneg (norm_nonneg _) _)

/-- Closed half-lines have exactly their positive length after radial transport. -/
theorem map_radialVolume_Iic (hN : 2 ≤ N) (t : ℝ) :
    (volume.map (radialVolume N)) (Iic t) = ENNReal.ofReal t := by
  haveI : Nontrivial (Fin N) := Fin.nontrivial_iff_two_le.mpr hN
  have hNp : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have homega := radialUnitVolume_pos hN
  rw [Measure.map_apply (continuous_radialVolume N).measurable measurableSet_Iic]
  by_cases ht : 0 ≤ t
  · let r := (t / radialUnitVolume N) ^ (N : ℝ)⁻¹
    have hr : 0 ≤ r := Real.rpow_nonneg (div_nonneg ht homega.le) _
    have hrN : r ^ N = t / radialUnitVolume N := by
      dsimp only [r]
      rw [← Real.rpow_mul_natCast (div_nonneg ht homega.le) (N : ℝ)⁻¹ N,
        inv_mul_cancel₀ hNp, Real.rpow_one]
    have hset : (radialVolume N) ⁻¹' Iic t = closedBall (0 : RN N) r := by
      ext x
      change radialUnitVolume N * ‖x‖ ^ N ≤ t ↔ dist x 0 ≤ r
      rw [dist_zero_right]
      constructor
      · intro hx
        apply (pow_le_pow_iff_left₀ (norm_nonneg x) hr (show N ≠ 0 by omega)).mp
        rw [hrN]
        exact (le_div_iff₀ homega).mpr (by simpa only [mul_comm] using hx)
      · intro hx
        have hp := pow_le_pow_left₀ (norm_nonneg x) hx N
        rw [hrN] at hp
        simpa only [mul_comm] using (le_div_iff₀ homega).mp hp
    rw [hset, Measure.addHaar_closedBall volume (0 : RN N) hr]
    simp only [finrank_euclideanSpace, Fintype.card_fin, hrN]
    rw [← ENNReal.ofReal_toReal (measure_ball_ne_top : volume (ball (0 : RN N) 1) ≠ ∞),
      ← ENNReal.ofReal_mul (div_nonneg ht homega.le)]
    change ENNReal.ofReal ((t / radialUnitVolume N) * radialUnitVolume N) = ENNReal.ofReal t
    rw [div_mul_cancel₀ _ homega.ne']
  · have hset : (radialVolume N) ⁻¹' Iic t = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact ht ((radialVolume_nonneg hN x).trans hx)
    rw [hset, measure_empty, ENNReal.ofReal_eq_zero.mpr (not_le.mp ht).le]

/-- Radial volume pushes Euclidean volume exactly to Lebesgue measure on the
positive volume axis, including the null origin. -/
theorem map_radialVolume (hN : 2 ≤ N) :
    volume.map (radialVolume N) = volume.restrict (Ioi (0 : ℝ)) := by
  let nu := volume.restrict (Ioi (0 : ℝ))
  let mu := volume.map (radialVolume N)
  have hnu : ∀ t : ℝ, nu (Iic t) = ENNReal.ofReal t := by
    intro t
    rw [Measure.restrict_apply measurableSet_Iic]
    have heq : Iic t ∩ Ioi (0 : ℝ) = Ioc 0 t := by ext s; simp [and_comm]
    rw [heq, Real.volume_Ioc, sub_zero]
  have hmu : ∀ t : ℝ, mu (Iic t) = ENNReal.ofReal t := map_radialVolume_Iic hN
  symm
  apply nu.ext_of_Ioc mu
  intro a b hab
  have hnfin : nu (Iic a) ≠ ∞ := by rw [hnu]; exact ENNReal.ofReal_ne_top
  have hmfin : mu (Iic a) ≠ ∞ := by rw [hmu]; exact ENNReal.ofReal_ne_top
  rw [← Iic_sdiff_Iic, measure_sdiff (Iic_subset_Iic.mpr hab.le) nullMeasurableSet_Iic hnfin,
    measure_sdiff (Iic_subset_Iic.mpr hab.le) nullMeasurableSet_Iic hmfin,
    hnu a, hnu b, hmu a, hmu b]

/-- A concrete measure-preserving map for transporting actual radial integrals. -/
theorem radialVolume_measurePreserving (hN : 2 ≤ N) :
    MeasurePreserving (radialVolume N) volume (volume.restrict (Ioi (0 : ℝ))) :=
  ⟨(continuous_radialVolume N).measurable, map_radialVolume hN⟩

end FourthRatio
end
