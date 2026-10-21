module

public import RequestProject.ScalarCoarea
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Coarea for the smooth compactly supported functions used in the Sobolev closure

These results apply to genuine smooth functions and their ordinary gradients.
They do not yet extend the comparison to arbitrary elements of H₀¹.
-/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal

namespace FourthRatio

lemma gradient_norm_eq_fderiv_norm {N : ℕ}
    (f : EuclideanSpace ℝ (Fin N) → ℝ) (x : EuclideanSpace ℝ (Fin N)) :
    ‖gradient f x‖ = ‖fderiv ℝ f x‖ := by
  simp only [gradient, LinearIsometryEquiv.norm_map]

/-- Weighted coarea for a compactly supported C¹ function. -/
theorem smooth_compact_coarea {N : ℕ} {f : EuclideanSpace ℝ (Fin N) → ℝ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (w : EuclideanSpace ℝ (Fin N) → ℝ≥0∞) (hw : Measurable w) :
    (∫⁻ x, ENNReal.ofReal ‖gradient f x‖ * w x) =
      ∫⁻ t : ℝ, ProbabilityTheory.scalarCoareaFiber f w t := by
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hf one_ne_zero
  simpa only [ProbabilityTheory.scalarJacobian, gradient_norm_eq_fderiv_norm] using
    ProbabilityTheory.LipschitzWith.scalarCoareaFormula hC w hw

/-- The gradient energy on a level slab is the integral of gradient norms on
its level fibers. -/
theorem smooth_compact_coarea_energy_slab {N : ℕ}
    {f : EuclideanSpace ℝ (Fin N) → ℝ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (a b : ℝ) :
    (∫⁻ x in f ⁻¹' Ioc a b, (ENNReal.ofReal ‖gradient f x‖) ^ 2) =
      ∫⁻ t in Ioc a b,
        ProbabilityTheory.scalarCoareaFiber f (fun x => ENNReal.ofReal ‖gradient f x‖) t := by
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hf one_ne_zero
  have hg : Continuous (gradient f) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin N))).symm.continuous.comp
      (hf.continuous_fderiv one_ne_zero)
  have hw : Measurable (fun x => ENNReal.ofReal ‖gradient f x‖) :=
    ENNReal.measurable_ofReal.comp hg.norm.measurable
  simpa only [ProbabilityTheory.scalarJacobian, gradient_norm_eq_fderiv_norm, pow_two] using
    ProbabilityTheory.LipschitzWith.scalarCoarea_setLIntegral_slab hC
      (fun x => ENNReal.ofReal ‖gradient f x‖) hw a b

end FourthRatio
