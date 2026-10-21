module

public import RequestProject.SobolevSmoothChain
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! # Stampacchia's lemma on arbitrary level sets

A bounded smooth scalar chain with a simple zero at the desired level reduces
this to the already proved zero-level lemma.
-/

@[expose] public section
open MeasureTheory Filter Topology
open scoped RealInnerProductSpace ENNReal
noncomputable section
namespace FourthRatio

def levelSineChain (a : ℝ) : SmoothScalarChain where
  toFun := fun t => Real.sin ((Real.pi / a) * t)
  derivFun := fun t => Real.cos ((Real.pi / a) * t) * (Real.pi / a)
  smooth := Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)
  zero := by simp
  hasDeriv := fun t => by
    simpa only [Function.comp_def, mul_one] using (Real.hasDerivAt_sin ((Real.pi / a) * t)).comp t
      ((hasDerivAt_id t).const_mul (Real.pi / a))
  deriv_continuous := (Real.continuous_cos.comp (continuous_const.mul continuous_id)).mul continuous_const
  bound := |Real.pi / a|
  bound_nonneg := abs_nonneg _
  lipschitz := fun s t => by
    calc
      _ ≤ |(Real.pi / a) * s - (Real.pi / a) * t| := Real.abs_sin_sub_sin_le _ _
      _ = _ := by rw [← mul_sub, abs_mul]
  deriv_bound := fun t => by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (abs_nonneg _)).trans_eq (one_mul _)

/-- A genuine weak gradient vanishes a.e. on every scalar level set. -/
theorem grad_eq_zero_on_level {N : ℕ} {D : Set (RN N)} {p : Amb N}
    (hp : p ∈ H D) (a : ℝ) :
    ∀ᵐ x, (p.1 : RN N → ℝ) x = a → (p.2 : RN N → RN N) x = 0 := by
  by_cases ha : a = 0
  · subst a
    exact grad_eq_zero_of_eq_zero hp
  let F := levelSineChain a
  have hFa : F.toFun a = 0 := by
    change Real.sin ((Real.pi / a) * a) = 0
    rw [div_mul_cancel₀ _ ha, Real.sin_pi]
  have hdFa : F.derivFun a ≠ 0 := by
    change Real.cos ((Real.pi / a) * a) * (Real.pi / a) ≠ 0
    rw [div_mul_cancel₀ _ ha, Real.cos_pi]
    exact mul_ne_zero (by norm_num) (div_ne_zero Real.pi_ne_zero ha)
  have hzero := grad_eq_zero_of_eq_zero (chainPair_mem_H F hp)
  filter_upwards [hzero, chainPair_fst_ae F p, chainPair_snd_ae F p] with x hz hf hg hxa
  have hval : ((chainPair F p).1 : RN N → ℝ) x = 0 := by rw [hf, hxa, hFa]
  have hgrad := hz hval
  rw [hg, hxa] at hgrad
  exact (smul_eq_zero.mp hgrad).resolve_left hdFa

end FourthRatio
end
