module

public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# The derivative of the regular divided difference at its base point

This elementary identity is useful when dividing out the common simple zeros
of two Bessel profiles. It is proved by differentiating the exact product
identity twice, rather than assigning a value to a singular quotient.
-/

@[expose] public section

open Set

noncomputable section

namespace FourthRatio

/-- The regular slope of an analytic function has derivative `f''(a)/2` at
its base point. The supplied derivative functions are genuine derivatives. -/
lemma hasDerivAt_dslope_center {f f1 f2 : ℝ → ℝ}
    (hf : AnalyticOnNhd ℝ f univ)
    (hF : ∀ t, HasDerivAt f (f1 t) t) (hF1 : ∀ t, HasDerivAt f1 (f2 t) t)
    (a : ℝ) : HasDerivAt (dslope f a) (f2 a / 2) a := by
  set P := dslope f a
  set P1 := deriv P
  have hPa : ∀ t, AnalyticAt ℝ P t := fun t => (hf t trivial).dslope a
  have hPd : ∀ t, HasDerivAt P (P1 t) t := fun t => (hPa t).differentiableAt.hasDerivAt
  have hP1d : ∀ t, HasDerivAt P1 (deriv P1 t) t := fun t =>
    (hPa t).deriv.differentiableAt.hasDerivAt
  have hfeq : f = fun t => (t - a) * P t + f a := by
    funext t
    have h := sub_smul_dslope f a t
    change (t - a) * P t = f t - f a at h
    linarith
  have hfd : ∀ t, HasDerivAt f (P t + (t - a) * P1 t) t := by
    intro t
    rw [hfeq]
    have h := (((hasDerivAt_id t).sub_const a).mul (hPd t)).add_const (f a)
    convert h using 1 <;> (try rfl) <;> simp only [id] <;> ring
  have hf1eq : f1 = fun t => P t + (t - a) * P1 t := by
    funext t
    exact (hF t).unique (hfd t)
  have hf1d : HasDerivAt f1 (2 * P1 a) a := by
    rw [hf1eq]
    have h := (hPd a).add (((hasDerivAt_id a).sub_const a).mul (hP1d a))
    convert h using 1 <;> (try rfl) <;> norm_num <;> ring
  have heq : f2 a = 2 * P1 a := (hF1 a).unique hf1d
  apply (hPd a).congr_deriv
  linarith

end FourthRatio

end
