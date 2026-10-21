module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Tactic

/-!
# A quotient comparison for Volterra differential inequalities

This is a one-dimensional comparison criterion. Application to a rearranged
Dirichlet eigenfunction still requires proving its Talenti inequality and
its endpoint regularity; those are not assumptions silently discharged here.
-/

@[expose] public section

open Set

namespace FourthRatio

/-- A Volterra differential supersolution divided by the positive comparison
solution is nondecreasing. Only the Wronskian needs continuity at the origin. -/
theorem volterra_quotient_monotone {u z U Z u1 z1 k : ℝ → ℝ} {R : ℝ}
    (hR : 0 < R)
    (hu : ∀ s ∈ Ioo 0 R, HasDerivAt u (u1 s) s)
    (hz : ∀ s ∈ Ioo 0 R, HasDerivAt z (z1 s) s)
    (hU : ∀ s ∈ Ioo 0 R, HasDerivAt U (u s) s)
    (hZ : ∀ s ∈ Ioo 0 R, HasDerivAt Z (z s) s)
    (hU0 : U 0 = 0) (hZ0 : Z 0 = 0)
    (hwc : ContinuousOn (fun s => u s * Z s - U s * z s) (Ico 0 R))
    (hk : ∀ s ∈ Ioo 0 R, 0 ≤ k s)
    (hZp : ∀ s ∈ Ioo 0 R, 0 ≤ Z s)
    (hzp : ∀ s ∈ Ioo 0 R, 0 < z s)
    (hui : ∀ s ∈ Ioo 0 R, -(k s * U s) ≤ u1 s)
    (hze : ∀ s ∈ Ioo 0 R, z1 s = -(k s * Z s)) :
    MonotoneOn (fun s => u s / z s) (Ioo 0 R) := by
  let W : ℝ → ℝ := fun s => u s * Z s - U s * z s
  let W1 : ℝ → ℝ := fun s => u1 s * Z s - U s * z1 s
  have hWd : ∀ s ∈ Ioo 0 R, HasDerivAt W (W1 s) s := by
    intro s hs
    refine (((hu s hs).mul (hZ s hs)).sub ((hU s hs).mul (hz s hs))).congr_deriv ?_
    dsimp only [W1]
    ring
  have hW1 : ∀ s ∈ Ioo 0 R, 0 ≤ W1 s := by
    intro s hs
    have hm := mul_le_mul_of_nonneg_right (hui s hs) (hZp s hs)
    dsimp only [W1]
    rw [hze s hs]
    nlinarith
  have hWm : MonotoneOn W (Ico 0 R) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := W1) (convex_Ico _ _)
      hwc ?_ ?_
    · intro s hs
      rw [interior_Ico] at hs
      exact (hWd s hs).hasDerivWithinAt
    · intro s hs
      rw [interior_Ico] at hs
      exact hW1 s hs
  have hWpos : ∀ s ∈ Ioo 0 R, 0 ≤ W s := by
    intro s hs
    have hm := hWm ⟨le_rfl, hR⟩ ⟨hs.1.le, hs.2⟩ hs.1.le
    simpa only [W, hU0, hZ0, mul_zero, zero_mul, sub_zero] using hm
  let q1 : ℝ → ℝ := fun s => (u1 s * z s - u s * z1 s) / z s ^ 2
  have hqd : ∀ s ∈ Ioo 0 R, HasDerivAt (fun s => u s / z s) (q1 s) s := by
    intro s hs
    exact (hu s hs).div (hz s hs) (hzp s hs).ne'
  refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := q1) (convex_Ioo _ _) ?_ ?_ ?_
  · intro s hs
    exact (hqd s hs).continuousAt.continuousWithinAt
  · intro s hs
    rw [interior_Ioo] at hs
    exact (hqd s hs).hasDerivWithinAt
  · intro s hs
    rw [interior_Ioo] at hs
    dsimp only [q1]
    apply div_nonneg ?_ (sq_nonneg _)
    have hm := mul_le_mul_of_nonneg_right (hui s hs) (hzp s hs).le
    have hw := mul_nonneg (hk s hs) (hWpos s hs)
    dsimp only [W] at hw
    rw [hze s hs]
    nlinarith

end FourthRatio
