module

public import RequestProject.ACMonotone
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Volterra comparison with almost-everywhere derivatives

This criterion uses local absolute continuity and a true right-hand limit.
It is suitable for rearrangement arguments, where derivatives exist only
almost everywhere. The geometric Talenti inequality is still a separate input.
-/

@[expose] public section

open Set Filter MeasureTheory Topology

namespace FourthRatio

/-- The positive comparison quotient is monotone under a Volterra inequality
holding almost everywhere, provided the Wronskian and quotient are locally
absolutely continuous and the Wronskian tends to zero at the left endpoint. -/
theorem ac_volterra_quotient_monotone {u z U Z u1 z1 k : ℝ → ℝ} {R : ℝ}
    (hu : ∀ᵐ s, s ∈ Ioo 0 R → HasDerivAt u (u1 s) s)
    (hz : ∀ᵐ s, s ∈ Ioo 0 R → HasDerivAt z (z1 s) s)
    (hU : ∀ᵐ s, s ∈ Ioo 0 R → HasDerivAt U (u s) s)
    (hZ : ∀ᵐ s, s ∈ Ioo 0 R → HasDerivAt Z (z s) s)
    (hWac : ∀ x ∈ Ioo 0 R, ∀ y ∈ Ioo 0 R,
      AbsolutelyContinuousOnInterval (fun s => u s * Z s - U s * z s) x y)
    (hQac : ∀ x ∈ Ioo 0 R, ∀ y ∈ Ioo 0 R,
      AbsolutelyContinuousOnInterval (fun s => u s / z s) x y)
    (hWlim : Tendsto (fun s => u s * Z s - U s * z s) (𝓝[>] 0) (𝓝 0))
    (hk : ∀ s ∈ Ioo 0 R, 0 ≤ k s)
    (hZp : ∀ s ∈ Ioo 0 R, 0 ≤ Z s)
    (hzp : ∀ s ∈ Ioo 0 R, 0 < z s)
    (hui : ∀ᵐ s, s ∈ Ioo 0 R → -(k s * U s) ≤ u1 s)
    (hze : ∀ᵐ s, s ∈ Ioo 0 R → z1 s = -(k s * Z s)) :
    MonotoneOn (fun s => u s / z s) (Ioo 0 R) := by
  let W : ℝ → ℝ := fun s => u s * Z s - U s * z s
  have hWd : ∀ᵐ s, s ∈ Ioo 0 R → 0 ≤ deriv W s := by
    filter_upwards [hu, hz, hU, hZ, hui, hze] with s hu hz hU hZ hui hze hs
    have hd : HasDerivAt W
        ((u1 s * Z s + u s * z s) - (u s * z s + U s * z1 s)) s :=
      ((hu hs).mul (hZ hs)).sub ((hU hs).mul (hz hs))
    rw [hd.deriv, hze hs]
    have hm := mul_le_mul_of_nonneg_right (hui hs) (hZp s hs)
    nlinarith
  have hWm : MonotoneOn W (Ioo 0 R) :=
    monotoneOn_of_locally_ac_deriv_nonneg hWac hWd
  have hWp : ∀ s ∈ Ioo 0 R, 0 ≤ W s := fun s hs =>
    right_limit_le_of_monotoneOn hWm hWlim hs
  have hQd : ∀ᵐ s, s ∈ Ioo 0 R → 0 ≤ deriv (fun s => u s / z s) s := by
    filter_upwards [hu, hz, hui, hze] with s hu hz hui hze hs
    have hd := (hu hs).div (hz hs) (hzp s hs).ne'
    change 0 ≤ deriv (u / z) s
    rw [hd.deriv]
    apply div_nonneg ?_ (sq_nonneg _)
    have hm := mul_le_mul_of_nonneg_right (hui hs) (hzp s hs).le
    have hw := mul_nonneg (hk s hs) (hWp s hs)
    dsimp only [W] at hw
    rw [hze hs]
    nlinarith
  exact monotoneOn_of_locally_ac_deriv_nonneg hQac hQd

end FourthRatio
