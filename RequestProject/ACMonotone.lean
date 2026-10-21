module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Topology.Sequences
public import Mathlib.Tactic

/-! # Monotonicity for locally absolutely continuous functions -/

@[expose] public section

open Set Filter MeasureTheory Topology

namespace FourthRatio

/-- A locally absolutely continuous function with nonnegative derivative almost
everywhere on an open interval is nondecreasing there. -/
theorem monotoneOn_of_locally_ac_deriv_nonneg {f : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ x ∈ Ioo a b, ∀ y ∈ Ioo a b, AbsolutelyContinuousOnInterval f x y)
    (hd : ∀ᵐ s, s ∈ Ioo a b → 0 ≤ deriv f s) :
    MonotoneOn f (Ioo a b) := by
  intro x hx y hy hxy
  have hn : 0 ≤ᵐ[volume.restrict (Icc x y)] deriv f := by
    apply (ae_restrict_iff' measurableSet_Icc).mpr
    filter_upwards [hd] with s hs hsin
    exact hs ⟨hx.1.trans_le hsin.1, hsin.2.trans_lt hy.2⟩
  have hi := intervalIntegral.integral_nonneg_of_ae_restrict hxy hn
  rw [(hf x hx y hy).integral_deriv_eq_sub] at hi
  exact sub_nonneg.mp hi

/-- A monotone function on a positive interval is at least its right-hand
limit at zero. The function need not have a continuous value at zero. -/
theorem right_limit_le_of_monotoneOn {f : ℝ → ℝ} {R l : ℝ}
    (hm : MonotoneOn f (Ioo 0 R)) (hl : Tendsto f (𝓝[>] 0) (𝓝 l))
    {s : ℝ} (hs : s ∈ Ioo 0 R) : l ≤ f s := by
  have hc : (0 : ℝ) ∈ closure (Ioo 0 s) := by
    rw [closure_Ioo hs.1.ne]
    exact ⟨le_rfl, hs.1.le⟩
  obtain ⟨v, hv, hlim⟩ := mem_closure_iff_seq_limit.mp hc
  have hvlim : Tendsto v atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall (fun n => (hv n).1)⟩
  have hle : ∀ n, f (v n) ≤ f s := fun n =>
    hm ⟨(hv n).1, (hv n).2.trans hs.2⟩ hs (hv n).2.le
  exact le_of_tendsto (hl.comp hvlim) (Eventually.of_forall hle)

end FourthRatio
