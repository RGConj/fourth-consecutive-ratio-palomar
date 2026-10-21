module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Initial-coordinate mass as an actual integral primitive -/

@[expose] public section
open Set MeasureTheory Filter Topology
noncomputable section
namespace FourthRatio

def initialMass (f : ℝ → ℝ) (s : ℝ) : ℝ := ∫ t in Ioo (0 : ℝ) s, f t

lemma initialMass_eq_primitive (f : ℝ → ℝ) {s : ℝ} (hs : 0 ≤ s) :
    initialMass f s = ∫ t in (0 : ℝ)..s, (Ioi (0 : ℝ)).indicator f t := by
  rw [intervalIntegral.integral_of_le hs, integral_Ioc_eq_integral_Ioo]
  symm
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  exact indicator_of_mem ht.1 f

/-- Integrability on the positive axis gives continuity of the initial mass. -/
theorem initialMass_continuousOn {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi (0 : ℝ))) :
    ContinuousOn (initialMass f) (Ioi (0 : ℝ)) := by
  have hg := hf.integrable_indicator measurableSet_Ioi
  exact (hg.continuous_primitive 0).continuousOn.congr (fun s hs => initialMass_eq_primitive f hs.le)

/-- At continuity points the actual initial-coordinate integral differentiates
to its density. -/
theorem initialMass_hasDerivAt {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi (0 : ℝ)))
    (hfm : Measurable f) {s : ℝ} (hs : 0 < s) (hfs : ContinuousAt f s) :
    HasDerivAt (initialMass f) (f s) s := by
  let g := (Ioi (0 : ℝ)).indicator f
  have hgi : Integrable g := hf.integrable_indicator measurableSet_Ioi
  have hgf : g =ᶠ[𝓝 s] f := by
    filter_upwards [isOpen_Ioi.mem_nhds hs] with t ht
    exact indicator_of_mem ht f
  have hgc : ContinuousAt g s := hfs.congr_of_eventuallyEq hgf
  have hgm : StronglyMeasurableAtFilter g (𝓝 s) :=
    (hfm.indicator measurableSet_Ioi).stronglyMeasurable.stronglyMeasurableAtFilter
  have hd := intervalIntegral.integral_hasDerivAt_right (a := (0 : ℝ)) hgi.intervalIntegrable hgm hgc
  have heq : initialMass f =ᶠ[𝓝 s] (fun u => ∫ t in (0 : ℝ)..u, g t) := by
    filter_upwards [isOpen_Ioi.mem_nhds hs] with t ht
    exact initialMass_eq_primitive f ht.le
  have hz : g s = f s := indicator_of_mem hs f
  rw [hz] at hd
  exact hd.congr_of_eventuallyEq heq

end FourthRatio
end
