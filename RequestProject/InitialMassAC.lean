module

public import RequestProject.InitialMass
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

/-! # Local absolute continuity of the actual initial-coordinate mass -/

@[expose] public section
open Set MeasureTheory Filter Topology
noncomputable section
namespace FourthRatio

theorem initialMass_absolutelyContinuous {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi (0 : ℝ)))
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    AbsolutelyContinuousOnInterval (initialMass f) a b := by
  let g := (Ioi (0 : ℝ)).indicator f
  have hgi : Integrable g := hf.integrable_indicator measurableSet_Ioi
  have hIt : IntervalIntegrable g volume (0 : ℝ) (max a b) := hgi.intervalIntegrable
  have hAC := hIt.absolutelyContinuousOnInterval_intervalIntegral (c := (0 : ℝ)) left_mem_uIcc
  have hsub : uIcc a b ⊆ uIcc (0 : ℝ) (max a b) := by
    rw [uIcc_of_le (ha.trans (le_max_left a b))]
    intro s hs
    exact ⟨(le_min ha hb).trans hs.1, hs.2⟩
  apply (hAC.mono hsub).congr
  intro s hs
  have hs0 : 0 ≤ s := (le_min ha hb).trans hs.1
  exact (initialMass_eq_primitive f hs0).symm

end FourthRatio
end
