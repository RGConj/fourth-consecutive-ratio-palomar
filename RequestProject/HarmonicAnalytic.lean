module

public import RequestProject.WeylDeriv
public import RequestProject.AnalyticBound

/-!
# Harmonic functions are real analytic

* `HarmOn.analyticOnNhd` — a smooth harmonic function on an open set is real analytic there
  (interior derivative estimates + Taylor's formula);
* `weakHarmonic_analytic` — a weakly harmonic function agrees almost everywhere on `U` with a
  function which is real analytic on `U`.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Function Set
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

variable {n : ℕ}

/-- Smooth harmonic functions are real analytic. -/
theorem HarmOn.analyticOnNhd (hn : 1 ≤ n) {U : Set (RN n)} (hU : IsOpen U) {f : RN n → ℝ}
    (hf : HarmOn U f) : AnalyticOnNhd ℝ f U := by
  intro x hx
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU x hx
  set r := ε / 2
  have hr : 0 < r := by positivity
  have hsub : closedBall x r ⊆ U := (closedBall_subset_ball (by simp only [r]; linarith)).trans hεU
  obtain ⟨M, hM⟩ := (isCompact_closedBall x r).exists_bound_of_continuousOn
    (hf.1.continuousOn.mono hsub)
  have hb := harmonic_iteratedFDeriv_bound hn hU hf hr hsub (M := M) fun z hz => by
    rw [← Real.norm_eq_abs]; exact hM z hz
  exact analyticAt_of_iteratedFDeriv_bound (by positivity : (0 : ℝ) < r / 2)
    (hf.1.mono ((ball_subset_closedBall.trans
      (closedBall_subset_closedBall (by linarith))).trans hsub)) hb

/-- **Weyl's lemma, analytic form.** A weakly harmonic function on an open set `U` agrees almost
everywhere on `U` with a function which is real analytic on `U`. -/
theorem weakHarmonic_analytic (hn : 1 ≤ n) {U : Set (RN n)} (hU : IsOpen U) {w : RN n → ℝ}
    (hw : WeakHarmonic U w) :
    ∃ g : RN n → ℝ, AnalyticOnNhd ℝ g U ∧ ∀ᵐ x, x ∈ U → w x = g x := by
  obtain ⟨h1, h2, h3⟩ := weyl hn hU hw
  exact ⟨weylRep n w, HarmOn.analyticOnNhd hn hU ⟨h1, h2⟩, h3⟩

end FourthRatio

end
