module

public import RequestProject.MainLineField
public import RequestProject.DegLineField

/-!
# The degree contradiction and the main theorem (Proposition 5.7, Theorem 5.0)
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Function
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

variable {N : ℕ}

namespace Setup

variable (S : Setup N)

/-- **Proposition 5.7 (The degree contradiction).** The standing assumptions are impossible. -/
theorem prop_degree_contradiction (S : Setup N) : False := by
  obtain ⟨O, hO, hKO, hgood⟩ := S.lemma_stable
  have he4 : ‖e4‖ = 1 := by simp [e4]
  have hneg : 0 < S.Fbal (-e4) := by rw [Fbal_neg]; linarith [S.Fbal_e4]
  obtain ⟨M, hM, hMc, hno⟩ := Degree.degree_no_line_field e4 he4 S.Fbal S.Fbal_continuousOn
    S.Fbal_e4 hneg O hO (fun u hu hF => hKO ⟨hu, hF⟩)
  exact hno (S.lemma_line_field hgood hM hMc)

end Setup

/-- **Theorem 5.0 (Fourth consecutive ratio), conditional form.** Assuming the PPW inequality and
its equality case (External theorem 2.3 of the paper, not proved in this project), for every
bounded domain `Ω ⊂ ℝ^N`, `λ₅(Ω) < C_N λ₄(Ω)`.  This theorem is free of `sorry`. -/
theorem fourth_ratio_of_ppw (hppw : PPWInequality N) (hppwEq : PPWEqualityCase N) (hN : 2 ≤ N)
    {Ω : Set (RN N)} (hΩ : IsDomain Ω) :
    eigenvalue Ω 5 < CN N * eigenvalue Ω 4 := by
  by_contra h
  obtain ⟨S, -⟩ := exists_setup hppw hppwEq hN hΩ (not_lt.mp h)
  exact S.prop_degree_contradiction

end FourthRatio

end
