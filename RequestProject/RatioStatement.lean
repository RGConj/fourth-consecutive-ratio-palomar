module

public import RequestProject.Unconditional

/-!
# The source manuscript's quotient statement

The original main theorem is written as a quotient. These wrappers make the
equivalence with the multiplication statement explicit, using positivity of
the fourth Dirichlet eigenvalue. The unconditional entry supplies the proved
PPW results; the conditional entry exposes its PPW hypotheses.
-/

@[expose] public section

noncomputable section

namespace FourthRatio

/-- The original quotient statement, with the two PPW hypotheses explicit. -/
theorem fourth_consecutive_ratio_div_of_ppw (N : ℕ) (hppw : PPWInequality N)
    (hppwEq : PPWEqualityCase N) (hN : 2 ≤ N) (Ω : Set (RN N)) (hΩ : IsDomain Ω) :
    eigenvalue Ω 5 / eigenvalue Ω 4 < CN N := by
  apply (div_lt_iff₀ (eigenvalue_pos hN hΩ.1 (by omega))).2
  exact fourth_ratio_of_ppw hppw hppwEq hN hΩ

/-- The original unconditional quotient statement. -/
theorem fourth_consecutive_ratio_div (N : ℕ) (hN : 2 ≤ N)
    (Ω : Set (RN N)) (hΩ : IsDomain Ω) :
    eigenvalue Ω 5 / eigenvalue Ω 4 < CN N := by
  apply (div_lt_iff₀ (eigenvalue_pos hN hΩ.1 (by omega))).2
  exact fourth_ratio hN hΩ

end FourthRatio

end
