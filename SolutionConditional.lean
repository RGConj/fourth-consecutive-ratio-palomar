module

public import RequestProject.MainTheorem

/-!
# Palomar solution for `ChallengeConditional.lean`

Theorem 5.0 assuming the PPW inequality and its equality case.  This proof is free of `sorry`:
`#print axioms` lists only `propext`, `Classical.choice`, `Quot.sound`.  It does not import
`RequestProject/PPWGap.lean`.
-/

@[expose] public section

noncomputable section

namespace FourthRatio

/-- **Theorem 5.0 (Shi–Tang), conditional on External theorem 2.3.** -/
theorem fourth_consecutive_ratio_of_ppw (N : ℕ) (hppw : PPWInequality N)
    (hppwEq : PPWEqualityCase N) (hN : 2 ≤ N) (Ω : Set (RN N)) (hΩ : IsDomain Ω) :
    eigenvalue Ω 5 < CN N * eigenvalue Ω 4 :=
  fourth_ratio_of_ppw hppw hppwEq hN hΩ

end FourthRatio

end
