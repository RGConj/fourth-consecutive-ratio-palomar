module

public import RequestProject.RatioStatement

/-!
# Palomar solution for `Challenge.lean`

The statement uses the actual definitions in `RequestProject/Defs.lean`, copied
in `Challenge.lean` for independent statement comparison. The PPW inequality
and equality case are proved using the Bessel monotonicity and Chiti
mass-concentration theorems; no extra mathematical input is assumed.
The public import also exposes `fourth_consecutive_ratio_div`, the exact
quotient statement of the source theorem.
-/

@[expose] public section

noncomputable section

namespace FourthRatio

/-- **Theorem 5.0 (Shi–Tang).** For `N ≥ 2` and every bounded domain `Ω ⊂ ℝ^N`,
`λ₅(Ω) < C_N λ₄(Ω)`. -/
theorem fourth_consecutive_ratio (N : ℕ) (hN : 2 ≤ N) (Ω : Set (RN N)) (hΩ : IsDomain Ω) :
    eigenvalue Ω 5 < CN N * eigenvalue Ω 4 :=
  fourth_ratio hN hΩ

end FourthRatio

end
