module

public import RequestProject.PPWProof

/-!
# The Payne–Pólya–Weinberger inequality and its equality case

External theorem 2.3 of the manuscript is assembled in `PPWProof` from the
proved Ashbaugh–Benguria Bessel lemmas and Chiti mass concentration.
The core argument also provides conditional reductions with explicit PPW
hypotheses; `Unconditional` supplies the theorems proved here.
-/

@[expose] public section

open MeasureTheory Metric

noncomputable section

namespace FourthRatio

variable {N : ℕ}

/-- **PPW inequality (Ashbaugh–Benguria), for bounded domains.**
(The extension to all nonempty bounded open sets is `PPWInequality.admissible`.) -/
theorem ext_ppw (hN : 2 ≤ N) {D : Set (RN N)} (hD : IsDomain D) :
    eigenvalue D 2 ≤ CN N * eigenvalue D 1 :=
  ppw_inequality hN hD

/-- **PPW equality case.** For a domain with equality there is a ball with the same first
eigenvalue and the same form domain `H₀¹(D) = H₀¹(B)` (as subspaces of `H¹(ℝ^N)`). -/
theorem ext_ppw_equality (hN : 2 ≤ N) {D : Set (RN N)} (hD : IsDomain D)
    (heq : eigenvalue D 2 = CN N * eigenvalue D 1) :
    ∃ (y : RN N) (R : ℝ), 0 < R ∧ eigenvalue (ball y R) 1 = eigenvalue D 1 ∧
      H D = H (ball y R) :=
  ppw_equality hN hD heq

lemma ppwInequality_holds (hN : 2 ≤ N) : PPWInequality N := fun _ hD => ext_ppw hN hD

lemma ppwEqualityCase_holds (hN : 2 ≤ N) : PPWEqualityCase N :=
  fun _ hD heq => ext_ppw_equality hN hD heq

end FourthRatio

end
