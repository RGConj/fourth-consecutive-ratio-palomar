module

public import RequestProject.Sharpness
public import RequestProject.PPWGap

/-!
# Unconditional forms

The conditional reductions are instantiated with the proved PPW inequality
and equality case. The Bessel input is proved in `BesselABComplete`; Chiti
mass concentration is proved in `ChitiGeneral` and assembled in `PPWDeep`.
`fourth_ratio_of_deep_inputs` also exposes the modular conditional reduction.
-/

@[expose] public section

open Metric

noncomputable section

namespace FourthRatio

variable {N : ℕ}

/-- **Theorem 5.0 (Fourth consecutive ratio).** For every bounded domain `Ω ⊂ ℝ^N`,
`λ₅(Ω) < C_N λ₄(Ω)`. -/
theorem fourth_ratio (hN : 2 ≤ N) {Ω : Set (RN N)} (hΩ : IsDomain Ω) :
    eigenvalue Ω 5 < CN N * eigenvalue Ω 4 :=
  fourth_ratio_of_ppw (ppwInequality_holds hN) (ppwEqualityCase_holds hN) hN hΩ

/-- **Theorem 5.0 from the two deep inputs** (sorry-free): the Ashbaugh–Benguria Bessel function
lemmas for `ν = N/2 - 1` and the mass-concentration form of Chiti's comparison theorem imply
`λ₅(Ω) < C_N λ₄(Ω)`. -/
theorem fourth_ratio_of_deep_inputs (hN : 2 ≤ N) (hAB : ABBesselLemmas ((N : ℝ) / 2 - 1))
    (hCh : ChitiMass N) {Ω : Set (RN N)} (hΩ : IsDomain Ω) :
    eigenvalue Ω 5 < CN N * eigenvalue Ω 4 :=
  fourth_ratio_of_ppw (ppw_of_deep_inputs hN hAB hCh).1 (ppw_of_deep_inputs hN hAB hCh).2 hN hΩ

/-- **Theorem 5.2 (higher ratio), PPW-free entry.** `λ₄(Ω) < C_N λ₂(Ω)`. -/
theorem higher_ratio_uncond (hN : 2 ≤ N) {D : Set (RN N)} (hD : IsDomain D) :
    eigenvalue D 4 < CN N * eigenvalue D 2 :=
  higher_ratio (ppwInequality_holds hN) (ppwEqualityCase_holds hN) hN hD

/-- **Corollary (upper bound), PPW-free entry.** `λ_{m+1} ≤ C_N λ_m` for `1 ≤ m ≤ 4` and every
nonempty bounded open set. -/
theorem cor_upper_uncond (hN : 2 ≤ N) {m : ℕ} (hm1 : 1 ≤ m) (hm4 : m ≤ 4) {D : Set (RN N)}
    (hD : IsAdmissible D) : eigenvalue D (m + 1) ≤ CN N * eigenvalue D m :=
  cor_upper (ppwInequality_holds hN) (ppwEqualityCase_holds hN) hN hm1 hm4 hD

/-- **Corollary (equality case), PPW-free entry.** -/
theorem cor_equality_uncond (hN : 2 ≤ N) {m : ℕ} (hm1 : 1 ≤ m) (hm4 : m ≤ 4) {D : Set (RN N)}
    (hD : IsAdmissible D) :
    eigenvalue D (m + 1) = CN N * eigenvalue D m ↔
      ∃ (x y : Fin m → RN N) (R : ℝ), 0 < R ∧ (∀ i, x i ∈ D) ∧
        Pairwise (fun i j => connectedComponentIn D (x i) ≠ connectedComponentIn D (x j)) ∧
        (∀ i, H (connectedComponentIn D (x i)) = H (ball (y i) R) ∧
          eigenvalue (connectedComponentIn D (x i)) 1 = eigenvalue D m) ∧
        ∀ z ∈ D, (∀ i, connectedComponentIn D z ≠ connectedComponentIn D (x i)) →
          CN N * eigenvalue D m ≤ eigenvalue (connectedComponentIn D z) 1 :=
  cor_equality (ppwInequality_holds hN) (ppwEqualityCase_holds hN) hN hm1 hm4 hD

/-- **Corollary (sharpness), PPW-free entry.** -/
theorem cor_sharpness_uncond (hN : 2 ≤ N) {m : ℕ} (hm1 : 1 ≤ m) (hm4 : m ≤ 4) :
    IsLUB {r : ℝ | ∃ Ω : Set (RN N), IsDomain Ω ∧ HasSmoothBoundary Ω ∧
      r = eigenvalue Ω (m + 1) / eigenvalue Ω m} (CN N) :=
  cor_sharpness (ppwInequality_holds hN) (ppwEqualityCase_holds hN) hN hm1 hm4

end FourthRatio

end
