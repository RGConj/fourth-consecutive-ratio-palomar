module

public import Mathlib

/-!
# Palomar challenge: Theorem 5.0 of Shi–Tang, *A sharp bound for the fourth consecutive
Dirichlet eigenvalue ratio*

The statements at the end of this file give both the multiplication form
`FourthRatio.fourth_consecutive_ratio` and the exact source quotient form
`FourthRatio.fourth_consecutive_ratio_div`.

## How the objects of the paper are modelled (all definitions below use only Mathlib)

* `RN N = EuclideanSpace ℝ (Fin N)` is `ℝ^N` with Lebesgue measure `volume`.
* `H D` is `H₀¹(D)`: the closure, in `L²(ℝ^N) × L²(ℝ^N; ℝ^N)`, of the graph
  `{(φ, ∇φ) : φ ∈ C_c^∞(ℝ^N), tsupport φ ⊆ D}`; elements are zero-extended to `ℝ^N`.
  The product maximum norm is equivalent to the usual `H¹` norm, giving the same closure.
* `qf v w = ∫ ∇v·∇w`, `l2 v w = ∫ v w`, `rayleigh v = qf v v / l2 v v`.
* `eigenvalue D j = inf_{V ≤ H D, dim V = j} sup_{0 ≠ v ∈ V} rayleigh v` (min–max), exactly
  Definition 1 of the paper.
* `besselJ ν x` is the series of the Bessel function of the first kind, `besselZero ν k` its
  `k`-th positive zero `j_{ν,k}`, and `CN N = j_{N/2,1}² / j_{N/2-1,1}²`.
* `IsAdmissible D`: `D` nonempty, bounded, open; `IsDomain D`: additionally connected.
-/

@[expose] public section

open MeasureTheory InnerProductSpace
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

/-- The ambient Euclidean space `ℝ^N`. -/
abbrev RN (N : ℕ) := EuclideanSpace ℝ (Fin N)

/-- Scalar `L²(ℝ^N)`. -/
abbrev L2 (N : ℕ) := Lp ℝ 2 (volume : Measure (RN N))

/-- Vector valued `L²(ℝ^N; ℝ^N)` (the space where weak gradients live). -/
abbrev L2v (N : ℕ) := Lp (RN N) 2 (volume : Measure (RN N))

/-- The ambient space of pairs `(function, gradient)`; `H¹(ℝ^N)` is modelled inside it. -/
abbrev Amb (N : ℕ) := L2 N × L2v N

variable {N : ℕ}

/-- `D ∈ 𝒪_N`: a nonempty bounded open subset of `ℝ^N`. -/
def IsAdmissible (D : Set (RN N)) : Prop :=
  IsOpen D ∧ D.Nonempty ∧ Bornology.IsBounded D

/-- A *domain*: a connected member of `𝒪_N`. -/
def IsDomain (D : Set (RN N)) : Prop :=
  IsAdmissible D ∧ IsConnected D

/-- The graph `{(φ, ∇φ)}` of the gradient on test functions `φ ∈ C_c^∞(D)`. -/
def testGraph (D : Set (RN N)) : Set (Amb N) :=
  {p | ∃ φ : RN N → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧ HasCompactSupport φ ∧
      tsupport φ ⊆ D ∧ (p.1 : RN N → ℝ) =ᵐ[volume] φ ∧
      (p.2 : RN N → RN N) =ᵐ[volume] gradient φ}

/-- `H_D = H₀¹(D)`: the `H¹`-closure of `C_c^∞(D)` (functions are zero-extended to `ℝ^N`). -/
def H (D : Set (RN N)) : Submodule ℝ (Amb N) :=
  (Submodule.span ℝ (testGraph D)).topologicalClosure

/-- The Dirichlet form `q(v,w) = ∫ ∇v · ∇w`. -/
def qf (v w : Amb N) : ℝ := ⟪v.2, w.2⟫

/-- The `L²` inner product `⟨v,w⟩ = ∫ v w`. -/
def l2 (v w : Amb N) : ℝ := ⟪v.1, w.1⟫

/-- The Rayleigh quotient `q(v,v)/‖v‖²`. -/
def rayleigh (v : Amb N) : ℝ := qf v v / l2 v v

/-- The `j`-th Dirichlet eigenvalue, defined by the min–max formula
`λ_j(D) = inf_{V ⊆ H_D, dim V = j} sup_{0 ≠ v ∈ V} R(v)` (meaningful for `j ≥ 1`). -/
def eigenvalue (D : Set (RN N)) (j : ℕ) : ℝ :=
  sInf ((fun V : Submodule ℝ (Amb N) => sSup (rayleigh '' {v | v ∈ V ∧ v ≠ 0})) ''
    {V | V ≤ H D ∧ Module.finrank ℝ V = j})

/-! ### Bessel functions and the PPW constant -/

/-- The Bessel function of the first kind,
`J_ν(x) = ∑_{m ≥ 0} (-1)^m / (m! Γ(m+ν+1)) (x/2)^{2m+ν}` (used for `x > 0`). -/
def besselJ (ν x : ℝ) : ℝ :=
  ∑' m : ℕ, (-1 : ℝ) ^ m / ((m.factorial : ℝ) * Real.Gamma (m + ν + 1)) *
    (x / 2) ^ (2 * (m : ℝ) + ν)

/-- `besselZero ν k = j_{ν,k}`, the `k`-th positive zero of `J_ν` (for `k ≥ 1`);
`besselZero ν 0 = 0` is a convenient starting value. -/
def besselZero (ν : ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => sInf {x : ℝ | besselZero ν k < x ∧ besselJ ν x = 0}

/-- The Payne–Pólya–Weinberger constant `C_N = j_{N/2,1}² / j_{N/2-1,1}²`. -/
def CN (N : ℕ) : ℝ :=
  besselZero ((N : ℝ) / 2) 1 ^ 2 / besselZero ((N : ℝ) / 2 - 1) 1 ^ 2

/-- **Theorem 5.0 (Shi–Tang).** For `N ≥ 2` and every bounded domain `Ω ⊂ ℝ^N`,
`λ₅(Ω) < C_N λ₄(Ω)`. -/
theorem fourth_consecutive_ratio (N : ℕ) (hN : 2 ≤ N) (Ω : Set (RN N)) (hΩ : IsDomain Ω) :
    eigenvalue Ω 5 < CN N * eigenvalue Ω 4 := by
  sorry

/-- The source theorem in its exact quotient form. -/
theorem fourth_consecutive_ratio_div (N : ℕ) (hN : 2 ≤ N)
    (Ω : Set (RN N)) (hΩ : IsDomain Ω) :
    eigenvalue Ω 5 / eigenvalue Ω 4 < CN N := by
  sorry

end FourthRatio

end
