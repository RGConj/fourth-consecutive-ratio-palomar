module

public import RequestProject.BallAnnulus
public import RequestProject.Truncation
public import RequestProject.Cone

/-!
# The fourth consecutive ratio: the contradictory configuration (Section 5.1–5.2)

Throughout, `Ω` is a bounded domain with `C_N λ₄(Ω) ≤ λ₅(Ω)` (the contradictory hypothesis);
we fix real orthonormal eigenfunctions `e₁, …, e₄` (here `e 0, …, e 3`) with `e₁ > 0` and use
coordinates `c ∈ ℝ⁴` on their span `S` via `U c = ∑ cᵢ eᵢ`.  This is an isometry from
Euclidean `ℝ⁴` onto `(S, ⟨·,·⟩_Ω)`, so the unit sphere `𝕊(S)` is the Euclidean unit sphere.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Function
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

variable {N : ℕ}

/-- The contradictory configuration of Section 5.1. -/
structure Setup (N : ℕ) where
  hN : 2 ≤ N
  Ω : Set (RN N)
  hΩ : IsDomain Ω
  e : ℕ → Amb N
  he : IsSpectralBasis Ω e
  f : ℕ → RN N → ℝ
  hf : ∀ i, IsContRep Ω (e i) (f i)
  hf0 : ∀ x ∈ Ω, 0 < f 0 x
  hgap : CN N * eigenvalue Ω 4 ≤ eigenvalue Ω 5
  /-- The PPW inequality (assumed hypothesis, see `PPWInequality`). -/
  ppw : PPWInequality N
  /-- The PPW equality case (assumed hypothesis, see `PPWEqualityCase`). -/
  ppwEq : PPWEqualityCase N

/-- The coordinate vector of `e = e₁` in `ℝ⁴`. -/
def e4 : E4 := EuclideanSpace.single 0 1

namespace Setup

variable (S : Setup N)

/-- `a = λ₄(Ω)`. -/
def a : ℝ := eigenvalue S.Ω 4
/-- `b = λ₅(Ω)`. -/
def b : ℝ := eigenvalue S.Ω 5

/-- Coordinates on `S = span{e₁,…,e₄}`. -/
def U (c : E4) : Amb N := ∑ i : Fin 4, c i • S.e i

/-- The continuous representative of `U c`. -/
def fU (c : E4) : RN N → ℝ := fun x => ∑ i : Fin 4, c i * S.f i x

/-- The balancing function `F(u) = Q_a(u₊) - Q_a(u₋)`. -/
def Fbal (c : E4) : ℝ := Qshift S.a (posPart (S.U c)) - Qshift S.a (negPart (S.U c))

/-- The balancing surface `K = F⁻¹(0) ⊆ 𝕊(S)`. -/
def K : Set E4 := {c | c ∈ sphere (0 : E4) 1 ∧ S.Fbal c = 0}

/-- The properties of Lemma 5.3 (stability) at a point `c`. -/
def Good (c : E4) : Prop :=
  posPart (S.U c) ≠ 0 ∧ negPart (S.U c) ≠ 0 ∧
  bshift S.b (posPart (S.U c)) (posPart (S.U c)) < 0 ∧
  bshift S.b (negPart (S.U c)) (negPart (S.U c)) < 0 ∧
  negIndex (bshift S.b) (H (posSign S.Ω (S.fU c))) = 2 ∧
  negIndex (bshift S.b) (H (negSign S.Ω (S.fU c))) = 2

end Setup

end FourthRatio

end
