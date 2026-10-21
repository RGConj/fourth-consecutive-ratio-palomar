module

public import Mathlib

/-!
# Definitions (Section 1 of the paper)

We fix the ambient Euclidean space `ℝ^N = EuclideanSpace ℝ (Fin N)`.

**Model of the Sobolev space.**  Mathlib has no Sobolev spaces, so we model `H¹(ℝ^N)` through
pairs `(v, g)` with `v ∈ L²(ℝ^N)` and `g ∈ L²(ℝ^N; ℝ^N)`, where `g` plays the role of the weak
gradient of `v`.  For an open set `D`, the space `H_D = H₀¹(D)` is defined as the closure (in
`L² × L²`, i.e. in the `H¹` norm) of the graph `{(φ, ∇φ) : φ ∈ C_c^∞(D)}`.  This is the usual
definition of `H₀¹(D)` as the `H¹`-closure of `C_c^∞(D)`; every element is automatically
identified with its zero extension to `ℝ^N`, exactly as in the paper.  In particular, for
`D₁ ⊆ D₂` we literally have `H D₁ ≤ H D₂`, and `H D₁ = H D₂` is the paper's equality of form
domains "as subspaces of `H¹(ℝ^N)`".
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

/-- The radial Bessel profile `Φ(x) = |x|^{-ν} J_ν(√a |x|)`, `ν = N/2 - 1` (normalised with
`c = 1`; its value at `x = 0` is irrelevant up to the analytic extension, see the external
ball lemma). -/
def besselProfile (N : ℕ) (a : ℝ) (x : RN N) : ℝ :=
  ‖x‖ ^ (-((N : ℝ) / 2 - 1)) * besselJ ((N : ℝ) / 2 - 1) (Real.sqrt a * ‖x‖)

/-! ### Sign truncations -/

/-- The measurable set `{v > 0}` of a (chosen representative of an) `L²` function. -/
def posSetL2 (f : L2 N) : Set (RN N) := {x | 0 < (f : RN N → ℝ) x}

lemma measurableSet_posSetL2 (f : L2 N) : MeasurableSet (posSetL2 f) :=
  measurableSet_lt measurable_const (Lp.stronglyMeasurable f).measurable

/-- Multiplication of a scalar `L²` function by the indicator of a measurable set. -/
def indL2 (s : Set (RN N)) (hs : MeasurableSet s) (g : L2 N) : L2 N :=
  (MemLp.indicator (p := 2) (μ := volume) hs.nullMeasurableSet (Lp.memLp g)).toLp (s.indicator (g : RN N → ℝ))

lemma indL2_ae (s : Set (RN N)) (hs : MeasurableSet s) (g : L2 N) :
    (indL2 s hs g : RN N → ℝ) =ᵐ[volume] s.indicator (g : RN N → ℝ) :=
  MemLp.coeFn_toLp _

/-- Multiplication of a vector `L²` function by the indicator of a measurable set. -/
def indL2v (s : Set (RN N)) (hs : MeasurableSet s) (g : L2v N) : L2v N :=
  (MemLp.indicator (p := 2) (μ := volume) hs.nullMeasurableSet (Lp.memLp g)).toLp (s.indicator (g : RN N → RN N))

lemma indL2v_ae (s : Set (RN N)) (hs : MeasurableSet s) (g : L2v N) :
    (indL2v s hs g : RN N → RN N) =ᵐ[volume] s.indicator (g : RN N → RN N) :=
  MemLp.coeFn_toLp _

/-- Positive part `v₊ = max(v,0)` of a pair, with weak gradient `1_{v>0} ∇v`
(the Sobolev chain rule). -/
def posPart (v : Amb N) : Amb N :=
  (Lp.posPart v.1, indL2v (posSetL2 v.1) (measurableSet_posSetL2 v.1) v.2)

/-- Negative part `v₋ = max(-v,0)`. -/
def negPart (v : Amb N) : Amb N := posPart (-v)

/-- `f` is a continuous representative of `v` on `D`: `f` is continuous on `D` and agrees with
`v` almost everywhere on `D`. -/
def IsContRep (D : Set (RN N)) (v : Amb N) (f : RN N → ℝ) : Prop :=
  ContinuousOn f D ∧ (v.1 : RN N → ℝ) =ᵐ[volume.restrict D] f

/-- The sign set `D₊(v) = {v > 0}` computed with a continuous representative `f`. -/
def posSign (D : Set (RN N)) (f : RN N → ℝ) : Set (RN N) := D ∩ {x | 0 < f x}

/-- The sign set `D₋(v) = {v < 0}` computed with a continuous representative `f`. -/
def negSign (D : Set (RN N)) (f : RN N → ℝ) : Set (RN N) := D ∩ {x | f x < 0}

open Classical in
/-- Restriction `1_G v` of a (zero extended) pair to a measurable set `G`, again zero extended
(junk value `0` if `G` is not measurable). -/
def restrictTo (G : Set (RN N)) (v : Amb N) : Amb N :=
  if hG : MeasurableSet G then (indL2 G hG v.1, indL2v G hG v.2) else 0

/-! ### Shifted forms, negative index, eigenfunctions -/

/-- The shifted quadratic form `Q_{γ}(v) = q(v,v) - γ ‖v‖²`. -/
def Qshift (γ : ℝ) (v : Amb N) : ℝ := qf v v - γ * l2 v v

/-- The shifted bilinear form `𝔟_γ(v,w) = q(v,w) - γ ⟨v,w⟩`. -/
def bshift (γ : ℝ) (v w : Amb N) : ℝ := qf v w - γ * l2 v w

/-- `ind₋(b|_X)`: the supremum of the dimensions of subspaces of `X` on which `b(v,v) < 0` for
every nonzero `v` (finite-dimensional negative subspaces suffice). -/
def negIndex {M : Type*} [AddCommGroup M] [Module ℝ M] (b : M → M → ℝ) (X : Submodule ℝ M) :
    ℕ∞ :=
  ⨆ (W : Submodule ℝ M) (_ : W ≤ X) (_ : FiniteDimensional ℝ W)
    (_ : ∀ v ∈ W, v ≠ 0 → b v v < 0), (Module.finrank ℝ W : ℕ∞)

/-- `u` is a Dirichlet eigenfunction of `D` with eigenvalue `λ`:
`u ∈ H_D \ {0}` and `q(u,φ) = λ ⟨u,φ⟩` for all `φ ∈ H_D`. -/
def IsEigenfunction (D : Set (RN N)) (u : Amb N) (lam : ℝ) : Prop :=
  u ∈ H D ∧ u ≠ 0 ∧ ∀ φ ∈ H D, qf u φ = lam * l2 u φ

/-- Counting function `#{j ≥ 1 : λ_j(D) ≤ t}` (eigenvalues counted with multiplicity). -/
def eigCount (D : Set (RN N)) (t : ℝ) : ℕ∞ :=
  {j : ℕ | 1 ≤ j ∧ eigenvalue D j ≤ t}.encard

/-- A bounded open set with smooth boundary, described by a smooth defining function `ρ`
(`Ω = {ρ < 0}` with `∇ρ ≠ 0` on `{ρ = 0}`). -/
def HasSmoothBoundary (Ω : Set (RN N)) : Prop :=
  ∃ ρ : RN N → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ ∧ Ω = {x | ρ x < 0} ∧
    ∀ x, ρ x = 0 → fderiv ℝ ρ x ≠ 0

/-! ### The Payne–Pólya–Weinberger statements (External theorem 2.3, used as hypotheses) -/

/-- The statement of the PPW inequality (Ashbaugh–Benguria) in dimension `N`:
`λ₂(D) ≤ C_N λ₁(D)` for every bounded domain `D`. Modular reductions take this
statement and `PPWEqualityCase` as hypotheses; `PPWGap` proves both. -/
def PPWInequality (N : ℕ) : Prop :=
  ∀ ⦃D : Set (RN N)⦄, IsDomain D → eigenvalue D 2 ≤ CN N * eigenvalue D 1

/-- The statement of the equality case of the PPW inequality in dimension `N` (the form used in
the paper): a domain with `λ₂(D) = C_N λ₁(D)` has the same first eigenvalue and the same form
domain as some ball. -/
def PPWEqualityCase (N : ℕ) : Prop :=
  ∀ ⦃D : Set (RN N)⦄, IsDomain D → eigenvalue D 2 = CN N * eigenvalue D 1 →
    ∃ (y : RN N) (R : ℝ), 0 < R ∧ eigenvalue (Metric.ball y R) 1 = eigenvalue D 1 ∧
      H D = H (Metric.ball y R)

end FourthRatio

end
