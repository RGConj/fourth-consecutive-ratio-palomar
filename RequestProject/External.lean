module

public import RequestProject.BesselZeros
public import RequestProject.Rellich

/-!
# External inputs (Section 2 of the paper)

This file records the external results used by the informal argument and their locations
in the Lean development. These results are proved in project modules, as detailed below.
The PPW inequality and equality case use the proved Ashbaugh–Benguria Bessel
monotonicities and the actual Chiti mass-concentration theorem.

Details of the proved reductions:
* The sphere-approximation and degree theorem is not assumed: the topological statement used in
  the degree contradiction (no continuous line field on a thin compact neighbourhood of the zero
  set of `F` in `𝕊³`) is proved as `Degree.degree_no_line_field` in
  `RequestProject/DegLineField.lean`, without degree theory (see the comment at External
  theorem 2.7 below).
* The separation-of-variables clause of the ball/annulus external lemma is not assumed: the
  annulus part is proved in `RequestProject/AnnulusSep.lean` and the one-dimensional content of
  the ball part in `RequestProject/BesselGap.lean`.
* The higher-ratio estimate `λ₄ < C_N λ₂` is not assumed: it is proved as `higher_ratio` in
  `RequestProject/Higher.lean` from the PPW inequality and its equality case.
* The shrinking-tube theorem is not assumed: the collinear configuration used for sharpness is
  proved as `chain_tubes` in `RequestProject/TubeChain.lean`.
* Interior analyticity is not assumed: it is proved as `ext_analytic` in
  `RequestProject/InteriorAnalytic.lean`.
* Positivity of the ground state is not assumed: it is proved as `ground_state_pos` in
  `RequestProject/MaxPrinciple.lean` (strong minimum principle).
* The spectral package is not assumed: `ext_spectral` (eigenfunction expansion, min–max
  characterisation, `λ₁ > 0`, `λ_j → ∞`) is proved from Rellich's compactness theorem, which is
  itself proved in `RequestProject/Rellich.lean`.
* The spectral part of the ball/annulus external lemma is not assumed: the first eigenvalues and
  eigenfunctions of the ball and of the annulus are proved in `RequestProject/BallSpectral.lean`,
  the `N` degree-one eigenfunctions with eigenvalue `C_N a` in `RequestProject/BallDegreeOne.lean`,
  and the lower half of the second-eigenvalue statement in `RequestProject/BallSecondLower.lean`.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Function
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

variable {N : ℕ}

/-! ### External theorem 2.1: the Dirichlet spectral package -/

/-- **Spectral package (proved).** A complete
`L²`-orthonormal sequence of real eigenfunctions `e_j` (indexed from `0`, `e j` has eigenvalue
`λ_{j+1}(D)`), the eigenvalues being the min–max values, positive, nondecreasing and tending to
`+∞`, with the spectral expansions of `q_D` and of the `L²` norm.

Proof (`RequestProject/Rellich.lean`, `RequestProject/SpectralAbstract.lean`,
`RequestProject/SpectralH.lean`): Rellich's theorem (compactness of `H_D ↪ L²`, by mollification
and Arzelà–Ascoli), then successive
minimisation of the Rayleigh quotient on the `L²`-orthogonal complements of the previously found
eigenfunctions (direct method: minimising sequences are Cauchy by compactness and the
parallelogram law), the Euler–Lagrange equation, the Poincaré inequality (`λ₁ > 0`), infinite
dimensionality of `H_D` (bump functions), `λ_j → ∞` by compactness, completeness and the min–max
characterisation. -/
theorem ext_spectral (hN : 2 ≤ N) {D : Set (RN N)} (hD : IsAdmissible D) :
    ∃ e : ℕ → Amb N,
      (∀ j, IsEigenfunction D (e j) (eigenvalue D (j + 1))) ∧
      (∀ i j, l2 (e i) (e j) = if i = j then 1 else 0) ∧
      0 < eigenvalue D 1 ∧
      Monotone (fun j => eigenvalue D (j + 1)) ∧
      Tendsto (fun j => eigenvalue D (j + 1)) atTop atTop ∧
      ∀ v ∈ H D, HasSum (fun j => eigenvalue D (j + 1) * l2 v (e j) ^ 2) (qf v v) ∧
        HasSum (fun j => l2 v (e j) ^ 2) (l2 v v) :=
  spectral_of_compact hN hD (rellich hD.2.2)

/- Compactness of the embedding `H_D ↪ L²(D)` is proved as `rellich` in
`RequestProject/Rellich.lean`; it is restated as `compact_embedding` in
`RequestProject/Derived.lean`. -/

/- Domain monotonicity `λ_j(D₂) ≤ λ_j(D₁)` for `D₁ ⊆ D₂` (part of the spectral package in the
paper) is not assumed: it is proved as `eigenvalue_domain_mono` in `RequestProject/Derived.lean`
from the min–max definition and `ext_spectral`. -/

/- Positivity of the ground state (on a domain the first eigenvalue has a strictly positive
continuous eigenfunction; part of the "connected sets" clause of the spectral package in the paper)
is not assumed: it is proved as `ground_state_pos` in `RequestProject/MaxPrinciple.lean` from
`ext_spectral`, `ext_analytic`, Lemma 3.1 and unique continuation (a first eigenfunction does not
change sign; its analytic representative solves `-Δf = λ₁f` pointwise; Hopf's lemma and the strong
minimum principle).  Simplicity of the first eigenvalue is proved from it as `ground_state` in
`RequestProject/GroundState.lean`. -/

/- The disjoint-union part of the spectral package (the form domain of a disjoint union of open
sets is the orthogonal sum of the form domains, and its eigenvalues are the combined multiset of
the eigenvalues of the pieces) is not assumed: it is proved as `disjoint_union` in
`RequestProject/DisjointCount.lean` (form domains: `H_iUnion_of_disjoint` in
`RequestProject/DisjointUnion.lean`; eigenvalue counting: `eigCount_iUnion`, derived from
`ext_spectral` for the pieces and for the union). -/

/-! ### External theorem 2.2: interior regularity and unique continuation -/

/- Interior analyticity (weak solutions of `-Δw = λw` in a domain `D` lying in `H_D` are real
analytic in `D`) is not assumed: it is proved as `ext_analytic` in
`RequestProject/InteriorAnalytic.lean` (Weyl's lemma for the harmonic lift
`u(x) cosh(√λ t)` in `D × ℝ`, interior derivative estimates for harmonic functions and Taylor's
formula). -/

/- Unique continuation (two weak solutions with the same `λ` that agree on a nonempty open
subset of the domain agree on the whole domain) is not assumed: it is proved as `ucp` in
`RequestProject/Derived.lean` from `ext_analytic` and the identity theorem for analytic
functions. -/

/- The special case "a nonzero eigenfunction of a domain cannot vanish on a nonempty open
subset" is not assumed: it is proved as `ucp_nonvanishing` in `RequestProject/Derived.lean`
from `ucp` (with `v = 0`). -/

/-! ### External theorem 2.3: Payne–Pólya–Weinberger inequality and equality -/

/- The statements `PPWInequality` and `PPWEqualityCase` (defined in `RequestProject/Defs.lean`)
are proved by `ext_ppw` and `ext_ppw_equality` in `RequestProject/PPWGap.lean`.
The core development also uses them as explicit hypotheses for modular reductions.
The two Bessel and Chiti inputs consumed by `PPWProof` are proved in
`BesselABComplete` and `ChitiGeneral`, respectively. -/

/-! ### External theorem 2.4: the previously known higher-ratio estimate -/

/- The higher-ratio estimate `λ₄(D) < C_N λ₂(D)` for bounded domains is not assumed: it is
proved as `higher_ratio` in `RequestProject/Higher.lean` from the PPW inequality and its
equality case, nodal localization, the disjoint-union counting identity and the ball–annulus
lemma (Lemma 4.1). -/

/-! ### External lemma 2.5: ball and annulus spectral data -/

/-- **Ball and annulus data, Bessel zeros (proved).** With `ν = N/2 - 1`: the first two
positive zeros of `J_ν` satisfy `0 < j_{ν,1} < j_{ν,2}`, `J_ν < 0` on `(j_{ν,1}, j_{ν,2})`, and
`C_N = j_{N/2,1}²/j_{ν,1}² > 1`.  This clause of the external lemma is not assumed: it is proved
from the series definition of `J_ν` in `RequestProject/BesselZeros.lean` (existence of zeros by
Sturm comparison, isolation of zeros by analyticity, sign change and interlacing from the
Bessel recursions).  (Positivity of `J_ν` on `(0, j_{ν,1})` follows from the definition of
`j_{ν,1}`, see `besselEntire_pos`.) -/
theorem ext_bessel (hN : 2 ≤ N) :
    let ν : ℝ := (N : ℝ) / 2 - 1
    0 < besselZero ν 1 ∧ besselZero ν 1 < besselZero ν 2 ∧
      (∀ s, besselZero ν 1 < s → s < besselZero ν 2 → besselJ ν s < 0) ∧ 1 < CN N := by
  intro ν
  have hν : 0 ≤ ν := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    simp only [ν]; linarith
  obtain ⟨a1, a2, -⟩ := besselZero_props hν
  exact ⟨a1, a2, fun s h1 h2 => besselJ_neg_between hν h1 h2, CN_gt_one hN⟩

/- The second-eigenvalue clause of the ball/annulus external lemma is not assumed either.  Its
lower half (`λ₂(B) ≥ C_N a`, and eigenfunctions with eigenvalue `C_N a` span at most `N`
dimensions) is proved as `ball_second_lower` in `RequestProject/BallSecondLower.lean` (reflection
symmetry of low eigenfunctions via the half ball, whose first eigenvalue is `C_N a`, and a
comparison argument for radial eigenfunctions using the Bessel interlacing
`j_{N/2,1} < j_{N/2-1,2}`); the paper's form `λ₂(B) = C_N a` with an `N`-dimensional second
eigenspace is `ext_ball_second` in `RequestProject/BallSecond.lean`. -/

/- The separation-of-variables clause of the ball/annulus external lemma is not assumed.
* Annulus part (the functions `ψ, ψ x₁/|x|, …, ψ x_N/|x|` span an `(N+1)`-dimensional subspace of
  `H₀¹(A)` with the separation-of-variables bound on the Rayleigh quotient): proved as
  `annulus_sep` in `RequestProject/AnnulusSep.lean` (membership in `RequestProject/AnnulusMem.lean`,
  radial calculus and the energy identity in `RequestProject/AnnulusRadial.lean`, spherical
  symmetry of radial integrals in `RequestProject/AnnulusSym.lean`).
* Ball part (degree-one modes): its one-dimensional content, the Bessel zero inequality
  `j_{ν,1}² + (N - 1) < j_{N/2,1}²`, is proved as `besselZero_sq_gap` in
  `RequestProject/BesselGap.lean`. -/

/-! ### External theorem 2.6: nodal localization -/

/- Nodal localization (smoothness of eigenfunctions, membership of the sign truncations in the
form domains of the sign sets, and the fact that the restrictions to the connected components of
the sign sets are, up to sign, positive first eigenfunctions with the same eigenvalue) is not
assumed: it is proved as `nodal` in `RequestProject/Nodal.lean` from `ext_spectral`,
`ground_state_pos`, `ext_analytic`, Lemma 3.1 and the form domain of a disjoint union. -/

/-! ### External theorem 2.7: sphere approximation and degree facts (packaged) -/

/-- The Euclidean space `ℝ⁴`, used as coordinates on the span of the first four eigenfunctions. -/
abbrev E4 := EuclideanSpace ℝ (Fin 4)

/- The sphere approximation and degree theorem is not assumed.  The paper uses it only in the
degree contradiction, through the following topological statement: for continuous `F : 𝕊³ → ℝ`
with `F(e) < 0 < F(-e)` and an open neighbourhood `𝒪` of `F⁻¹(0)`, some compact `M ⊆ 𝒪 ∩ 𝕊³`
carries no continuous line field `u ↦ ℝ w(u)` with `w(u) ⊥ u` and `w(u) ⊥ e`.  This is proved as
`Degree.degree_no_line_field` in `RequestProject/DegLineField.lean` with `M` a thin slab
`{-ε ≤ F ≤ 0}`: squaring the lines turns a line field into a continuous homotopy from the
degree-two map `qdir : 𝕊² → 𝕊²` to `-qdir` (`RequestProject/DegBmap.lean`), and such a homotopy
does not exist (`RequestProject/DegSmooth.lean`, `RequestProject/DegCore.lean`): after smoothing,
the Jacobian determinant is a null Lagrangian (`RequestProject/DegNullLagrangian.lean`), which
forces `∫ det D Qp = 0` over a shell, contradicting `det D Qp ≥ 0` (`RequestProject/DegQp.lean`). -/

/-! ### External theorem 2.8: shrinking-tube spectral convergence -/

/- The shrinking-tube theorem is not assumed.  The paper uses it only in the sharpness corollary,
for a chain of congruent balls whose centres lie on a line; for that configuration it is proved as
`chain_tubes` in `RequestProject/TubeChain.lean`: explicit smooth bounded domains of revolution
`Ωₙ ⊇ ⋃ᵢ Bᵢ` with regular defining functions, together with the spectral convergence
`λ_j(Ωₙ) → λ_j(⋃ᵢ Bᵢ)` proved in `RequestProject/TubeSpectral.lean` (Rellich compactness, lower
semicontinuity of the energy, and a dilation argument identifying the limits as elements of
`H₀¹(⋃ᵢ Bᵢ)`, `RequestProject/TubeDilation.lean`). -/

end FourthRatio

end
