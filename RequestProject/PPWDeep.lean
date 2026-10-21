module

public import RequestProject.BallSecond
public import RequestProject.GroundState
public import RequestProject.ChitiGeneral
public import RequestProject.BesselABComplete

/-!
# The Payne–Pólya–Weinberger inequality: the two deep inputs

The proof of the PPW inequality `λ₂(D) ≤ C_N λ₁(D)` and of its equality case (Ashbaugh–Benguria)
is assembled in `RequestProject/PPWProof.lean` from the elementary reductions proved in
`RequestProject/PPWGapTest.lean`, `RequestProject/PPWApprox.lean`,
`RequestProject/PPWCenter.lean`, `RequestProject/PPWTransfer.lean` and
`RequestProject/PPWBall.lean`, together with the two deep inputs stated in this file:

* `ab_bessel`: the two Bessel function monotonicity lemmas of Ashbaugh–Benguria (the profile
  `ABProfile` is built from them in `RequestProject/PPWABConstruct.lean`);
* `chiti_mass`: the mass-concentration form of Chiti's comparison theorem (Schwarz
  symmetrization, Talenti's comparison, Chiti's crossing lemma).

Everything is phrased in terms of the variable `s = |x|²`.  Throughout, `a > 0` is the first
eigenvalue under consideration and `R = annR N a = j_{N/2-1,1}/√a` is the radius of the balls
whose first Dirichlet eigenvalue is `a` (`ball_first_eigen`).
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped RealInnerProductSpace

noncomputable section

namespace FourthRatio

variable {N : ℕ}

/-- An Ashbaugh–Benguria radial profile at eigenvalue `a`.  The radial vector field used in the
proof is `x ↦ h(|x|²) x`, where `h = h₁` on `s ≤ R²` and `h = h₂` on `s > R²`. -/
structure ABProfile (N : ℕ) (a : ℝ) where
  /-- inner smooth piece (the Ashbaugh–Benguria ratio `J_{N/2}(β r/R)/(r J_{N/2-1}(α r/R))`) -/
  h1 : ℝ → ℝ
  /-- outer smooth piece (equal to `κ/√s` for `s ≥ R²`) -/
  h2 : ℝ → ℝ
  /-- the constant of the outer piece -/
  κ : ℝ
  h1_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h1
  h2_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h2
  κ_pos : 0 < κ
  h2_eq : ∀ s, annR N a ^ 2 ≤ s → h2 s = κ / Real.sqrt s
  matching : h1 (annR N a ^ 2) = h2 (annR N a ^ 2)
  h1_pos : ∀ s, 0 ≤ s → s ≤ annR N a ^ 2 → 0 < h1 s

namespace ABProfile

variable {a : ℝ} (p : ABProfile N a)

/-- The profile `h(s)`. -/
def prof (s : ℝ) : ℝ := if s ≤ annR N a ^ 2 then p.h1 s else p.h2 s

/-- Its derivative (away from `s = R²`). -/
def dprof (s : ℝ) : ℝ := if s < annR N a ^ 2 then deriv p.h1 s else deriv p.h2 s

/-- `G(s) = s h(s)²`, i.e. `g(r)²` for `g(r) = r h(r²)`. -/
def Gw (s : ℝ) : ℝ := s * p.prof s ^ 2

/-- `B(s) = N h² + 4 s h h' + 4 s² h'²`, i.e. `g'(r)² + (N-1) g(r)²/r²` for `g(r) = r h(r²)`;
it is the squared Hilbert–Schmidt norm of the Jacobian of `x ↦ h(|x|²) x`. -/
def Bw (s : ℝ) : ℝ :=
  (N : ℝ) * p.prof s ^ 2 + 4 * s * p.prof s * p.dprof s + 4 * s ^ 2 * p.dprof s ^ 2

end ABProfile

/-- The statement of the mass-concentration form of Chiti's comparison theorem in dimension `N`
(see `chiti_mass`). -/
def ChitiMass (N : ℕ) : Prop :=
  ∀ ⦃D : Set (RN N)⦄, IsDomain D → ∀ ⦃u : Amb N⦄, IsEigenfunction D u (eigenvalue D 1) →
    ∀ (c : RN N) (r : ℝ),
      (∫ x in ball c r, (u.1 : RN N → ℝ) x ^ 2) *
          (∫ x in ball (0 : RN N) (annR N (eigenvalue D 1)),
            besselEntire N (eigenvalue D 1) x ^ 2) ≤
        (∫ x in ball (0 : RN N) r ∩ ball 0 (annR N (eigenvalue D 1)),
            besselEntire N (eigenvalue D 1) x ^ 2) *
          ∫ x, (u.1 : RN N → ℝ) x ^ 2

/-- **Deep input 2 (Chiti's comparison theorem, mass-concentration form).**  Let `u` be a first
eigenfunction of the domain `D`, `a = λ₁(D)`, and let `z` be the first eigenfunction of the ball
`B_R(0)` with the same first eigenvalue (`R = annR N a`), normalized to have the same `L²` norm as
`u`.  Then no ball carries more of the mass of `u²` than the concentric ball of the same radius
carries of `z²`:
`∫_{B_r(c)} u² ≤ ∫_{B_r(0)} z²` for all `c` and `r`.
It is stated here in homogeneous form, with `z = Φ 1_{B_R}` unnormalized.

(Proof in the literature: by the Hardy–Littlewood inequality `∫_{B_r(c)} u² ≤ ∫_{B_r} (u^*)²`
for the Schwarz symmetrization `u^*`, and by Chiti's theorem: `z` and `u^*` (equal `L²` norms)
cross exactly once, which follows from Talenti's comparison
`-(u^*)'(r) ≤ a/(N ω_N r^{N-1}) ∫_{B_r} u^*`, itself a consequence of the coarea formula and the
isoperimetric inequality.) The proof here constructs the actual decreasing
quantile, derives Talenti from genuine H0^1 slab tests and sharp isoperimetry,
compares with the actual ball Bessel ODE, and transports the resulting mass
inequality to Euclidean balls. No boundary regularity is added. -/
theorem chiti_mass (hN : 2 ≤ N) : ChitiMass N := by
  intro D hD u hu center r
  simpa only [annR] using first_eigenfunction_ball_mass hN hD hu center r

end FourthRatio

end
