module

public import RequestProject.BesselAB
public import RequestProject.BesselABEnergy

/-! # Both Ashbaugh--Benguria Bessel monotonicity lemmas

The definitions and statements of abW, ABBesselLemmas and ab_bessel are
preserved from PPWDeep; the proof is now independent of the Chiti declaration.
-/

@[expose] public section

open Set

noncomputable section

namespace FourthRatio

/-- The Ashbaugh–Benguria function
`w(t) = t F_{ν+1}(j_{ν+1,1}² t²) / F_ν(j_{ν,1}² t²)`, `F_μ(z) = Σ_m (-z/4)^m / (m! Γ(m+μ+1))`.
Since `J_μ(z) = (z/2)^μ F_μ(z²)`, it is the positive multiple
`(j_{ν,1}/2)^ν / (j_{ν+1,1}/2)^{ν+1}` of the Ashbaugh–Benguria ratio
`J_{ν+1}(j_{ν+1,1} t) / J_ν(j_{ν,1} t)`. -/
def abW (ν t : ℝ) : ℝ :=
  t * besselSeries (ν + 1) 1 (besselZero (ν + 1) 1 ^ 2 * t ^ 2) /
    besselSeries ν 1 (besselZero ν 1 ^ 2 * t ^ 2)

/-- The statement of the two Bessel function lemmas of Ashbaugh–Benguria for the index `ν`:
`w = abW ν` is nondecreasing on `[0, 1)` and `B(t) = w'(t)² + (2ν + 1) w(t)²/t²` is
nonincreasing on `(0, 1)`. -/
def ABBesselLemmas (ν : ℝ) : Prop :=
  MonotoneOn (abW ν) (Ico 0 1) ∧
    AntitoneOn (fun t => deriv (abW ν) t ^ 2 + (2 * ν + 1) * (abW ν t / t) ^ 2) (Ioo 0 1)

/-- **Deep input 1 (Ashbaugh–Benguria's Bessel function lemmas).**  For `ν ≥ 0`, the function
`w = abW ν` is nondecreasing on `[0, 1)`, and `B(t) = w'(t)² + (2ν + 1) w(t)²/t²` is
nonincreasing on `(0, 1)`.

(These are the two monotonicity lemmas of Ashbaugh–Benguria, Ann. of Math. 135 (1992), for the
function `J_{ν+1}(j_{ν+1,1} t)/J_ν(j_{ν,1} t)`, with `2ν + 1 = N - 1` for `ν = N/2 - 1`; the
statement is invariant under multiplication of `w` by a positive constant.)
The first component is now proved as `ab_bessel_monotone` in `BesselAB.lean`.
The energy-weight component is proved in `BesselABEnergy.lean`, using a regular endpoint
extension of the Bessel quotient, its Riccati equation and the convex level-crossing argument.

The Ashbaugh–Benguria profile itself, its smoothness, the gluing at `r = R` and the gap identity
of the ball are proved from this in `RequestProject/PPWABConstruct.lean` (`ab_profile`). -/
theorem ab_bessel {ν : ℝ} (hν : 0 ≤ ν) : ABBesselLemmas ν := by
  refine ⟨ab_bessel_monotone hν, ?_⟩
  have hw : abW ν = abRawProfile ν := by
    funext t
    simp only [abW, abRawProfile, abDenom, besselF, mul_pow]
  rw [hw]
  exact ab_bessel_energy_antitone hν

end FourthRatio

end
