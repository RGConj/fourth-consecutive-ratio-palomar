# Source and verification audit

This file records the scope and limits of the formalization audit. It is not
an independent human review or a Palomar acceptance certificate.

## Statement fidelity

The source main theorem (`thm:main`) asserts
$\lambda_5(\Omega)/\lambda_4(\Omega)\lt C_N$ for every bounded domain in
Euclidean dimension at least two. Solution states the equivalent multiplication
inequality. `FourthRatio.fourth_consecutive_ratio_div` derives the exact quotient
using the proved positivity of the fourth variational Dirichlet eigenvalue.

Expanded inputs of the unconditional theorem:

| Input | Meaning | Source basis | Category |
|---|---|---|---|
| `N : Nat` | Euclidean dimension | Dimension convention | TYPING |
| `hN : 2 ≤ N` | Dimension at least two | Main theorem | SOURCE |
| `Ω : Set (RN N)` | Subset of Euclidean space | Domain quantifier | TYPING |
| `hΩ.1.1` | Ω is open | Definition of domain | SOURCE |
| `hΩ.1.2.1` | Ω is nonempty | Definition of domain | SOURCE |
| `hΩ.1.2.2` | Ω is bounded | Bounded domain hypothesis | SOURCE |
| `hΩ.2` | Ω is connected | Definition of domain | SOURCE |

Counts: SOURCE 5, TYPING 2, STANDING 0, RULED 0, EXCESS 0. No boundary
regularity, PPW statement, Chiti comparison, spectral package or abstract
Bessel assumption is an input of the main theorem.

The inspected definitions use actual Euclidean space, Lebesgue measure, closure
of the compact-support smooth gradient graph, its Dirichlet quadratic form,
and the finite-dimensional Rayleigh min–max. The positive-index spectral
properties are proved in `SpectralH` from compactness. `besselJ` is the Gamma series, with real powers totalized by Mathlib.
Its agreement with the classical positive-argument Bessel function is the
convention relevant here. Only its positive zeros enter the main constant: `besselZero_props` proves their positivity,
zero property and ordering for the nonnegative orders used here. The actual
ball profile uses the normalized entire series, including its value at the
origin. No arbitrary selected spectrum or assumed zero characterization is
substituted for these constructions.

## Repair of the initial delivery

A separate byte-identical baseline of the original Aristotle sources built on
Lean 4.28.0, but its unconditional main theorem depended on `sorryAx`. It had
two unproved mathematical inputs: `ab_bessel` and `chiti_mass`. Its conditional
PPW reduction had a clean axiom closure and did not establish the unconditional
source theorem by itself. The original delivery and manuscript were preserved.

Both gaps now have actual proofs:

- `BesselABComplete` supplies both Bessel monotonicities. The energy argument
  proves a regular common-zero endpoint extension, the true logarithmic-slope
  endpoint values, a Riccati equation and the required convex crossing bound.
- The Chiti chain proves the sharp Sobolev level-set estimate from actual
  isoperimetry and smooth approximation, arbitrary-level weak-gradient formulas,
  weak-eigenfunction slab identities, the actual decreasing quantile and Talenti
  comparison, local absolute continuity and the zero-endpoint limits. It then
  proves comparison with the actual Bessel ball ODE, homogeneous square-mass
  concentration and Euclidean radial-volume transport. `ChitiGeneral` handles
  every first eigenfunction using proved ground-state simplicity. `PPWDeep`
  applies this theorem directly to the original `ChitiMass` statement.

The two repaired input statements and main theorem have no extra hypotheses.
A separate AI reviewer inspected the main statement, definition meanings and
actual consumption of the new Bessel/Chiti results and reported no substantive
problem. This is AI source review, not human peer review.

## Verification gates

- Source gate: passes with no production proof hole or prohibited proof mechanism.
  Only the designated Challenge task placeholders are exempted.
- Pinned metadata: passes the official v0.4 schema, full dependency SHA checks,
  toolchain consistency and Comparator configuration checks.
- Bessel, geometry, Sobolev, quantile, Talenti, ball-model and Chiti auxiliary
  proofs passed strict axiom audits. Each gate rejects any axiom outside
  `propext`, `Classical.choice` and `Quot.sound`.
- Full project build: passed on 2026-10-21 (18,478 build tasks).
- Main axiom gate: passed for all 52 declarations, including the unconditional
  main theorem, exact quotient, repaired Bessel/Chiti inputs and unconditional
  corollaries. Their transitive axiom closures contain only the standard three.
- Fresh release build and official sandboxed Comparator replay: pending final
  execution in the release workflows. These are not yet claimed as passed.

The two GitHub workflows reproduce the build/axiom/metadata checks and Linux
sandboxed official Comparator with bundled NanoDa and con-ron. A local Windows
run without `bubblewrap` is not described as a sandboxed Palomar check.

## Release boundary

Only Lean source, declared dependency pins, verification scripts, documentation,
metadata and license material are included. The manuscript TeX, literature PDFs,
private process logs, build artifacts and development cache junction are excluded.
The release build uses its own dependency directories and begins with no project
artifacts. Dependency caches may be reused only at the declared exact revisions.

The repository remains private at the authors' request. Future Palomar intake
requires publication and a fixed full commit, as specified by the
[submission guide](https://palomar-registry.org/how-to-submit) and
[contribution policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md).
No registry submission is made by this preparation.
