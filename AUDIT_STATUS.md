# Source and verification audit

This file records the scope and limits of the formalization audit. It is not
an independent human review or a Palomar acceptance certificate.

## Statement fidelity

The source main theorem (`thm:main`) asserts
$\lambda_5(\Omega)/\lambda_4(\Omega)\lt C_N$ for every bounded domain in
Euclidean dimension at least two. Solution publicly exposes the multiplication
inequality and `FourthRatio.fourth_consecutive_ratio_div`, which derives the exact
quotient using the proved positivity of the fourth variational Dirichlet eigenvalue.
The main Comparator now checks both statements. Connectedness is part of the
standard domain convention and is essential: four disjoint congruent balls attain
equality, so the strict statement is not asserted for arbitrary bounded open sets.

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
- Statement source gate: `scripts/check_statement.py` compares the copied basic
  definitions and advertised theorem interfaces. This detects source drift;
  it does not replace Lean elaboration or the Comparator's semantic comparison.
- Pinned metadata: passes the official v0.4 schema, full dependency SHA checks,
  toolchain consistency and Comparator configuration checks.
- Bessel, geometry, Sobolev, quantile, Talenti, ball-model and Chiti auxiliary
  proofs passed strict axiom audits. Each gate rejects any axiom outside
  `propext`, `Classical.choice` and `Quot.sound`.
- Full project build: passed on 2026-10-21 (18,478 build tasks).
- Main axiom gate: passed for all 52 declarations, including the unconditional
  main theorem, exact quotient, repaired Bessel/Chiti inputs and unconditional
  corollaries. Their transitive axiom closures contain only the standard three.
- Fresh Linux release build: passed on the exact source commit
  `ef28a23edebcb472265f00dfcb527a57f08f7e92`, with no project artifacts restored.
  All nine strict axiom scripts passed (227 declaration checks).
  [Build and axiom run](https://github.com/RGConj/fourth-consecutive-ratio-palomar/actions/runs/39571270139).
- Official sandboxed Comparator, Lean kernel replay, and both bundled independent
  kernels (NanoDa and con-ron): passed on that same source commit.
  [Comparator run](https://github.com/RGConj/fourth-consecutive-ratio-palomar/actions/runs/39571270186).

The two GitHub workflows reproduce the build/axiom/metadata checks and the
Linux sandboxed official Comparator with bundled NanoDa and con-ron. The
independent replay uses `bubblewrap` and the pinned toolchain binaries.
The execution evidence above refers to the source commit; later documentation
updates do not alter its mathematical source.

## Final source review on 2026-10-21

The follow-up review started from `78454cd2b725e6f50198a53703d51bbc6f932edd`.
The GitHub API and downloaded logs confirmed the full build and all 227 axiom
checks on that exact revision, and confirmed con-ron, NanoDa and Lean kernel
acceptance of the multiplication theorem's dependency closure:
[build](https://github.com/RGConj/fourth-consecutive-ratio-palomar/actions/runs/39575147624),
[Comparator](https://github.com/RGConj/fourth-consecutive-ratio-palomar/actions/runs/39575147926).

Parallel AI source reviews checked the actual definitions and spectral min–max
construction, the main strictness and line-field argument, and the Bessel,
Chiti and PPW interfaces and key proofs. No substantive mathematical defect,
hidden main-theorem assumption or change of the target statement was found
within those reviews. This is a targeted source review supported by kernel
checks, not a claim of independent human review of every line.

The follow-up changes correct stale comments describing proved results as
external assumptions and clarify that the product maximum norm is equivalent
to the usual Sobolev norm. They also expose the exact quotient through
`import Solution`, include it in the main Challenge/Comparator pair, add the
statement source gate, and restrict CI caches to pinned dependencies so that
project modules are compiled from source on every workflow run. The existing
mathematical definitions and proof bodies are unchanged. Challenge contains
two deliberate task placeholders; ChallengeConditional contains one. Neither
is imported by a solution.

Historical CI passes above apply only to their named revisions. For these
follow-up changes, use both workflow results attached to the final revision.
Build logs may contain non-fatal style and unused-tactic linter messages;
passing compilation and axiom gates does not mean the source is warning-free.

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
