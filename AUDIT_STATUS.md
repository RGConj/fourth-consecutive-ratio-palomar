# Source and verification audit

This file records the scope and limits of the formalization audit and links to
the public Palomar registration and verification evidence. No independent human
peer review is claimed.

## Palomar registration on 2026-10-22

- Registered result: [PALOMAR-2026-10-22-000012, version 1](https://palomar-registry.org/entry?id=PALOMAR-2026-10-22-000012&version=1).
- Registered source: [`55ff1f42612a01b2fbe4a1eafc618cdcf83c3b75`](https://github.com/RGConj/fourth-consecutive-ratio-palomar/tree/55ff1f42612a01b2fbe4a1eafc618cdcf83c3b75).
- Configuration: repository-root `comparator.json`, checking both
  `FourthRatio.fourth_consecutive_ratio` and
  `FourthRatio.fourth_consecutive_ratio_div`.
- Mechanical verification: passed on 2026-10-21, including the official Comparator
  with NanoDa and con-ron; permitted axioms are `propext`, `Quot.sound` and
  `Classical.choice`.
  [Verification run](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/39601289547).
- Repository CI at the registered commit also passed:
  [build and axiom audit](https://github.com/RGConj/fourth-consecutive-ratio-palomar/actions/runs/39592206006),
  [Comparator and independent kernels](https://github.com/RGConj/fourth-consecutive-ratio-palomar/actions/runs/39592206004).
- Automated editorial review: completed on 2026-10-21 by `codex:gpt-6-sol`, with
  outcome `neutral`, no blocking problem, and one non-blocking proof-account warning.
- The [machine-readable registry record](https://data.palomar-registry.org/entries/PALOMAR-2026-10-22-000012-v1.json)
  identifies the verification evidence, review and source-preservation archive.

The review warning concerns the informal explanation of strictness: the
registered README listed the analytic inputs through PPW without explaining
the final topological contradiction. That argument was already implemented
in `MainLineField.lean`, `DegLineField.lean` and `MainTheorem.lean` at the
registered commit. Assuming `C_N * lambda_4 <= lambda_5`, the spectral and nodal
analysis constructs a continuous line field near a separating level set in
the unit sphere of the first four eigenfunctions. The lines are orthogonal
to both the sphere point and the ground-state coordinate vector.
`Degree.degree_no_line_field` rules out such a field on a thin compact slab
by a homotopy-degree obstruction on the two-sphere.
`Setup.prop_degree_contradiction` combines the construction and obstruction;
`fourth_ratio_of_ppw` concludes the strict inequality, with proved PPW inputs
supplied by `Unconditional.lean`.

The current README expands this proof account in response to the warning.
These documentation and metadata updates do not change the Lean definitions,
proofs, dependency pins or Comparator configuration. They do not amend the
registered version 1 snapshot or its published review. Registration records
mechanical verification and automated editorial review; it does not constitute
independent human peer review or establish novelty or priority.

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

Historical CI passes above apply only to their named revisions. Both workflows
also passed on the registered revision, as linked in the registration section.
Build logs may contain non-fatal style and unused-tactic linter messages;
passing compilation and axiom gates does not mean the source is warning-free.

## Release boundary

The Palomar preflight checked the official submission policy and the metadata
contract at `PalomarRegistry/PalomarSubmission` revision
`d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44`. Source types use the policy's
documented `paper` vocabulary, with the unpublished manuscript's availability
and unestablished novelty disclosed explicitly. The official metadata loader
accepts the project as a source-based substantive development. This preflight
does not constitute a Palomar submission or its own mechanical/editorial review.

Only Lean source, declared dependency pins, verification scripts, documentation,
metadata and license material are included. The manuscript TeX, literature PDFs,
private process logs, build artifacts and development cache junction are excluded.
The release build uses its own dependency directories and begins with no project
artifacts. Dependency caches may be reused only at the declared exact revisions.

The repository is now public. The authors registered the unconditional main
result with Palomar on 2026-10-22; the exact version, source commit and evidence
are linked above. Later repository updates do not change that registered snapshot.
