# The fourth consecutive Dirichlet eigenvalue ratio

**Authors: Jiachen Shi and Quanyu Tang.**

**Palomar:** [PALOMAR-2026-10-22-000012, version 1](https://palomar-registry.org/entry?id=PALOMAR-2026-10-22-000012&version=1), registered on 22 October 2026.

[![Lean build and axiom audit](https://github.com/RGConj/fourth-consecutive-ratio-palomar/actions/workflows/build.yml/badge.svg)](https://github.com/RGConj/fourth-consecutive-ratio-palomar/actions/workflows/build.yml)
[![Comparator and independent kernels](https://github.com/RGConj/fourth-consecutive-ratio-palomar/actions/workflows/comparator.yml/badge.svg)](https://github.com/RGConj/fourth-consecutive-ratio-palomar/actions/workflows/comparator.yml)

This Lean development formalizes the main theorem of *A sharp bound for the
fourth consecutive Dirichlet eigenvalue ratio*. For every nonempty bounded
open connected set $\Omega\subset\mathbb R^N$, $N\ge2$,

$$\frac{\lambda_5(\Omega)}{\lambda_4(\Omega)}\lt C_N,
\qquad C_N=\frac{j_{N/2,1}^2}{j_{N/2-1,1}^2}.$$

There is no boundary regularity assumption. Eigenvalues are counted with
multiplicity. Here "domain" includes connectedness: the strict conclusion does
not extend to arbitrary bounded open sets (four disjoint congruent balls attain
equality). This is the $m=4$ case of the consecutive-ratio conjecture.
Here $j_{\nu,1}$ denotes the first positive zero of the Bessel function $J_\nu$.

The intended audience is researchers in spectral geometry and elliptic
eigenvalue inequalities. The result bounds a consecutive pair beyond the
first two Dirichlet eigenvalues, including domains with irregular boundaries.

## Palomar registration

The [public registry entry](https://palomar-registry.org/entry?id=PALOMAR-2026-10-22-000012&version=1)
records both forms of the unconditional theorem at commit
[`55ff1f42612a01b2fbe4a1eafc618cdcf83c3b75`](https://github.com/RGConj/fourth-consecutive-ratio-palomar/tree/55ff1f42612a01b2fbe4a1eafc618cdcf83c3b75),
using the repository-root `comparator.json` and `formalization.yaml`.
Palomar's [mechanical verification](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/39601289547)
passed, and its automated editorial review identified no blocking problem.

The review recorded a non-blocking warning that the informal proof account
omitted the topological contradiction establishing strictness. The proof outline
below now explains that step and links to its Lean implementation, which was
already present in the registered source. This documentation update does not
amend the immutable version 1 record or its review. The registry entry links to
the original verification evidence and preserved source snapshot.

## Formal statement and definitions

The entry point is `FourthRatio.fourth_consecutive_ratio` in [Solution.lean](Solution.lean):

```lean
theorem fourth_consecutive_ratio (N : ℕ) (hN : 2 ≤ N)
    (Ω : Set (RN N)) (hΩ : IsDomain Ω) :
    eigenvalue Ω 5 < CN N * eigenvalue Ω 4
```

[Solution.lean](Solution.lean) also publicly exposes the exact source statement,
proved in [RatioStatement.lean](RequestProject/RatioStatement.lean):

```lean
theorem fourth_consecutive_ratio_div (N : ℕ) (hN : 2 ≤ N)
    (Ω : Set (RN N)) (hΩ : IsDomain Ω) :
    eigenvalue Ω 5 / eigenvalue Ω 4 < CN N
```

Its proof uses positivity of the fourth eigenvalue. Both forms have no PPW,
Chiti, smooth-boundary or abstract spectral hypothesis. The main Comparator
configuration checks both forms against the independently stated Challenge.

[Defs.lean](RequestProject/Defs.lean) constructs the actual objects: Euclidean
space with Lebesgue measure, the closure of the smooth compact-support gradient
graph in $L^2\times L^2$, Dirichlet energy and variational min–max eigenvalues.
The Bessel function is defined by its Gamma series and successive positive zeros.
Their required spectral and zero properties are proved in the development.

## Proof and verification

The development proves both the analytic inputs and the topological contradiction
needed for the strict fourth-ratio bound:

| Part | Main module |
|---|---|
| Ashbaugh–Benguria Bessel monotonicities | [BesselABComplete](RequestProject/BesselABComplete.lean) |
| Sobolev level-set and Talenti comparison | [TalentiDerivative](RequestProject/TalentiDerivative.lean) |
| Chiti comparison for the actual first eigenfunction | [ChitiGeneral](RequestProject/ChitiGeneral.lean) |
| PPW inequality and equality case | [PPWProof](RequestProject/PPWProof.lean) |
| Line-field construction from the contradictory spectral configuration | [MainLineField](RequestProject/MainLineField.lean) |
| Topological obstruction and degree contradiction | [DegLineField](RequestProject/DegLineField.lean), [MainTheorem](RequestProject/MainTheorem.lean) |
| Strict fourth-ratio conclusion | [Unconditional](RequestProject/Unconditional.lean) |

The analytic part proves the Ashbaugh–Benguria Bessel monotonicities and obtains
Chiti mass comparison from Sobolev level-set estimates and Talenti comparison.
These give the sharp Payne–Pólya–Weinberger (PPW) inequality and its equality case.

To prove strictness for the fourth ratio, assume instead that
$C_N\lambda_4(\Omega)\le\lambda_5(\Omega)$.
[MainSetup](RequestProject/MainSetup.lean) identifies the span of the first four
orthonormal eigenfunctions with $\mathbb R^4$. On its unit sphere $S^3$, balancing
the shifted energies of the positive and negative parts defines a separating
zero set. The nodal and spectral-index analysis in
[MainStrict](RequestProject/MainStrict.lean), its stability in
[MainStable](RequestProject/MainStable.lean), and the gluing of local negative
sections in [MainLineField](RequestProject/MainLineField.lean) construct a
continuous line field near this zero set. Each line is orthogonal both to the
sphere point and to the fixed coordinate vector of the positive first
eigenfunction; the field is represented by rank-one orthogonal projections.

[DegLineField](RequestProject/DegLineField.lean) proves that a field satisfying
these conditions cannot exist on a sufficiently thin compact slab adjoining
the zero set. Such a field would yield a homotopy on $S^2$ between a degree-two
map and its negative, whose topological degrees differ.
`Setup.prop_degree_contradiction` in [MainTheorem](RequestProject/MainTheorem.lean)
combines this obstruction with the constructed field and obtains a contradiction.
[Unconditional](RequestProject/Unconditional.lean) supplies the proved PPW inputs,
and [RatioStatement](RequestProject/RatioStatement.lean) uses positivity of
$\lambda_4$ to obtain the quotient form. This is the decisive strictness argument
in addition to the PPW inequality and equality case.

The production proof contains no `sorry` or custom axiom. The strict axiom gate
rejects every dependency outside `propext`, `Classical.choice` and `Quot.sound`.
The deliberate `sorry` terms in `Challenge*.lean` are Comparator task placeholders
(two in `Challenge.lean`, one in `ChallengeConditional.lean`); solutions do not
import those challenge modules. Conditional reductions are
retained as separate library results, alongside the unconditional proof.
See [AUDIT_STATUS.md](AUDIT_STATUS.md) for verification evidence and its limits.

## Reproduce

Pinned versions: Lean `leanprover/lean4:v4.36.0-rc1` and Mathlib
`625d8914199bc567cca9b91f90e8e5afafa5ae51`. All Git dependencies are locked to
full commit hashes in `lake-manifest.json`. Install [elan](https://github.com/leanprover/elan),
Python 3.11 or later, and Git, then run:

```sh
python3 -m pip install -r scripts/requirements.txt
lake exe cache get
lake build
python3 scripts/check_sources.py
python3 scripts/check_statement.py
python3 scripts/check_metadata.py
lake env lean scripts/CheckAxioms.lean
```

For the official Comparator with independent NanoDa and con-ron replay, use
Linux with `bubblewrap` and working unprivileged user namespaces:

```sh
bash scripts/verify-comparator.sh
```

The script uses the Comparator and kernel binaries bundled with the pinned Lean
toolchain. It generates a temporary independent-kernel configuration; the submitted
`comparator.json` contains only allowed fields. The build and Comparator workflows
run on pushes, pull requests and manual dispatch. They cache only pinned
dependencies and rebuild this project's Lean modules from source on every run.
The Python statement gate detects source drift in the copied definitions and
public theorem interfaces; Lean and the Comparator perform the semantic checks.
For all auxiliary axiom gates
and logged reproduction, run `bash scripts/reproduce.sh` after installing the
same prerequisites. A successful build alone is insufficient to rule out proof holes.

## Authorship, assistance and provenance

The original informal proof was developed by **Jiachen Shi and Quanyu Tang with
assistance from ChatGPT**. **Aristotle and Codex produced the formalization from
the authors' original informal proof**. Aristotle supplied the initial Lean
development; Codex audited its fidelity, repaired the proof gaps, and adapted the
development to the pinned toolchain. The audit includes an independent AI source
review and the Palomar automated review linked above. No independent human peer
review is claimed.

The Bessel argument follows Ashbaugh and Benguria,
[*A second proof of the Payne–Pólya–Weinberger conjecture*](https://doi.org/10.1007/BF02099533).
The mass comparison is based on Chiti's rearrangement method
([background](https://doi.org/10.1007/BF00948319)). Reused geometric and coarea
formal proofs are attributed in [THIRD_PARTY.md](THIRD_PARTY.md) and their source headers.
Lean and Mathlib supply the underlying library for the fourth-ratio proof.
The source manuscript is unpublished and is not included or publicly archived
in this repository, so its text cannot be independently checked from this
snapshot. Novelty and priority relative to other work have not been established
by this audit; no such claim rests on the private manuscript.

This repository contains formal source, verification scripts and metadata;
the original manuscript TeX and literature PDFs are excluded. The repository is
public, and its registered version is identified above.
The unconditional main theorem uses the repository-root project,
`comparator.json` and `formalization.yaml`. The separate
`comparator-conditional.json` records a modular reduction
with PPW hypotheses and is not the configuration for the unconditional claim.

Source license: [Apache-2.0](LICENSE).
