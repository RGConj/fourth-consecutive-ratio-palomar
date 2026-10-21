# The fourth consecutive Dirichlet eigenvalue ratio

**Authors: Jiachen Shi and Quanyu Tang.**

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

The two proof gaps in the initial Aristotle delivery have been filled:

| Part | Main module |
|---|---|
| Ashbaugh–Benguria Bessel monotonicities | [BesselABComplete](RequestProject/BesselABComplete.lean) |
| Sobolev level-set and Talenti comparison | [TalentiDerivative](RequestProject/TalentiDerivative.lean) |
| Chiti comparison for the actual first eigenfunction | [ChitiGeneral](RequestProject/ChitiGeneral.lean) |
| PPW inequality and equality case | [PPWProof](RequestProject/PPWProof.lean) |
| Strict fourth-ratio conclusion | [Unconditional](RequestProject/Unconditional.lean) |

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
review; no independent human peer review or Palomar acceptance is claimed.

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
the original manuscript TeX and literature PDFs are excluded. It is prepared
for a later [Palomar submission](https://palomar-registry.org/how-to-submit),
which requires a public repository and a fixed commit. It remains private until
the authors choose to publish it; no registry submission has been made.
For the unconditional main theorem, select the repository-root project,
`comparator.json` and `formalization.yaml`, and supply the full pushed commit
SHA. The separate `comparator-conditional.json` records a modular reduction
with PPW hypotheses and is not the configuration for the unconditional claim.

Source license: [Apache-2.0](LICENSE).
