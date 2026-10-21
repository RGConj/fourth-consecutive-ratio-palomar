# Third-party formal proofs

The following files retain their original copyright and Apache-2.0 license notices. Local edits adapt module headers, import paths, and proof syntax to the pinned Lean and Mathlib versions. The complete development is checked by the build and axiom gates described in README.md.

## Isoperimetric inequality

Jonathan Ho's proofs of the Prékopa–Leindler, Brunn–Minkowski and isoperimetric inequalities, originally at https://github.com/hojonathanho/isoperimetric, are taken from the LeanPool snapshot https://github.com/Vilin97/lean-pool/tree/9c296f447f48f3242df5e65e0b6120ddffcd79a7/LeanPool/Isoperimetric.

Local files: RequestProject/IsoperimetricBasic.lean, IsoperimetricPrekopaLeindler.lean, IsoperimetricBrunnMinkowski.lean and Isoperimetric.lean. The geometric endpoint bounds the volume of an epsilon thickening. The sharp level-set estimate in this project is derived directly from epsilon thickenings, upper ball envelopes and layer cake.

## Scalar coarea

RequestProject/ScalarCoarea.lean adapts Asher Yan's scalar coarea development (credited in the source to Asher Yan with ChatGPT 5.6), from https://github.com/Polarnova/ProbabilityApproximation/blob/a2fc5bda874d9b69186c0ba165bf79f3b9897662/ProbabilityApproximation/ConvexGeometry/ScalarCoarea.lean. The original is Apache-2.0. Local changes preserve the definitions and theorem statements while adapting module visibility, TFAE indexing and proof elaboration. Its scalar coarea theorem applies to globally Lipschitz maps. The project separately proves its required Sobolev level-set estimates by smooth approximation in the actual gradient-graph closure.
