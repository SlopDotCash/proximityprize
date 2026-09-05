# Binius module consolidation

This part of issue #2 groups twenty implementation files into four
modules. It preserves public namespaces and theorem bodies, and does not
establish an unconditional protocol security theorem.

| Module | Former implementation files | Lines |
|---|---|---:|
| `Soundness.PreTensorMetric` | PreTensorFiber, PreTensorDisagreement, PreTensorHamming, PreTensorUDR, PreTensorClosest, PreTensorCodeDistance, PreTensorDistance, PreTensorWitness | 904 |
| `Soundness.PreTensorMaps` | PreTensorSurjectivity, PreTensorInjectivity, PreTensorFar | 865 |

All names in the table are relative to
`ArkLib.ProofSystem.Binius.BinaryBasefold`. Each source's implementation is in a
separate section, preserving its local variables, options, and namespace scope.
The common copyright and license notice is retained. The new metric module
collects fiber congruence, disagreement, Hamming, unique-decoding, closest-codeword,
and witness bounds. The maps module collects surjectivity, injectivity, and
transport of distance bounds.

`Soundness.Incremental` and `Soundness.FoldDistance` now import the maps module;
`Incremental` also imports the metric module directly. The maps module imports
the metric module. The eleven old import paths are retired without compatibility
shims. Both new files remain under the default 1,500-line limit.

The `Soundness.Case1` module (816 lines) also consolidates
`SoundnessCase1Bridge`, `SoundnessCase1Discharge`, and `SoundnessProposition`.
It preserves the original authorship notices, theorem bodies, and separate local
scopes. Its four external consumers are `BinaryBasefold.Soundness`,
`SoundnessCase2FarLift`, `SoundnessCase2Probability`, and
`SoundnessCase2Discharge`. The conditional soundness proposition retains its
original hypotheses.

`Soundness.QuerySuffix` (1,187 lines) combines `SuffixAlignCore`,
`QueryPhaseSuffix`, `QueryPhasePrelims`, `QueryPhaseFirstOracle`,
`QueryPhaseFoldBridge`, and `QueryPhaseFoldedValue`. Six original bodies are
preserved in separate sections, with the original authorship notices. Its five
external consumers are `BinaryBasefold.Soundness`, `SuffixFiberAlignment`,
`QueryPhaseHelpers`, `QueryPhaseSoundness`, and `BadBlocks`.

## Validation boundary

The source grouping preserves the original proof bodies. A recursive import
check of the maps module visits an acyclic closure of 86 ArkLib modules after
the two pre-tensor contractions. The Case1 module has an acyclic closure of
101 ArkLib modules and preserves each of its three original implementation
bodies. The generated default umbrella still contains 4,984 imports.
The final set of fourteen new or changed modules has an acyclic closure of
129 ArkLib modules. These structural checks do not prove elaboration of the consolidated sources or
of their consumers. Original-source baseline builds and candidate compilation
are separate acceptance gates; this preparation is not a completed build claim.

The other Binius grouping candidates and the oversized `Incremental` and
`QueryPhaseSoundness` files remain separate work. Registered external assumptions
and conditional soundness hypotheses remain unchanged.
