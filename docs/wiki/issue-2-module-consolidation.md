# Issue #2 module consolidation prerequisites

The grouping audit used `a6475f7c0` on 2026-09-05. The bounded AppendRun
consolidation below follows that audit; the other groups remain proposals. The
baseline inventory covers the 33 modules in
`ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/` and the 52 `Append*.lean`
modules in `ArkLib/OracleReduction/Composition/Sequential/`.

## Candidate groups

The groups below are acyclic contractions of the tracked Lean import graph:
for each group, no external dependency transitively imports a member of that
group. Line counts sum the original files, including their repeated headers;
each proposed group is below the default 1,500-line cap. This graph condition
is necessary, but does not replace checking Lean declaration order, notation,
local attributes, section variables, or proof elaboration after consolidation.

Names in the first four rows are relative to `BinaryBasefold/Soundness/`;
names in the remaining rows are relative to `Composition/Sequential/`.

| Proposed group | Existing module names | Lines |
|---|---|---:|
| PreTensorMetric | PreTensorFiber, PreTensorDisagreement, PreTensorHamming, PreTensorUDR, PreTensorClosest, PreTensorCodeDistance, PreTensorDistance, PreTensorWitness | 914 |
| PreTensorMaps | PreTensorSurjectivity, PreTensorInjectivity, PreTensorFar | 851 |
| QuerySuffix | SuffixAlignCore, QueryPhaseSuffix, QueryPhasePrelims, QueryPhaseFirstOracle, QueryPhaseFoldBridge, QueryPhaseFoldedValue | 1,170 |
| Case1 | SoundnessCase1Bridge, SoundnessCase1Discharge, SoundnessProposition | 801 |
| AppendRun | AppendRunEvalDist, AppendRunEvalDistChallenge, AppendVerifierFusion, AppendVerifierFusionCore | 644 |
| AppendOracleAdapters | AppendToVerifierKeystone, AppendChallengeKeystoneOracle, AppendEmptyKeystoneOracle, AppendKnowledgeOracleTransport, AppendPerfectCompletenessOracleChallenge, AppendSoundnessOracleMsg | 658 |
| KnowledgeFailure | AppendRbrKnowledgeFailingDet, AppendRbrKnowledgeFailingDetChallenge, AppendRbrKnowledgeFailingDetEmpty | 726 |

These are partial candidates, covering 33 of the 85 audited modules. Merging
those groups would replace their 33 implementation files with seven; retaining
compatibility shims would reduce that file-count saving. All declarations and
public namespaces must survive, together with copyright and license notices.
Rewrite every tracked consumer import and recheck the full import graph after
choosing the final module names. Recheck generated umbrella imports through the
repository generator; never edit the umbrella by hand.

Four existing files need splitting rather than further merging:
`Soundness/Incremental.lean` (2,391 lines), `Soundness/QueryPhaseSoundness.lean`
(1,846), `Sequential/Append.lean` (4,111), and
`Sequential/AppendRbrKnowledgeStateFunction.lean` (1,803). Existing local linter
exceptions do not make them suitable destinations for these groups.

## Bounded AppendRun consolidation

The bounded baseline command was:

```bash
lake env lean ArkLib/OracleReduction/Composition/Sequential/AppendRunEvalDist.lean
```

The first direct attempt lacked `Append.olean`. A subsequent locked prerequisite
build compiled `Append` successfully (3,700 jobs), followed by a successful locked
baseline build of all four original members (3,706 jobs). The missing object was
therefore a cold-cache condition, not a source failure.

The four modules are consolidated into
`ArkLib.OracleReduction.Composition.Sequential.AppendRun` (654 lines). All
original declarations retain their public namespaces, statements, and proof
bodies. Separate sections preserve the original local scopes; a single header
retains the common copyright, license, and authors. Six tracked consumer imports
now point to the consolidated module. The old four import paths are retired.

The merged source passes a direct `lake env lean` check. This focused check does
not by itself certify every consumer's dependency closure or a hosted build.
The other candidate groups and oversized-file splits above remain outstanding;
this change does not claim the whole consolidation programme complete.

## Binius health boundary

The [Binius closeout audit](Binius_Closeout_Audit.md) records substrate migration
boundaries in the older soundness and reconstruction strata. No fresh
soundness-module build was completed for this grouping audit. Porting those
strata, where required, must precede a claim that consolidation preserves a
working full-security build.

`Soundness/SuffixFiberAlignment.lean` is a declaration-free compatibility shim
for `QueryPhaseSuffix`; its sole tracked Lean consumer is
`BinaryBasefold/Soundness.lean`. Redirecting that import is a small separate
candidate, but the consumer's dependency closure still needs baseline and
post-change validation. `SoundnessCase2Discharge.lean` also contains no proof
declarations and has no tracked Lean importers; its historical explanation must
be preserved if it is retired. Neither observation licenses deleting any
nonempty mathematical result.
