# Issue #2 module consolidation prerequisites

This is a source/import audit of `a6475f7c0` on 2026-09-05, not a completed
refactor or a Lean build certificate. It covers the 33 modules in
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

## AppendRun baseline and next gate

The bounded baseline command was:

```bash
lake env lean ArkLib/OracleReduction/Composition/Sequential/AppendRunEvalDist.lean
```

It failed at line 6 before elaboration because the local object file for
`ArkLib.OracleReduction.Composition.Sequential.Append` did not exist. This is
missing local build evidence, not a demonstrated source error or a mathematical
obstruction. No AppendRun source restructuring was performed.

First build the four existing targets through `scripts/lake-locked.sh`, then
record successful focused baseline checks and their axiom output before editing.
The group's graph has `AppendRunEvalDistChallenge` depending on
`AppendRunEvalDist`; the two fusion files import `Append` directly. Preserve each
file's namespace/section boundaries and place the EvalDist declarations before
the challenge declarations. After consolidation, check the new module and all
rewritten direct consumers, run the locked build and repository validation,
and preserve exact-commit hosted evidence before merging.

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
