# Sequential knowledge-soundness module consolidation

This part of issue #2 combines `AppendRbrKnowledgeFailingDet`,
`AppendRbrKnowledgeFailingDetChallenge`, and `AppendRbrKnowledgeFailingDetEmpty`
into `ArkLib.OracleReduction.Composition.Sequential.KnowledgeFailure` (745 lines).
The module collects the reduction from failing to total determinism and its
challenge-seam and empty-seam composition theorems.

All original implementation bodies and public namespaces are preserved in
separate sections. Copyright and license notices are retained. Ten external
consumers now import the consolidated module; the three old paths are retired.
This changes module organization, not the hypotheses of knowledge soundness.

## Validation boundary

The combined pending Binius and Sequential consolidation has 25 explicit new or
changed module targets and an acyclic closure of 240 ArkLib modules. Exact body
comparison preserves each of the three knowledge modules. Their original source
bytes also match those in the running oracle-adapter build; that build must
finish successfully before serving as baseline evidence.

Candidate elaboration and builds of all changed consumers remain acceptance
gates. Structural checks alone do not establish successful compilation or
unconditional protocol security. The default generated umbrella is unchanged
at 4,984 imports.
