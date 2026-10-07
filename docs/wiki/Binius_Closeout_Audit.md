# Binius Closeout Audit

This note resolves the remaining out-of-scope items for the Binius grant closeout as tracked in Issue #313 and #317.

## Out-of-Scope Residual Assumptions
The following assumptions are intentionally kept as external/residual hypotheses for now and are marked as grant-out-of-scope:
- `FinalSumcheckStepLogicCompleteResidual`
- `ExtractMLPCorrectnessResidual` (proven false as stated, handled by `revIndexMLP` and unique witness theorems, but the old residual class remains documented as an obstruction surface).
- `FoldMatrixDetNeZeroResidual` / `foldMatrix_det_ne_zero` (the historical discharge used the
  retired `foldMatrixNat` API; `FoldDetSplit.lean` and `FoldDetDischarge.lean` now record this as
  a substrate-port boundary instead of exposing a stale theorem).
- `Reconstruct/IncrementalHelpers.lean` (the historical helper lemmas used the retired
  `OracleFunction : Fin r` indexing and natural-number `iterated_fold` step API; the current
  substrate indexes oracle functions by protocol level `Fin (ell + 1)` and folds with
  `steps : Fin (ell + 1)`, so this file now records the migration boundary).
- Any remaining `h...Completeness` or `h...RbrKnowledgeSoundness` hypotheses not covered by direct append/seq-compose plumbing.

## Composition Assumptions

The role-named composition assumptions in `BinaryBasefold/CoreInteractionPhase.lean`,
`FRIBinius/CoreInteractionPhase.lean`, and the older full-security wrappers are intentionally kept
as external hypotheses. They are marked as grant-out-of-scope for this closeout, as discharging
them with `append_perfectCompleteness_total` would require a separate port of the stale
`Relations` / `ReductionLogic` / `QueryPhase` / `Soundness` / incremental reconstruction proof
strata to the current Binary Basefold substrate API.

The issue #313 focused validation target consists of
`BinaryBasefold/General.lean`, `FRIBinius/General.lean`, and `BBFSmallFieldIOPCS.lean`.
The two `General` modules contain the full-protocol composition wrappers;
`BBFSmallFieldIOPCS.lean` imports them. Their explicit component security
hypotheses remain obligations, even when these entry points compile.

Focused validation command:

```bash
./scripts/lake-locked.sh build ArkLib.ProofSystem.Binius.BinaryBasefold.General ArkLib.ProofSystem.Binius.FRIBinius.General ArkLib.ProofSystem.Binius.BBFSmallFieldIOPCS
```

## Issue #2 composition API repair (2026-09-06)

The current `BinaryBasefold/CoreInteractionPhase.lean` compiles against the
repaired step and cast APIs. Explicit append-coherence instances cover fold,
relay, commit, block sequences, and the sumcheck-fold wrappers. Cast transport
requires agreement of both input and output oracle interfaces. The repair also
normalizes block protocol types and fixes finite-index and sum-reindexing proofs.

This compilation preserves the role-named completeness and knowledge-soundness
hypotheses described above. It does not discharge them, finish QueryPhase, or
establish full Binius security. Full downstream and repository checks remain
separate acceptance requirements.

The compiled artifact and a separate import-based audit of all 54 top-level
lemmas, theorems, and named instances passed. Each declaration uses only
`propext`, `Classical.choice`, and/or `Quot.sound` (some use no axioms).
The source hash and declaration-by-declaration results are recorded in
[`binius-core-interaction-2026-09-06.json`](../kb/audits/binius-core-interaction-2026-09-06.json).
These axiom results do not remove explicit hypotheses from theorem statements.

## Terminal audit repair (2026-10-06)

The FRI-Binius sumcheck-fold input bridge cannot be recovered by a namespace-only
migration. `BinaryBasefold.roundRelation` admits its unfinished-block bad-event
branch at round zero, independently of the claimed sum or witness. The local
counterexample `sumcheckFold_input_bridge_counterexample` uses the zero witness
and a claimed sum of one: the BinaryBasefold input relation holds, but the
ring-switching input relation fails. The attempted unconditional extractor-lens
instance and its dependent soundness wrapper therefore have no valid port to
these relations and have been replaced by this refutation. The full protocol's
explicit composition hypotheses remain visible; compilation and the standard
axiom whitelist do not discharge those hypotheses.

The context-lifting migration supplies separate oracle-routing lenses for the
standalone verifier and the reduction's verifier, preserving each output-oracle
embedding. Their coherence and the strict-input completeness lift are checked
separately. Ring-switching uses the explicit binary-tower packing profile.

Query verification must propagate rejection through `OptionT`. Its logic step
previously returned a plain `OracleComp`, allowing a failed repetition's `none`
result to be discarded by a bind. The repaired interface retains `OptionT`
through verification and states no-failure completeness on that computation.

The final-sumcheck extraction bridge uses unique decoding to identify the first
decoded oracle with the novel-basis encoding of the extracted multilinear
polynomial. The decoded prefix-fold chain then reaches the final constant.
Its challenge order follows `foldOrderChallenges`; evaluation of the extracted
witness uses `revIndexMLP`. The flagship axiom list includes this bridge and the
input-relation counterexample, so both are checked by routine validation.

`BinaryBasefold/QueryPhase/Folding.lean` contains the query verifier definitions
and folding lemmas. `BinaryBasefold/QueryPhase.lean` imports it and retains the
completeness and knowledge-soundness proofs. This separation lets downstream
proof repair reuse the compiled folding lemmas without changing their public
names or statements. The preservation proof separates successful-query support
from the algebraic fold identity and uses the public fiber-evaluation bridge to
avoid reducing dependent domain conversions inside the kernel. Both query
folding endpoints are included in the flagship axiom audit.
`BinaryBasefold/FinalRelation.lean` supplies the shared equivalence between the
canonical final folding relation and the final-sumcheck state relation, including
their dependent oracle indices. Query soundness and the FRI final-step proof
reuse that equivalence.

All three Binius entry points now pass a locked build (4,066 jobs), including
both full-protocol modules. An import-based audit of 107 declarations reports
only `propext`, `Classical.choice`, and `Quot.sound` (some use no axioms).
The exact source hashes, declaration reports, and validation boundaries are in
[`binius-terminal-repair-2026-10-07.json`](../kb/audits/binius-terminal-repair-2026-10-07.json).
The local full-repository attempt stopped at host vnode exhaustion while
importing two unrelated mathlib dependency closures; clean hosted validation
is a separate merge gate. These checks do not discharge the explicit security
hypotheses.

The old scalar wrapper `fullOracleVerifier_knowledgeSoundness` was not a valid
proof: it called a conditional round-by-round wrapper without its hypothesis
and referenced implication lemmas absent from the supported security API.
It is replaced by the explicitly named
`fullOracleVerifier_knowledgeSoundness_of_sum_bound`, which transports an
established scalar bound using the proved error-sum inequality. This does not
establish the missing scalar security premise or the round-by-round-to-scalar
implication. The retired implication implementation's always-failing extractor
is not imported or used to claim security.

The current generic ring-switching batching theorem exposes error `1`.
`batchingTargetRbrKnowledgeError` therefore records the sharper `κ / |L|` target
separately. The existing full-protocol composition hypotheses must establish
that target; no proof identifies the generic unit bound with it. The DP24
arithmetic expression and the query-phase bounds are retained. The flagship
audit pins both the arithmetic inequality and the explicitly conditional
scalar transport theorem under their current names.

Hosted validation of `35bf20c48` completed the full default build (14,036 jobs)
and the flagship-module build (9,054 jobs). The combined axiom import then found
a duplicate `Reduction.append_completeness_msg` declaration in two sequential
composition modules. `AppendSeamBridges3` now reuses the canonical
`AppendCompletenessMsgKeystone` proof; its older initializer-bearing interface
is named `append_completeness_msg_of_neverFail`, and its two consumers use that
name. The combined import audit remains enabled.
The repaired module and both consumers pass a locked 3,782-job build. A direct
import of both previously conflicting modules passes; the canonical reduction
root, compatibility wrapper, and oracle-reduction root all have standard-only
axiom closures.
