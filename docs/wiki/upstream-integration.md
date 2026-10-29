# Upstream ArkLib integration

`SlopDotCash/proximityprize` contains the complete canonical library imported from
`Verified-zkEVM/ArkLib`, plus the downstream proximity-prize formalization and research evidence.
Upstream code is read-only as a publishing destination: all branches and pull requests from
this project belong to `SlopDotCash/proximityprize`.

## Source ownership

The [canonical inventory](../../scripts/arklib-upstream.json) records the source revision and
upstream modules re-exported by `ArkLib.lean`.
Those source files, Lean's module-system conventions, and the upstream toolchain and dependency
pins define the foundation. Keep one implementation of each shared definition. When upstream
moves a definition, migrate downstream imports or use a small compatibility import/alias;
do not retain the old implementation under its former path.

A checked downstream proof or construction may fill an inherited upstream admission. A compatible
type generalization may also preserve a broader downstream API without duplicating an upstream
implementation. Preserve existing behavior and record the affected declarations, original upstream blob,
downstream provenance, and reviewed content hash in the inventory's `downstream_adaptations`.
The source checker accepts only those exact reviewed contents. Remove discharged debt from
the admission baselines only after the kernel audit confirms the improvement.

The [higher-universe polynomial client](../../ArkLibTest/Compatibility/PolynomialUniverses.lean)
instantiates the reviewed SplitFold APIs and `Bivariate.degreeX_le_natWeightedDegree` at
`ULift.{1} ℚ : Type 1`. It checks coefficient extraction, recombination, folding, and the
weighted-degree bound through canonical imports, with kernel axiom reports. Generic downstream
clients and the complete package build remain part of validation.

Downstream-only modules and compatibility theorems belong to the extension layer. Existing
import paths can stay stable through separate Lake ownership, while the canonical umbrella
remains a module and exports the complete upstream library. Additional declarations formerly
embedded in shared files are consolidated under `ProximityPrize/Extensions/`, preserving their
mathematical namespaces. Their extraction manifest records the original sources and the
declarations replaced by canonical implementations.

Research remains a separate classic Lean library. The dependency direction is canonical
ArkLib, then extensions, then Research. A canonical module must not import downstream code.
Run the surface generators after staging added or removed Lean files; do not edit generated
umbrellas or library-glob blocks by hand.

`python3 scripts/integration/check_consolidation.py` verifies the inventory against the pinned
Git tree, checks every canonical source blob, rejects imports from canonical modules into
downstream or test code, and checks the local import graph for missing modules and cycles.
The normal import gate runs it. After committing the merge, add `--require-ancestor` to verify
that the upstream snapshot is part of the actual Git history.
Every CI job invoking `validate.sh` or the provenance gate must check out full history
(`fetch-depth: 0`) so the pinned upstream Git blobs are available on a fresh runner.

For a separate public-name ownership audit, run
`python3 scripts/integration/audit_public_declarations.py --output scripts/integration/public-declaration-audit.json`.
The bounded [snapshot](../../scripts/integration/public-declaration-audit.json) records the source
inventory hash and repeated names. The scanner respects `module` default privacy and nested
`public section` scopes; it scans tracked production and Research sources using their column-zero
command convention. Treat candidates as review items and confirm their actual public scope before
consolidating. Exports, syntax, generated declarations, and API compatibility still require Lean
module checks. Refresh the snapshot after source changes; it does not certify a package build.

Canonical Binary Basefold challenge slices are chronological. Historical newest-first vectors
must cross the explicit `Compatibility.newestFirstFoldingChallenges` adapter; reversing a native
vector before the adapter recovers the canonical slice. A two-challenge client distinguishes these
conventions ([audit](../../scripts/integration/binius-challenge-order-migration.json)). The old
witness encoding also reversed Boolean variables; its explicit `Compatibility.newestFirstCodeword`
uses canonical folding while retaining that input convention
([migration](../../scripts/integration/binius-basic-convention-migration.json)). The historical
logical query checks equal their canonical counterparts after this explicit statement conversion,
through every repetition; the raw matrix layouts remain distinct
([query proof](../../scripts/integration/binius-query-convention-migration.json)). Historical
`extractMLP` correctness retains both the `revIndexMLP` output and its actual unique-decoding-radius
guard; its encoding obstruction concerns that downstream convention
([reconstruction audit](../../scripts/integration/binius-reconstruction-migration.json)).
Concrete legacy logic-step records use canonical chronological relations and delegate the canonical
fold, commit and final completeness proofs. The commit adapter proves equality between native
virtual output materialization and the historical embedded oracle values; it does not identify their
query representations. Separate historical endpoint lemmas still prove the reversed encoding's
final polynomial evaluation ([logic audit](../../scripts/integration/binius-reduction-logic-consolidation.json)).


The FRI-Binius core uses the canonical chronological folding language and native decoder.
Its historical newest-first input relation and terminal algebra remain explicit compatibility
results; changed-language completeness and knowledge declarations have `_native` names. The final
step uses the native deterministic guard and knowledge-state engine. The full core RBR wrapper
still requires its explicit append-RBR premise. The [migration audit](../../scripts/integration/fribinius-core-native-migration.json)
records renamed commands, original sources and kernel checks; a [coefficient-view regression](../../ArkLibTest/Compatibility/FRIBiniusEncoding.lean)
distinguishes the encodings before any challenge. Its retained round-zero counterexample concerns
only the historical bad-event predicate.

The historical soundness tensor uses a low-row-bit coefficient matrix, now named
`Compatibility.lowRowBitFoldMatrix`. Its nonsingularity proof reuses the retained legacy matrix
owner; no entrywise equality to canonical `foldMatrix` is assumed. The pre-tensor Hamming bound
reuses the canonical fiber-distance theorem. FRI phase composition uses canonical metric-distance
endpoints, while `Compatibility.exactFoldChainRel` preserves the stronger historical positive-radius
and exact-witness data with a proved one-way implication. The native final-query checker condition
still excludes failure and fixes every successful output. The
[caller audit](../../scripts/integration/full12-binius-fri-caller-migration.json) preserves all
original commands and distinguishes source/overlay checks from package validation.

Native Binary Basefold query execution delegates canonical chronological completeness and
support proofs. The retained historical state predicate and single-repetition probability bound
live under `QueryPhase.Historical`; they describe the historical low-row-bit convention. Its
pure guard/fold/terminal lemmas use explicit newest-first slices and the lower-case historical
`strictFinalSumcheckRelOutProp`. The old execution-to-historical-check lemmas are retired rather
than identifying incompatible matrix layouts. Native fiber support and zero-failure helpers use
the canonical simulation and `OptionT` laws. The `BiniusChallengeOrder` and `FRIBiniusEncoding`
regressions distinguish the conventions. Both full-protocol completeness clients use the native
query theorem with their canonical strict final relation. The
[query execution audit](../../scripts/integration/binius-query-execution-consolidation.json) and
[folding audit](../../scripts/integration/binius-query-folding-migration.json) archive original
commands and their dispositions. The historical probability bound retains both its
no-folding-consistency and no-bad-event hypotheses.

The flagship kernel audit pins native query execution and chronological folding separately,
alongside the explicitly historical counterexample and terminal-fold result. The
[pin migration record](../../scripts/integration/flagship-native-query-pins.json) tracks all
replacements; the audit now checks 57 declarations without dropping any unaffected entry.

The canonical `disagreement_fold_subset_fiberwiseDisagreement` statement now formally requires
`Fact (β 0 = 1)` because its quotient-fiber set uses that normalized basis. The previous general
positive-step statement is retained as
`Compatibility.disagreement_fold_subset_globalDisagreementDestinations` without that premise.
Its explicitly coarse destination set marks every destination whenever there is any source
mismatch; a proved filter equality records the exact historical meaning. Actual disagreeing
quotient fibers map into that coarse set, and no converse is claimed. This is a canonical
specialization plus a separately named general compatibility theorem, rather than an unchanged
formal signature ([disposition](../../scripts/integration/full12-binius-fri-caller-migration.json)).

Fold-error containment now uses canonical fiber locality: equal source values on a fiber give
equal evaluation vectors and therefore equal folded values. The original UDR-close wrapper follows
from the stronger arbitrary-function result; global disagreement alone is insufficient
([proof audit](../../scripts/integration/binius-fold-locality-migration.json)).

## Compatibility APIs

| Development | Canonical API | Retained downstream surface |
| --- | --- | --- |
| Algebraic group representations | `AGM.GroupRepresentation` uses one coefficient per finite basis index | `ProximityPrize.Compatibility.AGM.ListRepresentation` retains the list model and completed handle simulator; explicit length-aware bridges connect the representations |
| Pure knowledge transport | Canonical round-by-round definitions and shared-state game mixture | [`PureKnowledge`](../../ProximityPrize/Compatibility/PureKnowledge.lean) owns the preserved arbitrary-witness extraction, carry/pushforward, and pure-phase flip lemmas; [provenance](../../scripts/integration/pure-knowledge-consolidation.json) records both former owners |
| Tight terminal completeness | Canonical `CheckClaim` is a pure pass-through | `finalCheckPure` delegates `finalCheckTight`; both keep terminal identities in semantic relations. The full and pure completeness wrappers share the seven-seam fold in `TightComposedCompleteness`; [mapping](../../scripts/integration/binius-spartan-final-fqn-consolidation.json) archives the consolidated proof copies |
| Uniform probabilities | VCVio native sampling and event measures | `ProximityPrize.Compatibility.UniformProbability` proves the finite PMF/native event bridge |
| Failing discrete coupling | Canonical measure TV through the checked PMF bridge | `ProximityPrize.Compatibility.CompletedPMFCoupling` keeps explicit `PMF (Option α)` completions, infinite countable supports, and equal `none` mass; the SPMF-specific path is an import shim |
| Reachability and probability | Native measure semantics separates these concepts | `ProximityPrize.Compatibility.DiscreteProbability` records the old discrete zero-event law and proves its uniform-oracle and `OptionT` instances |
| Polynomial splitting and folding | `Polynomial.splitNth` and `FoldingPolynomial.polyFold` | Legacy coefficient/reconstruction lemmas delegate to canonical proofs; `Polynomial.foldNth` abbreviates the canonical fold |
| Constrained Reed–Solomon codes | `ReedSolomon.constrainedCode` and `multiConstrainedCode` use `Domain.SmoothCosetFftDomain` | `ReedSolomon.Compatibility.{constrainedCode,multiConstrainedCode}` retain arbitrary `Smooth` embeddings and `Type*` universes; both equality-to-canonical lemmas are `rfl` ([audit](../../scripts/integration/dependency-dedup.json)) |
| Modified Guruswami interpolants | Canonical existence uses positive multiplicity | `ProximityGap.Compatibility.modified_guruswami_has_a_solution_of_degree_bounds` preserves the older arbitrary-multiplicity interface under explicit degree budgets; positive multiplicities use the canonical construction |
| Grand challenges | Canonical adjacent integer-grid boundaries and `Code.Lambda` | Research retains its different maximal-radius / legacy-list-size model under `Continuous*` names and `continuousGrandListDecodingChallenge`; see [collision audit](../../scripts/integration/public-fqn-consolidation.json) |
| Ring-switching coordinates | Canonical columns recover the packed right factor; rows recover the left factor | Historical recovery helper names now state their formulas using the authoritative coordinate operations; `binaryTowerProfile` delegates to `tensorProductProfile` |
| Partial polynomial evaluation | `fixFirstVariablesOfMQP` fixes a prefix; the next challenge uses `Fin.snoc` | Legacy wrappers delegate the canonical evaluation/substitution/transition laws; [convention clients](../../ArkLibTest/Compatibility/RingSwitchingCoordinates.lean) distinguish the former suffix convention ([audit](../../scripts/integration/ringswitching-conventions.json)) |
| Binary Basefold basis and fibers | Pinned CompPoly owns intermediate-basis reconstruction; canonical fibers require destination ≤ ℓ | Historical basis names re-export their owners. The broader rate-tail fiber and low-row-bit matrix evaluator retain explicit compatibility proofs ([audit](../../scripts/integration/binius-basis-consolidation.json)) |
| Binary Basefold unique decoder | Canonical `uniqueDecodingCodeword` owns the implementation | `UDRCodeword` retains its full original positional metadata/proof interface and delegates the canonical decoder; a generic positional client checks the unchanged API ([audit](../../scripts/integration/binius-decoder-consolidation.json), [regression](../../ArkLibTest/Compatibility/BiniusDecoder.lean)) |
| Ordinary commitment adversaries | VCVio's `CommitmentScheme.BindingAdversary` / `HidingAdversary` use `ProbComp` | `OracleBindingAdversary` / `OracleHidingAdversary` retain arbitrary oracle specs and separate committer/verifier keys |
| Toy-problem winning sets | Canonical instances pin a linear encoder; `winningSetDensity` is their combinatorial supremum | `ToyProblem.ExistentialEncoding` retains the distinct legacy instance/ratio API that existentially quantifies encoders for an arbitrary code set |
| Canonical polynomial coefficients | CompPoly's constructors and coefficient maps | The former downstream univariate module is a compatibility import rather than another implementation |

Do not substitute `Code.Lambda` and `ListDecodable.Lambda` without a bridge. Canonical
`Code.Lambda` uses `Set.encard`, so an infinite list has cardinality `⊤`; the legacy definition
uses `Set.ncard` cast to `ℕ∞`, which gives `0` for an infinite set. Retained statements use the
intended name explicitly. The [finite list-size bridges](../../ProximityPrize/Compatibility/ListSize.lean)
prove equality when point lists or the code are finite, including finite codes over infinite
alphabets. [Acceptance clients](../../ArkLibTest/Compatibility/ListSize.lean) check that boundary
and the distinct values for an infinite point list. Likewise, a generic probability theorem may
require the discrete
support contract: arbitrary native measures need not assign positive mass to each reachable
point. The native marginal bounds only need lawful measure semantics, with exact attachment
for support-quantified statements; they do not need the stronger discrete zero-event contract.
Finite-uniform PMF conclusions retain their explicit normalized-count bridge. Generic native
probability observers use `Type`, as required by `EvalDistSemantics`; pure simulation and
structural support laws retain their higher-universe generality. The exact mappings and retained
names are recorded in [the probability migration audit](../../scripts/integration/probability-api-migration.json).

Preserve existing `DecidableEq` instances when transporting a protocol challenge to its field.
A fresh instance can change implicit `Finset` parameters and turn a small predicate comparison
into expensive polynomial unfolding. Supply only the challenge metadata inference actually
needs; the [LogUp outer port](../../scripts/integration/full20-logup-outer-malicious-native-port.json)
records a checked example at the default Lean heartbeat budget.

The [permutation migration audit](../../scripts/integration/lazy-permutation-migration.json)
records the native eager–lazy bridge and the retired completed-SPMF observers. Its finite
prefix/continuation models reuse the existing PMF counting and absorption proofs through
`PMF.toMeasure`. The master equality supports arbitrary measurable output types; it does not
require a countable output type or another probability interpreter.

The per-state Fiat–Shamir verifier leg uses a native program continuation before taking output
measures. It preserves the prover's output queries, the subsequent verifier queries, and explicit
`none` rejection. Its original full-transcript joint-coupling hypothesis remains explicit; the
port does not discharge that hypothesis ([migration](../../scripts/integration/hvzk-per-state-native-migration.json)).

The historical `ArkLib.ToMathlib.SPMFBindComm` path now imports canonical
`MeasureTheory.Measure.bind_bind_swap`; the SPMF-specific declaration is retired. The native law
requires s-finite prefix measures and a jointly measurable continuation, and also applies to
subprobability measures with missing mass. The concrete state-preserving simulation swaps live in
[StatePreservingSimulation](../../ProximityPrize/Compatibility/StatePreservingSimulation.lean).
They derive commutation from the existing handler-state guarantee and canonical uniform
`ProbComp` semantics. No program assumption or global discrete instance is added. Their original
`OptionTStateT` names remain available through `RunUnroll`.

The [native security migration](../../scripts/integration/native-security-migration.json)
records the state-collapse program equality and the security-game correction. Upstream's
`knowledgeSoundnessWith` counts extractor failure as a bad event and permits arbitrary private
prover inputs. The old always-failing-extractor vacuity theorem and its unconditional corollary
are retired. The retained conditional bridge certifies its specified pure extractor under explicit
full-run seam, marginal transport and per-round bounds for arbitrary private inputs; the guarded
worst-case bridge and the knowledge-to-plain round-by-round implication reuse canonical owners.

The [additional math-owner audit](../../scripts/integration/additional-math-owner-consolidation.json)
records reuse of canonical Hamming-ball averaging, entropy-volume and Lagrange interpolation
proofs. Floor-equality entropy adapters have explicit `_of_floor_eq` names and use the finite
`Lambda` bridge. Power-generator interleaving corollaries import their existing invariance owner.

Oracle casts transport both interface families explicitly. Equal output carrier types alone do
not identify the query interfaces used by canonical output materialization; `CastInOut` therefore
requires output-interface `HEq` along with its existing input-interface and relation transports.

The retained message-seam n-ary completeness engines now take native pointwise oracle-response
instances. Their original component-completeness and handler-support premises remain explicit;
the oracle adapter reuses the canonical `seqCompose_toReduction` law. See the
[n-ary completeness migration](../../scripts/integration/sequential-completeness-migration.json).

The message-seam round-by-round soundness proof also retains canonical append's completed
first-phase carry during phase two. Its doomed composite reads `S₁ completed ∨ seam ∈ lang₂ ∨ S₂`:
either fixed disjunct makes a flip impossible, and otherwise the second component's original
soundness premise applies. The unconditional wrapper keeps its original structural hypotheses.
See the [phase-two carry migration](../../scripts/integration/append-phase2-carry-migration.json).

Final FRI completeness delegates canonical execution and materialization: the final witness meets
the degree guard, and the transmitted polynomial has zero distance from itself. Its historical
residual contract is retained ([migration](../../scripts/integration/fri-final-completeness-migration.json)).

## Corrected Johnson radius

Canonical `JohnsonBound.Jqℓ q ℓ δ` is `J q (((ℓ - 1) / ℓ) * δ)`. The former downstream
radius used the inverse factor `ℓ / (ℓ - 1)`, so its three-word diagnostic no longer applies.
At `q = ℓ = 2` and `δ = 1/2`, the corrected radius is `(1 - sqrt (1/2)) / 2`, strictly below
`1/2`. The canonical `CodingTheory.johnson_bound_lambda_le_ell` is proved and authoritative.

The [retirement record](../../scripts/integration/johnson-radius-retirement.json) preserves
the three obsolete diagnostic statements and their old source. The existing
[finite-code fixture](../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean)
keeps its valid distance and cardinality facts and now checks the corrected theorem instead.
No wrong-radius compatibility definition is retained to make the old inconsistency claim pass.
The [historical issue disposition](../kb/audits/proximity-prize/dispositions/issue-49-johnson-family.md)
is explicitly superseded for this radius.

## Sequential execution and output oracles

Canonical verifiers carry either an embedded output with interface coherence, or a virtual output
with a proved query/materialization agreement law. Canonical append constructs a virtual output.
The former `AppendCoherent` class and embedding-only composition metadata are retired; adapters
reuse canonical `append_toVerifier`, `seqCompose_toVerifier`, and `seqCompose_toReduction`.
The extensional output law is `materializeOutput_append`, rather than a total `append.embed`.

Component executions use `liftAppendLeft` and `liftAppendRight` to pin their challenge inclusions.
This matters when the two component protocols coincide: a newly elaborated bare `liftM` can choose
the right inclusion for either copy. The upstream sequential-execution acceptance test distinguishes
the two query indices. Message-first completeness delegates `append_run_of_seam`; the retained
conditional residual adapter is named `append_run_of_right_residual`, separate from the canonical
purity-based `append_run` theorem.

The retained lens event inequality is now `liftContext_probEvent_le_of_not_mem`: the outer input
must be outside the input language, as required by canonical lens soundness. Exact retired commands,
canonical replacements, and validation boundaries are recorded in
[`sequential-output-api-migration.json`](../../scripts/integration/sequential-output-api-migration.json).

Native completeness proofs use the upstream `Reduction.run_run_eq_bind` execution boundary.
The message-seam append proof observes every optional result, transfers each component's
completeness through the original support-faithfulness premise, and rules out both verifier
failure branches. The three historical message-composition names share that one completed owner.
The forwarding `SendClaim` extension still executes its public oracle computation before returning
its output; its completeness proof preserves those queries. The WHIR RBR-facing completeness
wrappers reuse `Whir.ProtocolCompleteness` instead of copying the proof and challenge instances.
The [native completeness audit](../../scripts/integration/native-completeness-migration.json)
records the contracts, retired duplicate sources and kernel checks.

Message and empty seams share `Reduction.append_perfectCompleteness_of_run_factorization`.
Always-accepting WHIR and STIR shells share
`Reduction.perfectCompleteness_of_constant_output`; its premises require the actual honest
prover output and optional verifier run to return the same valid output. It preserves the
entire prover prefix and its queries. The remaining WHIR and STIR proof copies are tracked in
the [proof-consolidation record](../../scripts/integration/whir-stir-proof-consolidation.json).

The genuine STIR checking verifier keeps its Boolean checks and honest-prefix invariant.
Its completeness proof, and the three-slot block proofs, use native optional-output support
laws and canonical output materialization. Their original mathematical contracts and source
are recorded in the [checking migration audit](../../scripts/integration/stir-checking-native-migration.json). The vectorized
chain follows the same support proof through each sampled vector challenge and then reuses
the append and n-ary engines. Its eight theorem headers and all statement/oracle agreements
are preserved; response metadata is expressed by pointwise `Range` families
([vector-chain audit](../../scripts/integration/stir-vector-chain-native-migration.json)).

The lazy Fiat–Shamir prover proofs retain their original cache behavior and full projected
message, private-state and ambient-state observations. Stronger native program equalities have
separate `program_eq` names; the historical public coupling names take native distribution
observations of those programs. Their [migration record](../../scripts/integration/lazy-fs-native-programs.json)
preserves the old source and the canonical support-congruence replacement.

Canonical batched FRI exposes its generator-selected combined oracle before native FRI runs.
The old coefficient-only non-oracle statement tail cannot materialize that output through the
current oracle interface. Its exact sources are archived; the retained conditional security
contributions use explicitly named `CanonicalBatchingSeam` interfaces. The
[tail migration record](../../scripts/integration/batched-fri-tail-migration.json) includes the
checked two-input countermodel. The shared `Verifier.reduction_run_run_nf` now delegates to
canonical execution through `ProximityPrize.Compatibility.ReductionRunNormalForm`.

## Integrating another upstream snapshot

For proofs with large concrete finite intervals, prove the interval identity and bound with
a symbolic endpoint, then instantiate that theorem at the numeric endpoint. Rewriting a closed
interval can force the kernel to expand millions of elements. The
[small-pool ledger migration](../../scripts/integration/research-numeric-ledger-kernel-migration.json)
preserves its original constants and hypotheses while using this symbolic calculation.
Large polynomial witnesses follow the same rule: the shared Reed–Solomon monomial-witness
theorems prove membership with symbolic exponents, and the Research callers instantiate them
at their original parameters ([migration audit](../../scripts/integration/full17-research-api-ports.json)).

1. Start a feature branch from current downstream `origin/main` in an isolated worktree.
2. Fetch upstream `main` by its explicit HTTPS URL into a read-only tracking ref. Do not
   configure an upstream push destination.
3. Merge through the shared Git history. Resolve shared implementations in favor of the
   upstream source, then port unique downstream declarations and callers to that API.
4. Review upstream renames and deletions. A retained old path must provide unique downstream
   behavior or a compatibility surface, rather than recreate a retired implementation.
5. Update the source inventory, run both `scripts/update-lib.sh` and
   `python3 scripts/update-research-lib.py`, and reconcile bibliography entries by key.
   The Research `All.lean` export surface has its own generator. Keep upstream text for shared
   bibliography keys and retain downstream-only references.
6. Validate canonical ArkLib and downstream extensions and Research with the pinned toolchain,
   using `scripts/lake-locked.sh` for every build and cache fetch. Include the upstream acceptance
   tests and kernel audits, the downstream proof-policy gates, and import/documentation checks.
7. Immediately before publishing, verify the actual push URL. Create pull requests with an
   explicit `--repo SlopDotCash/proximityprize`; verify the returned base repository too.
8. Merge the integration PR with a merge commit, preserving the upstream commit as an ancestor
   of downstream `main`. Squashing or rebasing the integration would discard that shared-history
   relationship and make later synchronizations repeat the same upstream changes. Verify the
   pinned revision with `git merge-base --is-ancestor` on the resulting downstream head.

Check migrated modules through their actual import boundaries: combining source files can hide
private-instance and typeclass differences. Individual Lean checks are separate from a complete
package build. If a temporary import overlay is necessary, expose all fallback modules and the
complete Lean artifact families, including `.ir.sig` beside `.ir`. A partial namespace shadows
later search roots, and a missing IR signature can make a computable imported declaration appear
to have no executable code. Re-run the complete default-target build after freezing the sources.

## Proof debt and licensing

An imported upstream `sorry` remains a proof gap. Record the exact source revision and
declaration in the upstream and downstream audit baselines. Never describe the integrated
library as having zero admissions when the source carries inherited debt. Newly written
compatibility proofs must not introduce admissions or additional axioms.

Preserve upstream copyrights and Apache-2.0 notices. The downstream contribution policy and
dual-license terms continue to apply to the contributions covered by that policy; importing
upstream code does not relicense it. Research evidence is retained according to
[generated-files.md](generated-files.md#research-evidence-retention).

The native seam foundations now prove equality in distribution before taking a measure view.
This matters for support on uncountable result/state types: the product sigma-algebra of two
discrete spaces need not itself be discrete. The support bridge uses native `EvalDistEq` and its
map/bind laws directly. Legacy generic per-query premises explicitly use the all-subsets joint
observation they required under the former PMF semantics.

Public theorem ownership is recorded in `scripts/integration/sequential-output-api-migration.json`.
The old positive-length append discharge, support-faithful Sumcheck construction, legacy lens
coherence construction, and completed failing-deterministic Sumcheck RBR construction have distinct
names from the canonical owners. The latter completed proof is retained because the canonical
RBR composition owner still has inherited upstream admitted debt. A proposition in
`Whir113Keystone` naming an old completeness target is explicitly named `legacyResidual`; it is
not confused with the completed theorem. Existing audit prints that expose inherited canonical
debt remain active; new helper axiom checks are recorded separately.

The canonical sumcheck verifier checks the prover's message polynomial. The old downstream
input-oracle rejection argument therefore does not establish a constant knowledge state or
zero-error soundness for that verifier. The checked regression in
`ArkLibTest/Compatibility/SumcheckMessageSemantics.lean` uses `ZMod 2`, input polynomial `X`,
domain `{1}`, target `0`, message `0`, and challenge `0`: the input relation fails, the canonical
verifier accepts, and the output relation holds. Exact retired proofs and dependent Logup
capstones are archived in `scripts/integration/sumcheck-message-semantics-retirements.json`.
Completed deterministic execution and composition constructions are retained. The affected Spartan
knowledge assemblies have distinct `_of_sumcheck_rounds` names and explicit actual degree-2 or
degree-3 round knowledge premises, named by `Sumcheck.Spec.RoundKnowledge`. This predicate has no
instance or automatic proof; it does not discharge the upstream knowledge-soundness proof debt.


The completed downstream Spartan first-challenge phase has the explicit entry point
`Spartan.Spec.oracleReduction.completedFirstChallenge`, defined in
[`SpartanFirstChallenge.lean`](../../ProximityPrize/Compatibility/SpartanFirstChallenge.lean).
It consumes the post-first-message `Unit` witness and reuses the completed concrete prover and
native verifier. Canonical `oracleReduction.firstChallenge` retains its inherited admitted
definition and its original `Witness R pp` input interface. The completed
`completedFirstChallenge_perfectCompleteness` theorem and its downstream consumers target the
explicit completed entry point; they make no completion claim about the admitted canonical
constructor. Exact original commands, renamed guarantees, and the consumer mapping are in
[`spartan-first-challenge-migration.json`](../../scripts/integration/spartan-first-challenge-migration.json).

The same boundary applies to `sendEvalClaim` and `linearCombination`: their inherited admitted
constructors retain the canonical interfaces. `completedSendEvalClaim` and
`completedLinearCombination` explicitly assemble the completed downstream programs with the
post-first-sumcheck `Unit` witness and the canonical scalar claim family. The bundled prover message
is exposed through canonical virtual output queries, rather than an obsolete bundled output oracle.
The composed downstream reduction uses these three completed phase constructors and its four
existence/constructor anchors pass the standard-three-axiom audit. Exact pre-routing commands and
canonical command hashes are recorded in
[the evaluation-claim mapping](../../scripts/integration/spartan-send-eval-claim-migration.json) and
[the linear-combination mapping](../../scripts/integration/spartan-linear-combination-migration.json).
These receipts do not assert completion of the inherited canonical admitted constructors.

Large concrete finite types need symbolic cardinality transport before instantiation. Prove the
whole dimension or syndrome implication over `Fin n`, rewrite `Fintype.card_fin` while `n` is a
variable, and only then instantiate a production length such as `2^30`. Otherwise definitional
comparison of a numeric budget with `Fintype.card (Fin (2^30))` can enumerate the finite type.
The G87 syndrome bridge follows this pattern without changing its nineteen public contracts;
its exact original source, twelve axiom reports, and separate source/package validation status
are recorded in [the G87 migration audit](../../scripts/integration/g87-syndrome-symbolic-migration.json).

Evaluation-code parameters also need their precise convention: `KKH26.evalCode g n d` uses
degree at most `d`, whereas `rsCode dom k` uses degree below `k`. For positive `k`,
`Ownership.evalCode_pred_eq_rsCode` proves the `k - 1` conversion while `k` is symbolic, before
specializing a large dimension. The four canonical incidence clients reuse that owner without
changing their numeric bounds ([caller audit](../../scripts/integration/full21-incidence-evaluation-code-ports.json)).

The same symbolic boundary applies to large polynomial locators: prove their degree, exact root
set, and whole codeword membership for an arbitrary number of factors before instantiating a
production finite set. The full-scale incidence construction keeps all fifty-five public
contracts and its original kernel certificate while using these private symbolic proofs; see
[the locator migration audit](../../scripts/integration/incidence-full-scale-symbolic-migration.json).
