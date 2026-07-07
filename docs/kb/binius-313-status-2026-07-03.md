# Binius #313 — build status + remaining error surface (2026-07-03)

STATUS NOTE (not a certification). Successor to
`docs/kb/binius-313-closeout-2026-07-02.md`. This note records the **authoritative
focused-cone-build surface** that the 2026-07-02 note deliberately skipped, and
partitions every remaining error into (a) two maintainer-gated structural blockers
and (b) mechanically-isolated substrate-API drift.

## TL;DR

- **The math residuals are done.** All four #313/#317/#327 named residuals are
  discharged or refuted-with-replacement, and the discharge modules are in-tree
  (`Code.lean`, `FoldDetSplit.lean`/`FoldDetDischarge.lean`, `ReductionLogic.lean`,
  `ExtractMLPCorrectness.lean`). Unchanged from 2026-07-02.
- **The cone still does NOT build**, and it is **not closeable-as-green under the
  proofs-only mandate** (no `sorry`/`admit`/`native_decide`, no statement
  weakening). Two of the failures are **statement-level / substrate-level** and
  require maintainer design decisions; they cannot be repaired by proof-body edits
  alone.
- **`QueryPhase.lean` = 18 errors** (authoritative focused cone build, 2026-07-03;
  a solo `lake env lean` grep counted 17, missing the 511 `unknown identifier`
  cascade line). Partition: **Blocker A** (ill-typed statement, 3 errors incl.
  cascade 511/518), **Blocker B** (fold-order vs statement-order reversal cluster,
  9 errors incl. cascade 2303/2441), **6 isolated** substrate-API drift errors.
- **`Steps/Fold.lean` = 11 errors** (authoritative focused cone build) — the toFun
  `simulateQ`/`support` normalization pair (593, 670), the reversal HEq cluster
  (1118, 1190, 1344, 1348, 1366, 1387, 1533, 1560 — `afterSlice`/`beforeSlice`
  raw-vs-`foldOrderChallenges`), and one anonymous-constructor type (1776).
- **`Steps/FinalSumcheck.lean` = GREEN** (0 errors; the focused cone build compiled
  it clean — confirms the FSC lane's green claim, supersedes the 2026-07-02
  "inconclusive/timeout").
- **29 leaf errors total** (`Fold` 11 + `QueryPhase` 18); entry files
  (`General`/`FRIBinius.General`/`BBFSmallFieldIOPCS`) are unreachable behind the
  leaf failures.
- Recommendation: **BLOCKED, not closeable today.** See the verdict section.

## Build method

Substrate oleans are current and coherent (`Code.lean` and all `Prelude`/`Basic`/
`Relations`/`Compliance` deps build green — the 2026-07-02 note's implication that
"no Binius olean exists" is about the three failing leaves only; their imports are
built, so `lake env lean <leaf>` elaborates the leaf against fresh substrate oleans
with no lock). Per-file surface via `lake env lean`; authoritative full surface via
the focused cone build
`./scripts/lake-locked.sh build ArkLib.ProofSystem.Binius.BinaryBasefold.General
ArkLib.ProofSystem.Binius.FRIBinius.General ArkLib.ProofSystem.Binius.BBFSmallFieldIOPCS`.

Caveat learned this session: **two concurrent `lake env lean` runs kill each
other** on this contended shared box (output truncates mid-token, outer shell
reports 127). Run the leaves sequentially, or use the lock-holding focused build to
get an uncontended surface.

## QueryPhase.lean — 18 errors (authoritative focused cone build, 2026-07-03)

### Blocker A — ill-typed statement (maintainer-gated). Errors 369, 511, 518.

`iteratedQuotientMap_eq_qMap_total_fiber_extractMiddleFinMask` (QueryPhase.lean:361).
The `iteratedQuotientMap` refactor changed its result type to be indexed by
`⟨(iₚ).val + k, _⟩`. The statement feeds `iₚ := ⟨0,_⟩`, so the inner
`iteratedQuotientMap (i:=⟨0,_⟩) (k:=destIdx.val) v` has type
`sDomain … ⟨0 + destIdx.val, _⟩`, while `qMap_total_fiber i steps _` demands its
`y` argument at `sDomain … ⟨i.val + steps, _⟩` (`Prelude.lean:212-216`). The two
indices are equal only via `h_destIdx : destIdx.val = i.val + steps` — **not
definitionally** (`0 + x` does not reduce on `ℕ`, and `destIdx.val` ≠ `i.val+steps`
without the hypothesis). Elaborating the *statement* therefore grinds `isDefEq`
to the heartbeat cap (369: timeout at 1,000,000; the lane reports it still times
out at 4,000,000 — i.e. this is a genuine non-defeq, not slowness). Because the
lemma fails to register, its own consumer inside `query_phase_consistency_guard_safe`
gets **`unknown identifier`** at 511 and the dependent `rw` fails at 518.

Fixing it requires an **explicit index cast in the statement** (a `h_destIdx ▸` /
`Fin.cast` reconciling `sDomain ⟨0+destIdx.val⟩` with `sDomain ⟨i.val+steps⟩`) **or
re-typing the substrate** so `iteratedQuotientMap`/`qMap_total_fiber` share a
`Fin ℓ`-consistent index convention. Both are statement/substrate changes with a
large consumer fan-out (the "`i : Fin r` fed to `Fin ℓ`-typed functions" design
issue). Out of the proofs-only lane; needs maintainer design intent.

### Blocker B — fold-order vs statement-order reversal cluster (maintainer-gated). Errors 1768, 1809, 1842, 1864, 1870, 1940, 2110 (+ cascade 2303, 2441).

`logical_checkSingleRepetition_of_mem_support_forIn_body`. Minimal failing goal
(1842, `rfl`):

```
LHS  single_point_localized_fold_matrix_form … (fun j => foldOrderChallenges stmtIn.challenges ⟨(k-1)·ϑ+j⟩) …
RHS  single_point_localized_fold_matrix_form … (fun j => stmtIn.challenges                     ⟨(k-1)·ϑ+j⟩) …
```

`foldOrderChallenges c = fun j => c (Fin.rev j)` (`Basic.lean:49`). The logical spec
(`logical_computeFoldedValue`, fold-order) carries the `Fin.rev` reversal; the
monadic honest prover (`checkSingleFoldingStep`) carries the raw statement-order
vector. They are **not defeq** — they differ by `Fin.rev`. The surrounding `omega`
(1809), `simp` (1864/1870/1940/2110), and the two downstream completeness theorems
`queryPhaseLogicStep_isStronglyComplete` (2303) and its sibling (2441, both stuck on
an underdetermined `Fact (ϑ ∣ ℓ)` metavar) are all cascades of this one mismatch.

Reconciling requires authoring the currently-nonexistent `foldOrderChallenges`
**snoc-reindexing bridge** (only `foldOrderChallenges_cons`, the wrong direction,
exists — `Basic.lean:54`) **and** redefining the raw honest-prover side to fold
order. The raw side originates in the honest-prover substrate
(`checkSingleFoldingStep`), not in QueryPhase. Triple-witnessed as maintainer-grade
(see `BinaryBasefold/docs/reversal-cluster-diagnosis-2026-06-24.md`). Out of lane.

### Isolated substrate-API drift (6). Errors 305, 596, 1008, 2158, 2694, 2865.

These are "the tactic no longer matches the drifted goal", each needing the live
goal state; none is a `sorry`/statement change, but each is a *guess* risk (the
prior 305 attempt regressed) and **none changes the verdict** — even fixed, the cone
stays red on Blockers A/B. Documented, not guessed, per the "do not guess" rule.

- **305** `mem_support_queryFiberPoints` — `simp` made no progress on the final
  `Array.getElem_finRange, Fin.cast_mk, Fin.eta` step; the OptionT
  `support (some <$> (query.cont <$> pure …))` no longer reduces membership→equality
  under the current simp set.
- **596** `query_phase_step_preserves_fold` — `typeclass instance problem is stuck:
  Fact (?m ∣ ?m)`; a `Fact (ϑ ∣ ℓ)` divisibility metavar left undetermined at proof
  end (goal `⊢ iterated_fold 𝔽q β 0 (k·ϑ) …`). Needs an explicit instance/type
  annotation to pin the metavar.
- **1008** `query_phase_final_fold_eq_constant` — `dsimp only [getFirstOracle]` made
  no progress (head symbol drifted).
- **2158** — `rw [bind_assoc]` pattern `?x >>= ?f >>= ?g` absent; the term is
  already `do`-desugared / right-associated. Needs `simp only [bind_assoc]` or a
  reshaped chain.
- **2694** `queryOracleVerifier_rbrKnowledgeSoundness` — `simp only [… ] at hDir`
  made no progress.
- **2865** same theorem — `let q : OracleQuery [pSpec.Challenge]ₒ _ := query ⟨⟨0, by
  rfl⟩, ()⟩`: the `_` response type is undetermined, so the anonymous constructor's
  type cannot be inferred. Needs the concrete challenge-response type ascription.

## Steps/Fold.lean — 11 errors (focused cone build, authoritative)

Partition mirrors QueryPhase.

**Reversal HEq cluster (maintainer-gated) — 1118, 1190, 1344, 1348, 1366, 1387,
1533, 1560 (8 errors).** `afterSlice`/`beforeSlice` are built in raw statement order
(`Fin.snoc stmtIn.challenges r_i' ⟨j·ϑ+cId⟩`, Fold.lean:1060-1069 and the
`getLastOraclePositionIndex` variant at 1319-1344), but the consumer
`incrementalBadEventExistsProp` (`Relations.lean:410`) passes
`fun cId => foldOrderChallenges challenges ⟨…⟩` — the `Fin.rev`-reversed fold-order
view. `fin_fun_heq_of_cast` cannot bridge the raw↔wrapped `HEq` because the block
index differs by `Fin.rev`. **Identical root cause to QueryPhase Blocker B**; the fix
is the same missing `foldOrderChallenges` snoc-reindexing bridge + redefining the raw
side. Out of the proofs-only lane.

**toFun `simulateQ`/`support` normalization (isolated drift) — 593, 670 (2 errors).**
`foldKnowledgeStateFunction.toFun_full` pos/neg branches. The `verifierCheck` ite is
buried under `simulateQ impl (simulateQ (simOracle2 …) …)`; after `erw
[simulateQ_bind]` the `simp only [simulateQ_pure, …]` (593) makes no progress and
`erw [support_pure]` (670) cannot find `_root_.support (pure ?x)` — the term is now
`PFunctor.FreeM.pure`/`OptionT.pure`, a syntactic mismatch. Needs the
`foldOracleVerifier_toVerifier_failingDet` determinism collapse reproduced inline
(the sibling in `VerifierDeterminism.lean` is cross-file → circular) plus `erw`
rather than `simp only` for the `FreeM.pure`/`OptionT.pure` steps.

**Anonymous constructor (isolated drift) — 1776 (1 error).** Identical to QueryPhase
2865: `let q : OracleQuery [(pSpecFold).Challenge]ₒ _ := query ⟨⟨1, by rfl⟩, ()⟩`
needs the concrete response-type ascription for `_`.

## Steps/FinalSumcheck.lean — GREEN (0 errors)

The focused cone build compiled `Steps/FinalSumcheck.lean` clean (imported via
`Steps.lean`; produced no error lines — the build proceeded past it to fail only on
`Fold` and `QueryPhase`). This **confirms the FSC lane's green claim** and supersedes
the 2026-07-02 note's "inconclusive (timeout >400 s)". 14
`linter.unusedSimpArgs`/style warnings remain in the pre-existing
`perfectCompleteness` proof (non-blocking).

## Downstream entry files (General / FRIBinius.General / BBFSmallFieldIOPCS)

These **cannot be elaborated** while `QueryPhase`/`Fold` fail — they import those
modules, so lake never produces the leaf oleans and the entry files never compile.
The focused build reports the two leaf failures and does not reach the entry-file
bodies. **Consequence:** any *genuine* downstream API drift in the entry files is
currently invisible — it can only be surfaced after the leaves are green. The entry
files are parameterized over the role-named `Prop` hypotheses listed below (the
modularity convention), so they are not expected to carry new proof obligations
beyond those transports.

## Named-residual census (unchanged; math done)

All four issue-named residuals remain discharged/refuted-with-replacement in-tree
(see 2026-07-02 note for the per-residual detail):
`ExtractMLPCorrectnessResidual` (refuted-with-replacement, DP24 §4 endianness
correction), `FoldPreservesBBFCodeMembershipResidual` (discharged, `Code.lean`),
`FoldMatrixDetNeZeroResidual` (discharged, `FoldDetSplit`/`FoldDetDischarge`),
`FinalSumcheckStepLogicCompleteResidual` (discharged,
`ReductionLogic.finalSumcheckStep_is_logic_complete`). The cone-entry files carry
role-named `Prop` completeness/rbr-KS hypotheses (`BBFInnerPerfectCompleteness`,
`BBFInnerRbrKnowledgeSoundness`, `hCoreInteractionAppendRbrKnowledgeSoundness`,
`hBatchingCoreAppendRbrKnowledgeSoundness`, `hFullAppendRbrKnowledgeSoundness`,
`hFullProtocolCompleteness`, …) — the deliberate modularity ("named residual")
convention, not incompleteness.

## Verdict

**#313 is NOT closeable-as-green today.** Authoritative focused-cone-build surface:
`FinalSumcheck` green; `Fold` 11 errors; `QueryPhase` 18 errors (29 leaf errors
total); entry files unreachable behind the leaf failures.

Of the 29, **20 are the two maintainer-gated structural blockers**:

- **Reversal cluster** (fold-order `foldOrderChallenges`/`Fin.rev` spec vs raw
  statement-order honest prover): QueryPhase 1768/1809/1842/1864/1870/1940/2110 +
  cascade 2303/2441 (9) and Fold 1118/1190/1344/1348/1366/1387/1533/1560 (8) = 17.
  Requires authoring the missing `foldOrderChallenges` snoc-reindexing bridge **and**
  redefining the raw honest-prover side (`checkSingleFoldingStep`) to fold order — a
  substrate change, triple-witnessed as maintainer-grade.
- **`iteratedQuotientMap_eq_qMap_total_fiber_extractMiddleFinMask` ill-typed
  statement**: QueryPhase 369 + cascade 511/518 = 3. Requires an explicit index cast
  in the statement or an `iteratedQuotientMap`/`qMap_total_fiber` index-convention
  retype — a statement/substrate change with large consumer fan-out.

Both are explicitly outside the proofs-only mandate (no statement weakening; a cast
that fixes ill-typedness still changes the statement text and ripples to consumers
whose intended shape only the maintainer can fix). Independently triple-witnessed
(2026-06-24 cold-trace diagnosis; three repair lanes this session; this session's
source confirmation).

The remaining **9 are isolated substrate-API drift** (QueryPhase 305/596/1008/2158/
2694/2865; Fold 593/670/1776) — "the tactic no longer matches the drifted goal."
Each needs live goal-state iteration; per the "do not guess" rule (and the prior 305
regression) they are documented above, not blind-patched. Crucially, **fixing all 9
would still leave the cone red** on the 20 structural-blocker errors, so they do not
change the closeability verdict.

**Recommendation: keep #313 OPEN, BLOCKED on the substrate-API migration**
(reversal-order reconciliation + `iteratedQuotientMap`/`qMap_total_fiber` index
retype), which is maintainer-grade multi-file work. The mathematical closeout stands
(4/4 named residuals discharged/refuted; composition seam = deliberate modularity
convention). Correct public state: **math done; build red on two maintainer-gated
structural blockers + isolated API drift; closeout pending the substrate port.**

## Draft #313 closing comment (DO NOT POST — recommendation is to keep OPEN)

> Status update (2026-07-03). Ran the authoritative focused cone build
> (`General` / `FRIBinius.General` / `BBFSmallFieldIOPCS`). Result: `FinalSumcheck`
> now builds green; `QueryPhase` (18) and `Steps/Fold` (11) remain red; entry files
> are unreachable behind those two leaves. No `sorry`/`admit`/`native_decide` anywhere
> in the cone; every failure is substrate-API/index drift. The four issue-named
> residuals remain discharged/refuted-with-replacement in-tree. Two structural
> blockers (the fold-order↔statement-order `foldOrderChallenges` reversal cluster,
> and the ill-typed `iteratedQuotientMap_eq_qMap_total_fiber_extractMiddleFinMask`
> statement) are maintainer-grade substrate/statement changes and cannot be repaired
> under a proofs-only mandate. **Recommend keeping #313 open, blocked on the
> substrate-API migration**, not closing as green. Full surface + goal states:
> `docs/kb/binius-313-status-2026-07-03.md`.
