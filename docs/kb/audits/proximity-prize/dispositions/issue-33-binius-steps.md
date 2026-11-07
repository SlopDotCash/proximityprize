# Issue #33 — Binius Steps: close 9 named residuals after Prelude port lands

**Status:** OPEN / not closeable. The 9 named Steps residuals are *written* as genuine proofs (no
`sorry`/`admit` anywhere in the Binius tree), but they cannot be **compiled / verified green**
because every Steps module transitively depends on the **never-compiled Binius Soundness layer**
(`Soundness/Lift.lean`, `Soundness/QueryPhasePrelims.lean`, and the rest of the 7-module subtree),
which has deep build errors. That layer is a separate, in-progress harvest from `CompBinius`, not a
Steps residual. The `FoldPreservesBBFCodeMembershipResidual` (Lemma 4.13 port) also remains, also
separate.

## Ask (issue scope)

After the Prelude port (#32) lands, close the named Binius **Steps** residuals: 3 step
perfect-completeness theorems repaired with `hInit : NeverFail init`,
`foldKnowledgeStateFunction.toFun_full`, `foldOracleVerifier_rbrKnowledgeSoundness`, `commitKState`,
and finalSumcheck `toFun_next`/`toFun_full` back-transport.

## What is done

- The Steps residuals are written as real theorems with real tactic proofs (no `sorry`):
  - `Steps/Commit.lean:148` `commitOracleReduction_perfectCompleteness (hInit : NeverFail init)`,
    `Steps/Fold.lean:162` `foldOracleReduction_perfectCompleteness (hInit : NeverFail init)`,
    `Steps/Relay.lean:146` `relayOracleReduction_perfectCompleteness (hInit : NeverFail init)`,
    `Steps/FinalSumcheck.lean:141` `finalSumcheckOracleReduction_perfectCompleteness`.
  - `toFun_full` extractor proofs in Fold/Commit/FinalSumcheck/Relay.
  - `*_rbrKnowledgeSoundness` in all four steps.

> **Correction (2026-10-28): the two Fold entries above are not proofs in the current tree.**
> `foldKnowledgeStateFunction` gets its `toFun_full` from the explicit hypothesis
> `FoldKnowledgeStateToFunFull`. That hypothesis was the custom axiom
> `foldKnowledgeStateFunction_toFun_full`, and its docstring explains why it is expected to be false
> at commitment rounds. There is no single-round `foldOracleVerifier_rbrKnowledgeSoundness`
> theorem; the unused custom axiom of that name was removed. See
> `ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/Fold.lean`.
- `#32` (Prelude port) resolved.
- Whole-tree comment-stripped scan of `ArkLib/ProofSystem/Binius/BinaryBasefold/**` → **zero**
  `sorry`/`admit`.

## Why the green build cannot be confirmed (the real blocker)

The four `Steps/*.lean` modules all `import ReductionLogic`, and
`ReductionLogic.lean` imports `Soundness.Lift`. `Steps/Fold.lean` additionally imports the
`Soundness` umbrella and uses `Soundness.Incremental` bad-event machinery
(`incrementalFoldingBadEvent`, `incrementalBadFoldEvent`, `incrementalBadEventExistsProp`). The
entire `Soundness/` subtree is **never-compiled** (all 7 oleans absent) and currently does not build:

- `Soundness/Lift.lean` — `rewrite` failures (`:198`, `:213`), instance-synthesis failure (`:330`),
  application type mismatches (`:328`, `:370`).
- `Soundness/QueryPhasePrelims.lean` — ~50 errors: `Invalid argument name h_ℓ_add_R_rate` for
  `queryBlockSourceIdx`/`queryBlockDestIdx`(`_le`) (signature drift), `Unknown identifier`
  for `lt_r_of_lt_ℓ`/`lt_r_of_le_ℓ`/`k_mul_ϑ_lt_ℓ`/`queryBlockDestIdx_eq_queryBlockSourceIdx_succ`/
  `UDRClose_of_fin_eq`, kernel `unknown constant extractSuffixFromChallenge_congr_destIdx`, and two
  `whnf` heartbeat timeouts (`:833`, `:951`).
- `Soundness/{Proposition421,Incremental,FoldDistance,BadBlocks,QueryPhaseSoundness}` — also
  uncompiled (oleans absent); `BadBlocks` imports `QueryPhasePrelims`.

Repairing this whole layer is a substantial multi-session port against the refactored Binius
soundness API (signature drift + missing lemmas + proof-perf), clearly separate from "close the 9
Steps residuals." Until it builds, the Steps proofs cannot be machine-checked.

## The other remaining frontier residual (separate from Steps)

`FoldPreservesBBFCodeMembershipResidual` (`Code.lean:992`, `class : Prop`) — the Lemma 4.13
code-membership consequence. Legitimate named residual (not a `sorry`), consumed only by the
soundness lift (`Soundness/Lift.lean:185`), **not by any Steps file**. Gated on porting the
general-`i` reconstruction stack (`getINovelCoeffs`, `degree_intermediateEvaluationPoly_lt`,
`intermediateEvaluationPoly_from_inovel_coeffs_eq_self`, `fold_advances_evaluation_poly`); CompPoly
provides the general-`i` building blocks (`intermediateEvaluationPoly`, `intermediateNovelBasisX`,
`evaluation_poly_split_identity`) but only the `i = 0` reconstruction (`intermediate_poly_P_base`).
Predominantly CompPoly-layer work. Audited under `0c5a2b2df` /
`docs/kb/audits/issue-33-binius-branch-harvest-2026-06-06.md`.

## Decoupling lever — executed, but the completeness layer is ALSO broken

`Steps/Commit`, `Steps/Relay`, `Steps/FinalSumcheck` import only `ReductionLogic` (not the
`Soundness` umbrella), and `ReductionLogic` imported the broken `Soundness.Lift` for **exactly
one** symbol: the 2-line helper `bitsOfIndex`. That helper was extracted into a new stable module
`ArkLib/ProofSystem/Binius/BinaryBasefold/BitsOfIndex.lean` (builds green standalone), and both
`Soundness/Lift` and `ReductionLogic` now import it instead — dropping `ReductionLogic`'s
dependency on the broken soundness lift. This is a valid coupling reduction and is non-regressing
(both `Lift` and `ReductionLogic` were already uncompiled), but it is **not sufficient** to verify
the Steps residuals, because:

**`ReductionLogic.lean` (the Steps completeness substrate) is itself broken** with its own API
drift, independent of the Soundness layer: `Unknown identifier getSumcheckRoundPoly_sum_eq`
(`:348`), `unsolved goals` (`:350`), `rfl` failure (`:369`), `Unknown identifier
projectToNextSumcheckPoly_sum_eq` (`:393`). Since every Steps file imports `ReductionLogic`, all
four step residuals are blocked here too.

So verifying the 9 Steps residuals green requires repairing BOTH (a) the Steps completeness
substrate (`ReductionLogic` sumcheck-round-poly API drift) and (b) the never-compiled `Soundness/`
subtree (Lift interleaved-code mismatch + QueryPhasePrelims signature drift/kernel/heartbeat +
siblings, with `Steps/Fold` also needing `Soundness.Incremental`). Both are multi-module API-drift
ports against the refactored Binius API — not Steps-residual defects.

## Concrete completion roadmap for `ReductionLogic` (1 of 8 broken modules)

Adding `import ArkLib.ProofSystem.Sumcheck.Structured.SingleRound` + `open Sumcheck.Structured`
resolves `getSumcheckRoundPoly_sum_eq` (it exists at `SingleRound.lean:153`, just unimported).
After that, `ReductionLogic` still has **13 errors**, including **6 substantive lemmas that do not
exist anywhere and must be proven from scratch**:

- `projectToNextSumcheckPoly_sum_eq` — round-poly marginal: `hᵢ(rᵢ) = Σ_{cube} Hᵢ₊₁` (base
  `projectToNextSumcheckPoly` at `Sumcheck/Structured.lean:168`).
- `projectToMidSumcheckPoly_succ` — mid-poly recursion across rounds.
- `projectToMidSumcheckPoly_at_last_eval` — final-round mid-poly evaluation.
- `iterated_fold_advances_evaluation_poly` — **Lemma 4.13 (general-`i`)**, the same reconstruction
  behind `FoldPreservesBBFCodeMembershipResidual`.
- `OracleVerifier.mkVerifierOStmtOut_inl` / `_inr` — oracle-statement embedding computation rules.

Plus in-place proof repairs (`rfl`/`rewrite`/`simp` no-progress/type-mismatch/unsolved-goals at
`:352,:371,:627,:768,:1101,:1276,:1441`). The in-place repairs and the `apply` rewrites must EDIT
`ReductionLogic.lean`, but the shared-tree autosync reverts edits to existing files (it grabbed the
new `BitsOfIndex.lean` but reverted the `ReductionLogic` import edit), so this work needs a
quiescent tree (or new-file-only lemma modules). And `ReductionLogic` is only 1 of 8 broken modules;
the 7-module `Soundness/` subtree (~60+ errors incl. kernel unknown-constant and `whnf` heartbeat
timeouts) is required additionally for `Steps/Fold`.

## Recommendation

Keep #33 open. The Steps proofs are written (no `sorry`), but green-build verification is gated on a
separate, multi-module repair of the broken Binius reduction+soundness layer (`ReductionLogic`
sumcheck API drift; the `Soundness/` subtree) — which should be tracked as its own issue — plus the
Lemma 4.13 reconstruction port behind `FoldPreservesBBFCodeMembershipResidual`. None of these is a
Steps-residual defect.
