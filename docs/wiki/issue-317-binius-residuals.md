# Issue #317: Binius Residual Scratchpad

Status: **historical scratchpad** (last substantive update 2026-06-11). The inventory,
progress log, and build receipts below are pinned to the pre-consolidation tree of that date and
are not authoritative for the current tree; several module paths they cite no longer exist.
For current open residuals use [`residual-census.md`](residual-census.md).

Issue: #317 in this repository (`SlopDotCash/proximityprize`). The historical issue link
pointed at a different fork and is not an authority for current status.

## Current navigation (verified against the source tree, 2026-10-29)

The Soundness modules were consolidated after this scratchpad was written. The old paths
`Soundness/Proposition421.lean`, `Soundness/PreTensorFiber.lean`,
`Soundness/Prop421Case1Discharge.lean`, and `Soundness/Prop421Case2Assembly.lean` (and the other
`PreTensor*.lean` files listed in the progress log) do not exist; do not try to build them.
Current locations, all under `ArkLib/ProofSystem/Binius/BinaryBasefold/`:

- Proposition 4.21 case 1 (fiberwise close): `Soundness/Case1.lean`
  (`prop_4_21_case_1_fiberwise_close`). The `Prop421Case1FiberwiseCloseResidual` name survives
  only in that module's prose.
- Proposition 4.21 case 2 (fiberwise far): `Soundness/SoundnessCase2Probability.lean`
  (`prop421Case2_probability_bound`, `prop_4_21_case_2_fiberwise_far`), with
  `Soundness/SoundnessCase2Assembly.lean` and `Soundness/SoundnessCase2FarLift.lean` holding the
  bridge-parameterized forms. `Soundness/SoundnessCase2Discharge.lean` only records that the
  former `Prop421Case2FiberwiseFarResidual` class was retired.
- Lemma 4.22 joint proximity: `Soundness/Lift.lean`
  (`preTensorCombine_jointProximityNat_of_fiberwiseClose`); the contrapositive
  `not_jointProximityNat_of_not_fiberwiseClose` is in `Soundness/PreTensorMaps.lean`.
- Incremental Proposition 4.21.2 statements: the downstream extension
  `ArkLib/Extensions/ProofSystem/Binius/BinaryBasefold/Soundness/Incremental.lean`.
- Query-phase preliminaries and suffix alignment: `Soundness/QueryPhasePrelims.lean`,
  `Soundness/SuffixFiberAlignment.lean`. No `PreviousSuffixFiberAlignmentResidual`,
  `ExtractMLPCorrectnessResidual`, or `FinalSumcheckStepLogicCompleteResidual` declaration is
  present in the current tree; `ExtractMLPCorrectness.lean` keeps the corrected
  `extractMLP_zero_eq_some_revIndexMLP_iff`.
- Fold-matrix determinant: the destination-indexed `foldMatrix_det_ne_zero` is in the canonical
  `Prelude/Folding.lean`; `FoldDetSplit.lean` and `FoldDetDischarge.lean` still contain real
  recursive `foldMatrixNat_det_ne_zero` proofs (the two developments overlap). This note does not claim a fresh elaboration of those files.

Check current status with the locked recipe from [`quickstart.md`](quickstart.md), e.g.
`./scripts/lake-locked.sh build ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.Case1`
(never a bare `lake build`). The `lake build` / `lake env lean -j1 -M4096` lines in the progress
log below are historical receipts, not current instructions.

## Source Trail

- Diamond--Posen, *Polylogarithmic Proofs for Multilinears over Binary Towers*,
  IACR ePrint 2024/504: <https://eprint.iacr.org/2024/504>.
  Relevant anchors: Definition 4.6 / 4.8 folding, Lemma 4.9 fold-matrix form and
  invertibility, Construction 4.12, Theorem 4.13 completeness, Theorem 4.17 soundness,
  Definition 4.20 good/far cases, Proposition 4.21, and Lemma 4.22.
- Zeilberger--Chiesa, *BaseFold*, IACR ePrint 2023/1705:
  <https://eprint.iacr.org/2023/1705>. Useful for the older fold-matrix intuition and
  code-switching comparison; not the main source for the Binius residuals.
- Diamond--Guo, *Proximity Gaps in Interleaved Codes*, IACR ePrint 2024/1351:
  <https://eprint.iacr.org/2024/1351>. Relevant anchors: Theorem 3.1 affine gaps lift to
  interleaved codes, Theorem 3.6 tensor-style gaps, Corollary 3.7 Reed-Solomon tensor gaps.
- Local harvest note:
  [`../kb/audits/issue-33-binius-branch-harvest-2026-06-06.md`](../kb/audits/issue-33-binius-branch-harvest-2026-06-06.md).
  Stale Binius branches are useful for intent but should not be merged wholesale.

## Local Residual Inventory (historical, 2026-06-11)

The issue body names the Binius proof-system residuals that should become in-tree theorems or
honest smaller residuals. The local residual surfaces at the time of writing were:

- `Prop421Case1FiberwiseCloseResidual` and `Prop421Case2FiberwiseFarResidual` in
  `ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/Proposition421.lean`; both have in-tree
  instances.
- The old `Prop4212Case1Residual` and `Prop4212Case2Residual` classes are gone from
  `ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/Incremental.lean`; the current API exposes
  direct theorems `prop_4_21_2_case_1_fiberwise_close_incremental`,
  `prop_4_21_2_case_2_fiberwise_far_incremental`, and
  `prop_4_21_2_incremental_bad_event_probability`.
- `PreviousSuffixFiberAlignmentResidual` in
  `ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/QueryPhasePrelims.lean`; it has an in-tree
  instance in `Soundness/SuffixFiberAlignment.lean`.
- `ExtractMLPCorrectnessResidual` in `ArkLib/ProofSystem/Binius/BinaryBasefold/Relations.lean`.
- `FinalSumcheckStepLogicCompleteResidual` in
  `ArkLib/ProofSystem/Binius/BinaryBasefold/ReductionLogic.lean`.
No live `FoldMatrixDetNeZeroResidual`, `FoldPreservesBBFCodeMembershipResidual`,
`PreTensorCombineMultilinearResidual`, `FoldPreTensorCombineAffineSplitResidual`,
or `PreTensorCombineJointProximityResidual` class remains in the current working tree.

## Progress Log (historical receipts, 2026-06-10/11)

- `FoldMatrixDetNeZeroResidual`: already has in-tree discharge modules
  `FoldDetSplit.lean` and `FoldDetDischarge.lean`. The old residual class is gone; consumers now
  call `foldMatrix_det_ne_zero` directly.
- `Basic.lean` relay bookkeeping: repaired the challenge-order/older-frontier lemmas and added
  `getFoldingChallenges_proof_irrel` so relay preservation does not depend on proof-term identity.
  Targeted checks:
  - `lake env lean ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean`
  - `lake build ArkLib.ProofSystem.Binius.BinaryBasefold.Basic:olean`
- `FoldPreTensorCombineAffineSplitResidual`: discharged in
  `Soundness/Incremental.lean` as
  `fold_preTensorCombine_eq_affineLineEvaluation_split`. The live theorem is a row-stack
  equality; a private pointwise helper keeps the proof term small enough for targeted builds.
  Axiom audit reports only standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).
- `PreTensorCombineMultilinearResidual`: removed from `Soundness/Incremental.lean`.
  `iterated_fold_eq_multilinearCombine_preTensorCombine` is now an induction over the first
  challenge, using `multilinearCombine_recursive_form_first` and the affine split theorem.
  Targeted check:
  - `lake build ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.Incremental:olean`
  Latest narrow check after the row-stack bridge split passed on 2026-06-10.
- Bad-event disagreement surface: `foldingBadEvent`, `incrementalFoldingBadEvent`, and the full
  Proposition 4.21 close-branch statement now use `fiberwiseDisagreementSetPerFiber` for the
  close-case source disagreement set. Targeted checks:
  - `lake build ArkLib.ProofSystem.Binius.BinaryBasefold.Compliance:olean`
  - `lake build ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.Proposition421:olean`
- `PreviousSuffixFiberAlignmentResidual`: proved in
  `Soundness/SuffixFiberAlignment.lean` as `instPreviousSuffixFiberAlignmentResidual`. The
  aggregate `Soundness.lean` now imports that discharge module so the instance is available from
  the public soundness entry point. This still needs a clean focused build after the current
  long-running Lean jobs finish.
- `FinalSumcheckStepLogicCompleteResidual`: still live in the current tree. The verifier-check
  half is already factored as `finalSumcheckStep_verifierCheck_passed`; the relation-out half is
  isolated to the final constant consistency proof. The promising local bridge is
  `Reconstruct.FinalOracleBridge.strictOracleFoldingConsistency_last_getLastOracle_eq_prefixFold`,
  which should be composed with the final `ϑ` folds via `iterated_fold_transitivity` and the
  constant/evaluation lemmas from `Reconstruct.IteratedFoldToLevel`.
- `ExtractMLPCorrectnessResidual`: still live in `Relations.lean`, but
  `ExtractMLPCorrectness.lean` now shows the residual is false as stated for `ℓ ≥ 2`.
  The checked replacement is the reversed-index/UDR-guarded theorem
  `extractMLP_zero_eq_some_revIndexMLP_iff`, and the actually consumed uniqueness consequence is
  available as residual-free `firstOracleWitnessConsistencyProp_unique'`.
  `Steps/Fold.lean` and `BBFSmallFieldIOPCS.lean` have been moved off the false residual for
  their local uniqueness lemmas. `Steps/FinalSumcheck.lean` and
  `FRIBinius/CoreInteractionPhase.lean` now also use the corrected `revIndexMLP` witness and the
  UDR-guarded forward theorem instead of the false iff. The old theorem remains only in
  `Relations.lean` as a documented false residual/obstruction surface.
- `FoldPreservesBBFCodeMembershipResidual`: discharged in `Code.lean`. The final proof avoids the
  brittle intermediate novel-basis round trip: it shows the binary quotient map is a nonzero scalar
  multiple of `X^2 - X`, decomposes any polynomial of degree `< 2m` as
  `A(q_i(X)) + X * B(q_i(X))` with `deg A, deg B < m`, and computes the one-step fold on the two
  preimages in each fiber. Targeted checks passed on 2026-06-10:
  - `lake env lean -j1 -M4096 ArkLib/ProofSystem/Binius/BinaryBasefold/Code.lean`
  - `lake build ArkLib.ProofSystem.Binius.BinaryBasefold.Code:olean`
  - `lake env lean -j1 -M4096 ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/Lift.lean`
- `PreTensorCombineJointProximityResidual`: discharged as
  `preTensorCombine_jointProximityNat_of_fiberwiseClose`, factored across
  `Soundness/PreTensorFiber.lean`, `PreTensorDisagreement.lean`, `PreTensorHamming.lean`,
  `PreTensorUDR.lean`, `PreTensorClosest.lean`, `PreTensorCodeDistance.lean`, and
  `PreTensorDistance.lean`. The proof follows DP24 Lemma 4.22: row equality from equal source
  fibers, column-disagreement containment, a Hamming/cardinality bound, closest-codeword
  minimization, and the destination unique-decoding-radius arithmetic. Targeted checks passed on
  2026-06-10:
  - `lake env lean -j1 -M4096 ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/PreTensorFiber.lean`
  - `lake env lean -j1 -M4096 ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/PreTensorDisagreement.lean`
  - `lake env lean -j1 -M4096 ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/PreTensorHamming.lean`
  - `lake env lean -j1 -M4096 ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/PreTensorUDR.lean`
  - `lake env lean -j1 -M4096 ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/PreTensorClosest.lean`
  - `lake env lean -j1 -M4096 ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/PreTensorCodeDistance.lean`
  - `lake env lean -j1 -M4096 ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/PreTensorDistance.lean`
  - `lake build ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.Incremental:olean`

## Open Math/Definition Notes (historical, 2026-06-11)

- `Prop4212Case1Residual` and `Prop4212Case2Residual` have been removed from
  `Soundness/Incremental.lean`. Their content is now direct theorem surface:
  `prop_4_21_2_case_1_fiberwise_close_incremental`,
  `prop_4_21_2_case_2_fiberwise_far_incremental`, and
  `prop_4_21_2_incremental_bad_event_probability`. The case-2 proof uses the one-step
  affine/interleaved proximity gap via `case2_one_step_far_positive_probability` and
  `case2_one_step_far_final_probability`.
- `Prop421Case1FiberwiseCloseResidual` is discharged in
  `Soundness/Prop421Case1Discharge.lean`, and `Soundness.lean` now re-exports that module.
- `Prop421Case2FiberwiseFarResidual` has a discharge path:
  `Soundness/PreTensorFar.lean` now packages the Lemma 4.22 contrapositive
  (`not_jointProximityNat_of_not_fiberwiseClose`), and `Soundness/Prop421Case2Assembly.lean`
  installs `instProp421Case2FiberwiseFarResidual` from the proven fold/pre-tensor bridge plus the
  far-lift. A local `lake build
  ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.Prop421Case2Assembly:olean` attempt on
  2026-06-11 replayed dependencies for 900 seconds and timed out before producing a target
  diagnostic in the saturated local environment.
- `PreviousSuffixFiberAlignmentResidual`, `ExtractMLPCorrectnessResidual`, and
  `FinalSumcheckStepLogicCompleteResidual` remain theorem-scope surfaces in the current tree. For
  `ExtractMLPCorrectnessResidual`, do not try to instantiate the old iff: use the corrected
  `revIndexMLP` theorem or replace downstream statements that expect unreversed output.
- The next geometry lemma is the first-step analogue of
  `qMap_total_fiber_succ_peel_last`: split an `(n+1)`-step fiber index into low bit `idx % 2`
  (the fresh single-step fold) and high suffix `idx / 2`. Unlike the existing last-step peel,
  the first-step statement has a boundary case when `n = 0`: the tail source can be `ℓ`, so the
  existing `qMap_total_fiber_repr_coeff (i : Fin ℓ)` helper cannot be applied without a separate
  zero-suffix proof.

## Working Heuristics

- Prefer targeted checks over repo-wide rebuilds, using the serialized wrappers from
  [`quickstart.md`](quickstart.md): `./scripts/lake-locked.sh build <Module>` (never a bare
  `lake build` or `lake exe cache get` while other agents may be building).
- Do not hand-edit generated `ArkLib.lean`.
- Treat DP24 Proposition 4.21 / Lemma 4.22 and DG25 Theorems 3.1/3.6 as the external math map,
  but discharge anything already expressible from local definitions as Lean lemmas.
- If a residual cannot honestly be closed from the current formal surface, replace it only with a
  strictly smaller named residual and document the reduction.
