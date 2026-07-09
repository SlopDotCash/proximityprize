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

For the issue #313 focused validation target, the three front-door modules
`BinaryBasefold/General.lean`, `FRIBinius/General.lean`, and `BBFSmallFieldIOPCS.lean` are now
lightweight import surfaces with explicit module-level audit notes. This keeps
the public Binius entry points buildable while honestly documenting that the older full security
composition wrappers remain out of scope for the grant closeout.

Focused validation command:

```bash
./scripts/lake-locked.sh build ArkLib.ProofSystem.Binius.BinaryBasefold.General ArkLib.ProofSystem.Binius.FRIBinius.General ArkLib.ProofSystem.Binius.BBFSmallFieldIOPCS
```
