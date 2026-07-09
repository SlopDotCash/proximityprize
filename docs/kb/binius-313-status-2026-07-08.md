# Binius #313 — current closeout status (2026-07-08)

Issue: https://github.com/lalalune/ArkLib/issues/313

## Verdict

#313 is **not green / not closeable as finished** in the current checkout.

The named mathematical residual work still appears to be in tree, but the focused
Binius cone does not build. I did **not** push this state to `fork/main` as a
finished closeout, because doing so would publish a known-red Binius front door.

## Commands run

Focused cone:

```bash
./scripts/lake-locked.sh build \
  ArkLib.ProofSystem.Binius.BinaryBasefold.General \
  ArkLib.ProofSystem.Binius.FRIBinius.General \
  ArkLib.ProofSystem.Binius.BBFSmallFieldIOPCS
```

Result: failed. Required targets with logged failures:

- `ArkLib.ProofSystem.Binius.BinaryBasefold.QueryPhase`
- `ArkLib.ProofSystem.Binius.BinaryBasefold.Steps.Fold`

Direct leaf check:

```bash
./scripts/lake-locked.sh build ArkLib.ProofSystem.Binius.BinaryBasefold.QueryPhase
```

Result: failed earlier in the file than the focused-build tail suggests.

## Current failure surface

The direct `QueryPhase` build reports pre-front-door elaboration failures including:

- `mem_support_queryFiberPoints` type mismatch around line 323.
- arithmetic/index-cast drift around lines 540, 637, 665, 832.
- missing helper identifiers `qMap_total_fiber_congr_source_apply` and
  `single_point_localized_fold_matrix_form_congr_steps_index`.
- no-op / brittle tactic failures around lines 948, 1752, 2095, 2627.
- late support/lift ambiguity around `support_liftComp`.
- the response-type hole in the query oracle construction near line 2797.

The direct `Steps.Fold` build reports:

- no-op / brittle support simplification around lines 602 and 679.
- `badSumcheckEventProp` API drift: current definition expects functions `L → L`,
  while the file passes bounded polynomial subtypes directly around lines 1408,
  1575, and related consumers.
- an active `sorry` warning around line 1419 in the
  `foldStep_rbrExtractionFailureEvent_imply_sumcheck_or_badEvent` path.
- the same query response-type hole near line 1818.

## Operational note

The current local checkout is on `codex/normalized-square-grid-budget` with a large
dirty worktree, mostly proximity-gap work. Any final #313 push to `fork/main`
should be done from a clean branch/worktree and should stage only Binius closeout
files. Do not push the current dirty worktree wholesale to `main`.
