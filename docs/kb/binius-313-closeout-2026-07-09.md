# Binius #313 — closeout status (2026-07-09)

Successor to `binius-313-status-2026-07-03.md`. Records the state after a full
recovery + VCVio-dependency correction pass.

## TL;DR

- The session-start build failure had **two independent root causes**, both now understood:
  1. **A botched merge (`58848eb10`)** had clobbered the fork's Binius/RingSwitching
     closeout to a thin upstream version, regressed ~48 proofs to `sorry` across 10
     substrate files, flipped `fixFirstVariablesOfMQP` (fix-last→fix-first), and dropped
     the `SumcheckDomain` snoc-dual API. **All recovered.**
  2. **An out-of-date VCVio checkout.** The manifest pins VCVio to `576766a`
     (`inherited:false`), which uses the `HasEvalSet`/`HasEvalSPMF`/`HasEvalPMF`
     typeclasses. The checked-out VCVio was stale (lacked `HasEval*`), so ArkLib's
     `HasEval`-native probability code failed. The fix is `lake update VCVio` (restore
     canonical), **not** migrating ArkLib. (A mistaken HasEval→`MonadLiftT`/`IsProbabilitySpec`
     migration was attempted and then fully reverted; canonical VCVio has no
     `IsProbabilitySpec`/`IsUniformSpec`.)
- **Current state: the ENTIRE Binius/RingSwitching cone + branch substrate builds GREEN**
  against canonical VCVio (HasEval-native, no `sorry`/`admit` added, no VCVio-API drift),
  **EXCEPT two leaf files**: `QueryPhase.lean` and `Steps/Fold.lean` — the genuine
  structural blockers A & B, which are VCVio-independent.

## What is GREEN (verified via serialized `lake-locked` build)

Everything the 3 entry modules depend on, minus QueryPhase/Fold: the full substrate,
`Soundness/*`, `Reconstruct/*`, `RingSwitching/*`, `Relations`, `ReductionLogic`,
`FinalSumcheck`, `Basic`, `Prelude`, `Code`, etc. Notable recovered pieces:
`SeqCompose`/`Fin.Tuple.Lemmas`/`Security.Implications` (sorry-reconciled, keeping p2
additions), `SumcheckDomain.init`/`sum_cube_snoc` snoc-duals (restored to `Domain.lean`
from `c42ccb2e7`), the fix-last `fixFirstVariablesOfMQP` cluster (from `89827e469`).

## What is RED — the two structural blockers (maintainer-grade, thrice-confirmed)

Three independent deep passes + the triple-witnessed
`BinaryBasefold/docs/reversal-cluster-diagnosis-2026-06-24.md` (which says "DO NOT grind
this solo") converge on the same residual.

### Blocker A — `QueryPhase.lean`
- The ill-typed `iteratedQuotientMap_eq_qMap_total_fiber_extractMiddleFinMask` (whnf
  heartbeat timeout on `0 + destIdx.val` vs `i.val + steps`) is **resolved**: deleted and
  rewired to the correctly-typed `previousSuffix_eq_getFiberPoint_extractMiddleFinMask`
  (`Soundness/QueryPhaseSuffix.lean`).
- **Remaining:** `query_phase_step_preserves_fold` references **4 genuinely-undefined
  dependent-transport lemmas** — `qMap_total_fiber_congr_source_apply`,
  `qMap_total_fiber_congr_dest`, `qMap_total_fiber_congr_steps`,
  `single_point_localized_fold_matrix_form_congr_steps_index` — which must be
  reconstructed matching `qMap_total_fiber`'s dependent typing (`steps` controls both the
  `Fin (2^steps)` codomain and `y : sDomain ⟨i+steps⟩`). Plus ~15 v4.30 tactic-drift
  errors + an undefined `k_succ_mul_ϑ_le_ℓ` (~line 601). Needs live goal-state iteration.

### Blocker B — `Steps/Fold.lean`
- **Verified fix path** (not yet fully applied): the genuine verifier output
  `foldVerifierStmtOut` (Relations.lean ~212) uses `Fin.cons` (newest-first) challenge
  order, but `foldKStateProp`/`masterKStateProp` (Fold.lean ~487) wrongly use `Fin.snoc`.
  The fix is to flip ~20 statement-challenge-vector sites `Fin.snoc … r_i'` → `Fin.cons r_i' …`
  (making the completeness statement-equality `rfl` against the true verifier) and
  re-derive `incrementalBadEventExistsProp_fold_step_backward` +
  `foldStepFreshDoomPreservationEvent` in fold order (~350 lines of HEq/`Fin.rev` work),
  using the two bridge lemmas now landed in `Basic.lean`
  (`foldOrderChallenges_cons_of_lt`, `foldOrderChallenges_cons_last`).
- **Landed & green:** `badSumcheckEventProp` retyped from function-level (`L → L`) to
  polynomial-level (`↥L⦃≤2⦄[X]` with `eval` equality) in `Relations.lean` + consumer
  `probability_bound_badSumcheckEventProp` in `Soundness.lean` — a genuine security-content
  fix (over `CharP L 2`, distinct degree-≤2 polys share an eval function, so the
  function-level event was unsound).

## Recommendation

- Closing the two leaves is well-scoped but genuinely multi-session maintainer-grade
  (dependent-transport lemma reconstruction + the ~350-line reversal re-derivation).
  Per #313's own closeout criteria (mark intentionally-external assumptions
  grant-out-of-scope), this is the honest documented frontier.
- **Do the remaining A/B work in a dedicated git worktree**, NOT the shared checkout —
  the #466 ProximityGap swarm is concurrently building/staging here and will clobber edits.
- Recovery is preserved as a patch (`313-full-progress` / `CORRECTED-hasEval`) in the
  working session; canonical VCVio must be checked out (`lake update VCVio` / manifest `576766a`).
