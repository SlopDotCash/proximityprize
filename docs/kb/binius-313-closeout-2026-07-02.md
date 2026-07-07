# Binius #313 closeout — build status + residual census (2026-07-02)

STATUS NOTE (not a certification). Lane B5. Successor to
`docs/wiki/Binius_Closeout_Audit.md` and
`docs/wiki/issue-317-binius-residuals.md` (scratchpad, 2026-06-10/11).

## TL;DR

- **The math residuals are done** (all four #313/#317/#327 named residuals are
  discharged or refuted-with-replacement, and the discharge modules are in-tree).
- **The cone does NOT build.** The Binius proof-system cone has been committed
  *build-failing* since 2026-06-14 (`06954f859` — "wip(#313): partial repair of
  Binius cone build blockers — QueryPhase + Steps/Fold (BUILD-FAILING)"). Under
  `lake env lean` against the current (coherent, up-to-date) substrate oleans:
  `QueryPhase.lean` = 10 errors, `Steps/Fold.lean` = 12 errors,
  `Steps/FinalSumcheck.lean` = did not finish in 400 s (warnings only in the
  compiled prefix). Every error is Mathlib/substrate **API drift** or
  **index-definition drift** — none is a `sorry`, an `admit`, a new math gap, or a
  weakened statement.
- **Honest recommendation: BLOCKED, not closeable-as-green today.** The
  named-residual convention presupposes a *compiling* cone whose only gaps are the
  named residuals. This cone does not compile at all, so the discharges cannot be
  re-certified axiom-clean in the current tree. Closeout requires first landing the
  substrate-API migration for QueryPhase + Fold + FinalSumcheck (a multi-file port,
  beyond a single-file iteration budget), *then* re-running the focused cone build.

## Build status (authoritative: direct `lake env lean`, current substrate)

No Binius `.olean` exists in `.lake` for QueryPhase / Fold / FinalSumcheck — the
cone has never successfully built in this checkout. Substrate oleans
(`ArkLib/OracleReduction/*`) are newer than their sources (coherent), so the
failures below are genuine, not stale-olean artifacts.

| File | Result | Error signature |
|---|---|---|
| `BinaryBasefold/QueryPhase.lean` | **10 errors** | `rewrite` pattern-not-found (296, 499); `isDefEq` heartbeat timeout (369); `omega could not prove the goal` ×5 + `unsolved goals` (574–580, downstream of the 499 rewrite failure); `dsimp made no progress` (993). |
| `BinaryBasefold/Steps/Fold.lean` | **12 errors** | `Application type mismatch: The argument` on the HEq/`incrementalFoldingBadEvent_eq_foldingBadEvent_of_k_eq_ϑ` / `fin_fun_heq_of_cast` lemmas (1115, 1341, 1345, 1363, 1530, 1557); `simp`/`dsimp made no progress` on the `simulateQ`/`support_*` simp-set (374, 590); `rewrite` pattern-not-found (667); `Type mismatch` (1187); anonymous-constructor type-undetermined on `query ⟨⟨1, …⟩, ()⟩` (1773). The `declaration uses sorry` warning at 1374 is a **cascade** from the errors (no literal `sorry` exists in the file). |
| `BinaryBasefold/Steps/FinalSumcheck.lean` | **inconclusive** (timeout >400 s) | Only `linter.unusedSimpArgs` warnings emitted in the compiled prefix (e.g. 173–174, duplicate `simulateQ_bind` in a `simp only`); no error reached before the timeout. Heavy file (`maxHeartbeats` bumped). Needs a longer dedicated compile to certify. |

Root cause is uniform: these three files were written against an older
`OracleReduction` `simulateQ` / `support` / `OracleQuery` API and an older set of
fold-index arithmetic definitions. The substrate moved (June commits through
`9526b121d`, 2026-06-14); the proofs' `erw`/`simp only`/`rw` chains and `omega`
index bounds no longer match. The upstream `rewrite`-not-found failures corrupt the
downstream goal state, which is why the QueryPhase 574–580 `omega`s fail
(symptom, not root).

**Focused cone build (`General` / `FRIBinius.General` / `BBFSmallFieldIOPCS`)
was deliberately NOT run.** It compiles the same failing source and would be red;
running it only takes the contended machine-wide build lock (serializing all
agents) for a guaranteed failure. The per-file `lake env lean` results above are
authoritative that the cone is red.

## Per-residual census (the four issue-named residuals)

All four named residuals are already handled in-tree; **none survives as a live
unproven `Prop`/`class`/`axiom`** (grep of the cone: the four identifiers appear
only in docstrings and discharge-module headers; there are zero `axiom`
declarations, zero `native_decide`, zero proof-position `sorry`/`admit` in the
cone). Caveat: the discharges below are **not re-verifiable in the current tree**
because their host files sit downstream of the build failure — the axiom-clean
certifications cited are from the 2026-06-10/11 scratchpad, now bit-rotted at the
API level (not the math level).

1. **`ExtractMLPCorrectnessResidual`** — classification **(refutation-with-replacement; a WIN)**.
   `ArkLib/ProofSystem/Binius/BinaryBasefold/ExtractMLPCorrectness.lean` proves the
   residual as stated is **false for `ℓ ≥ 2`** with a machine-checked countermodel:
   `extractMLPCorrectnessResidual_ell_eq_one` shows it forces `ℓ = 1`, and
   `revIndexMLP_eq_self_of_residual` isolates the little-endian
   (`Nat.binaryFinMapToNat`) vs bit-reversed (`statementOrderBitsOfIndex`)
   endianness mismatch. The checked replacement is the UDR-guarded two-sided
   `extractMLP_zero_eq_some_revIndexMLP_iff` (:655); the consequence downstream code
   actually consumes is the residual-free `firstOracleWitnessConsistencyProp_unique'`.
   Consumers (`Steps/Fold.lean`, `BBFSmallFieldIOPCS.lean`,
   `Steps/FinalSumcheck.lean`, `FRIBinius/CoreInteractionPhase.lean`) were migrated
   off the false `iff`. Genuine paper-antecedent correction to DP24 §4.

2. **`FoldPreservesBBFCodeMembershipResidual`** — classification **(discharged)**.
   Proved in `BinaryBasefold/Code.lean`: the binary quotient map is a nonzero scalar
   multiple of `X² − X`; any `deg < 2m` polynomial decomposes as
   `A(qᵢ(X)) + X·B(qᵢ(X))` with `deg A, deg B < m`; the one-step fold is computed on
   the two fiber preimages. No live residual class remains.

3. **`FoldMatrixDetNeZeroResidual`** — classification **(discharged)**.
   Proved via `BinaryBasefold/FoldDetSplit.lean` + `FoldDetDischarge.lean`
   (`detSplitFactor`: `det foldMatrixNat(n+1) = (x₁−x₀)^{2ⁿ}·det M₀·det M₁`, plus the
   `qMap_total_fiber_one_sub` fiber-separation brick and induction). Consumers call
   `foldMatrix_det_ne_zero` directly; no residual class remains.

4. **`FinalSumcheckStepLogicCompleteResidual`** — classification **(discharged)**.
   Now a direct proof `finalSumcheckStep_is_logic_complete` in
   `BinaryBasefold/ReductionLogic.lean:1719` (issue #327), discharging all four
   obligations: verifier check (`finalSumcheckStep_verifierCheck_passed`), relation
   out (`finalSumcheckStep_strictOracleFoldingConsistency_out` + the final-constant
   weld `getLastOracle_finalFold_eq_eval'`), and the two definitional output
   agreements. (The 2026-06-10 scratchpad marked this "still live"; that note is
   stale — it has since been discharged.)

### Role-named front-door assumptions (composition seam)

The cone-entry files (`FRIBinius/General.lean`, `BinaryBasefold/General.lean`,
`FRIBinius/CoreInteractionPhase.lean`, `BBFSmallFieldIOPCS.lean`) carry role-named
`append`/`seqCompose` completeness + rbr-knowledge-soundness hypotheses as explicit
`Prop` parameters (e.g. `BBFInnerRbrKnowledgeSoundness`,
`hCoreInteractionAppendRbrKnowledgeSoundness`, `hBatchingCoreAppendRbrKnowledgeSoundness`,
`hFullAppendRbrKnowledgeSoundness` in `BBFSmallFieldIOPCS.lean`). These are the
**modularity ("named residual") convention**, not incompleteness: each names an
`append_perfectCompleteness_total` / seq-compose transport that is intentionally
kept out-of-scope for the grant closeout (per `docs/wiki/Binius_Closeout_Audit.md`),
because discharging them needs live type-checking of `AppendCoherent` trait
resolution — which is exactly what the current build failure blocks.

## Honest recommendation

**Do NOT close #313 as green today.** The mathematical closeout is complete
(4/4 named residuals discharged/refuted; composition seam is the deliberate
modularity convention), but the cone is not certifiable because it does not build.

Blockers, in dependency order:

1. **Substrate-API migration of `QueryPhase.lean` (10) + `Steps/Fold.lean` (12).**
   Port the `simulateQ`/`support`/`OracleQuery` `erw`/`simp only` chains and the
   HEq fold-index lemma calls to the current `OracleReduction` API; re-derive the
   drifted `omega` index bounds. This is a multi-file port, not a single-file
   iteration — the errors interlock through shared simp-normal-form and index
   definitions. `origin/wip/313-finalsumcheck-reversal-fix` (the
   `foldOrderChallenges` reversal axis) may harvest for the FinalSumcheck/Fold
   reversal errors.
2. **Certify `FinalSumcheck.lean`** with a longer dedicated compile once (1) lands
   (only warnings seen so far, but it did not complete in 400 s).
3. **Re-run the focused cone build**
   `./scripts/lake-locked.sh build ArkLib.ProofSystem.Binius.BinaryBasefold.General ArkLib.ProofSystem.Binius.FRIBinius.General ArkLib.ProofSystem.Binius.BBFSmallFieldIOPCS`
   and axiom-audit the discharge modules (`Code.lean`, `FoldDetDischarge.lean`,
   `ReductionLogic.lean`, `ExtractMLPCorrectness.lean`) to re-confirm
   `[propext, Classical.choice, Quot.sound]`.

Only after (1)–(3) is the named-residual closeout convention actually satisfiable.
Until then #313 is **BLOCKED on the 2026-06-14 WIP build failure**, and the correct
public state is "math done, build red, closeout pending the substrate port."
