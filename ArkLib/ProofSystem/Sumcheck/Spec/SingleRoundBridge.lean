/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Sumcheck.Spec.SingleRound
import ArkLib.OracleReduction.LiftContext.OracleReduction

/-!
# The single-round sum-check `toReduction = reduction` bridge (`hPerRound`, issue #13)

`Sumcheck.Spec.oracleReductionToReduction_of_perRound`
(`OracleCompletenessUncond.lean`) reduces the whole multi-round sum-check
`oracleReduction.toReduction = reduction` bridge to the single, *orthogonal* per-round fact

  `hPerRound : ∀ i, (SingleRound.oracleReduction R n deg D oSpec i).toReduction =
                    SingleRound.reduction R n deg D oSpec i`.                              (★)

This file isolates exactly what is needed to discharge `(★)` per round and shows that **all the
structural `liftContext`-commutation plumbing is already provable**, leaving precisely **one** named,
genuinely-deep residual.

## What is structural (proven here, unconditionally)

Each side of `(★)` is a *lifted* object built by `OracleReduction.liftContext`:

* `SingleRound.oracleReduction i =
    (Simple.oracleReduction).liftContext (oCtxLens i) (sumcheckOracleLens i)`;
* `SingleRound.reduction i = (Simple.reduction).liftContext (oCtxLens i).toContext`.

The framework lemma `OracleReduction.liftContext_toReduction_comm` rewrites the LHS of `(★)` to
`(Simple.oracleReduction).toReduction.liftContext (oCtxLens i).toContext` **given** two side
conditions:

1. `hStmt : (sumcheckOracleLens i).toLens = (oCtxLens i).stmt` — discharged here by `rfl`
   (`sumcheckOracleLens.toLens` and `oCtxLens.stmt` are *both definitionally* `oStmtLens i`); and
2. `[coh : OracleVerifier.LiftContextCoherent (sumcheckOracleLens i) (Simple.oracleReduction).verifier]`
   — the per-round oracle-routing coherence (design note #433).

Modulo those, `(★)` becomes the *lifted* image of the **simple-level base bridge**
`(Simple.oracleReduction).toReduction = Simple.reduction`, i.e.
`(Simple.oracleVerifier).toVerifier = Simple.verifier`.

## The one genuinely-deep residual (named hypotheses)

The simple-level base bridge is *not* an identity: `Simple.verifier` checks the `D`-sum of the
**prover-message** round polynomial (`transcript 0`), while `(Simple.oracleVerifier).toVerifier`
checks the `D`-sum of the **oracle-statement** polynomial (`oStmt ()`); these are different objects
(this is the "false `oracleReduction_eq_reduction`" repeatedly flagged in `SingleRound.lean`). It —
together with the per-round routing coherence — is therefore carried as the explicit named
hypotheses

* `coh i` — `OracleVerifier.LiftContextCoherent (sumcheckOracleLens i) (Simple.oracleVerifier)`;
* `hSimpleBridge` — `(Simple.oracleReduction).toReduction = Simple.reduction`.

No `sorry`/`admit`. The main theorem `singleRound_toReduction_eq_reduction_of` is the per-round
bridge **conditional on exactly those two named residuals**, and `perRound_of` packages the
`∀ i`-form consumed by `oracleReductionToReduction_of_perRound`.
-/

open ProtocolSpec OracleComp OracleSpec

set_option linter.unusedSectionVars false

namespace Sumcheck.Spec.SingleRound

noncomputable section

variable {R : Type} [CommSemiring R] {n : ℕ} {deg : ℕ} {m : ℕ} {D : Fin m ↪ R}
  {ι : Type} {oSpec : OracleSpec ι} [DecidableEq R] [SampleableType R]

/-- **Lens-coherence side condition `hStmt` is definitional.** The oracle-routing lens'
underlying value lens `(sumcheckOracleLens i).toLens` and the context lens' statement component
`(oCtxLens i).stmt` are *both* the single value-level statement lens `oStmtLens i`, so they agree by
`rfl`. This discharges the `hStmt` premise of `liftContext_toReduction_comm` for every round. -/
theorem sumcheckOracleLens_toLens_eq_oCtxLens_stmt (i : Fin n) :
    (sumcheckOracleLens R n deg D oSpec i).toLens = (oCtxLens R n deg D i).stmt :=
  rfl

/-- **The per-round `toReduction = reduction` bridge — modulo its two named residuals.**

The structural `liftContext`-commutation is discharged in full (the `hStmt` side condition is `rfl`
and the framework lemma `OracleReduction.liftContext_toReduction_comm` does the rest given the
routing coherence `coh`). What remains is exactly the *lifted image* of the simple-level base bridge
`(Simple.oracleReduction).toReduction = Simple.reduction` (`hSimpleBridge`), which is genuinely deep
(the simple oracle verifier reads the oracle statement, the plain verifier reads the prover message).

* `coh` — the per-round oracle-routing coherence `LiftContextCoherent` for this round's lens applied
  to the simple oracle verifier;
* `hSimpleBridge` — the simple-level base bridge.

Both are carried as explicit named hypotheses (no `sorry`). -/
theorem singleRound_toReduction_eq_reduction_of (i : Fin n)
    (coh : OracleVerifier.LiftContextCoherent (sumcheckOracleLens R n deg D oSpec i)
      (Simple.oracleReduction R deg D oSpec).verifier)
    (hSimpleBridge :
      (Simple.oracleReduction R deg D oSpec).toReduction = Simple.reduction R deg D oSpec) :
    (oracleReduction R n deg D oSpec i).toReduction = reduction R n deg D oSpec i := by
  haveI : OracleVerifier.LiftContextCoherent (sumcheckOracleLens R n deg D oSpec i)
      (Simple.oracleReduction R deg D oSpec).verifier := coh
  -- `oracleReduction i` / `reduction i` are the lifted `Simple.oracleReduction` / `Simple.reduction`.
  show ((Simple.oracleReduction R deg D oSpec).liftContext (oCtxLens R n deg D i)
        (sumcheckOracleLens R n deg D oSpec i)).toReduction
      = (Simple.reduction R deg D oSpec).liftContext (oCtxLens R n deg D i).toContext
  -- (1) Structural step: commute `toReduction` past the lift via the framework lemma
  --     (`hStmt` is `rfl`; `coh` supplies the routing coherence).
  rw [OracleReduction.liftContext_toReduction_comm
        (lens := oCtxLens R n deg D i) (stmtLens := sumcheckOracleLens R n deg D oSpec i)
        (R := Simple.oracleReduction R deg D oSpec)
        (sumcheckOracleLens_toLens_eq_oCtxLens_stmt i)]
  -- (2) Both sides are now `(·).liftContext (oCtxLens i).toContext`; rewrite the inner reduction via
  --     the named simple-level base bridge.
  rw [hSimpleBridge]

/-- **The `∀ i`-form `hPerRound`, modulo the two named residuals.**

This is the shape consumed by `Sumcheck.Spec.oracleReductionToReduction_of_perRound`
(`OracleCompletenessUncond.lean`). The structural plumbing is fully discharged; the inputs are
exactly the per-round routing coherence instances `coh` and the simple-level base bridge
`hSimpleBridge`. -/
theorem perRound_of
    (coh : ∀ i, OracleVerifier.LiftContextCoherent (sumcheckOracleLens R n deg D oSpec i)
      (Simple.oracleReduction R deg D oSpec).verifier)
    (hSimpleBridge :
      (Simple.oracleReduction R deg D oSpec).toReduction = Simple.reduction R deg D oSpec) :
    ∀ i, (oracleReduction R n deg D oSpec i).toReduction = reduction R n deg D oSpec i :=
  fun i => singleRound_toReduction_eq_reduction_of i (coh i) hSimpleBridge

end

end Sumcheck.Spec.SingleRound

#print axioms Sumcheck.Spec.SingleRound.sumcheckOracleLens_toLens_eq_oCtxLens_stmt
#print axioms Sumcheck.Spec.SingleRound.singleRound_toReduction_eq_reduction_of
#print axioms Sumcheck.Spec.SingleRound.perRound_of
