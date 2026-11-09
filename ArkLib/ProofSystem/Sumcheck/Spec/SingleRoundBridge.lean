/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Extensions.ProofSystem.Sumcheck.Spec.SingleRound
import ArkLib.Extensions.OracleReduction.LiftContext.OracleReduction

/-!
# The single-round sumcheck reduction bridge

Canonical `SingleRound.oracleReduction_toReduction` identifies the materialized oracle round
with its ordinary context-lifted reduction. The historical wrappers preserve their explicit
lens coherence and simple-round bridge arguments for downstream callers.

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

/-- The canonical per-round bridge in the historical context-lifting interface. -/
theorem singleRound_toReduction_eq_reduction_of (i : Fin n)
    (coh : OracleVerifier.LiftContextCoherent (sumcheckOracleLens R n deg D oSpec i)
      (Simple.oracleReduction R deg D oSpec).verifier)
    (hSimpleBridge :
      (Simple.oracleReduction R deg D oSpec).toReduction = Simple.reduction R deg D oSpec) :
    (oracleReduction R n deg D oSpec i).toReduction = reduction R n deg D oSpec i :=
  oracleReduction_toReduction R n deg D oSpec i

/-- The per-round bridge for all rounds, with the historical arguments. -/
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
