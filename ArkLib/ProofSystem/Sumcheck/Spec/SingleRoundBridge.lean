/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ProximityPrize.Extensions.ProofSystem.Sumcheck.Spec.SingleRound
import ProximityPrize.Extensions.OracleReduction.LiftContext.OracleReduction

/-!
# The single-round sum-check `toReduction = reduction` bridge (`hPerRound`, issue #13)

`Sumcheck.Spec.oracleReductionToReduction_of_perRound`
(`OracleCompletenessUncond.lean`) reduces the whole multi-round sum-check
`oracleReduction.toReduction = reduction` bridge to the single, *orthogonal* per-round fact

  `hPerRound : ∀ i, (SingleRound.oracleReduction R n deg D oSpec i).toReduction =
                    SingleRound.reduction R n deg D oSpec i`.                              (★)

## Current status: `(★)` holds

Canonical ArkLib (`Sumcheck/Spec/SingleRound.lean`) defines both round verifiers to read the prover
message: `Simple.oracleVerifier` queries the message oracle at every point of `D` and at the
challenge, and `Simple.verifier` guards the message's `D`-sum and takes the new target from the
message. Canonical ArkLib proves the simple bridge `Simple.oracleReduction_eq_reduction` and the
lifted verifier bridge `oracleVerifier_eq_verifier i`; the lifted `SingleRound.oracleReduction i`
is built with the executable lens `oCtxExecutableLens i`. So `(★)` holds for every round:
`SingleRound.oracleReduction_toReduction_eq_reduction`
(`Logup/Security/BridgeAndAppendResiduals.lean`).

The theorems `singleRound_toReduction_eq_reduction_of` and `perRound_of` keep their historical
signatures with two hypotheses, `coh` (routing coherence for the downstream lens
`sumcheckOracleLens i`) and `hSimpleBridge` (`(Simple.oracleReduction).toReduction =
Simple.reduction`). Both hypotheses are now unused by the proofs: the conclusion comes directly
from `oracleVerifier_eq_verifier`. `hSimpleBridge` is canonical ArkLib's
`Simple.oracleReduction_eq_reduction`, and `coh` is `SingleRoundCohWired.coh_proven_inst`.

## History

An earlier downstream version lifted the simple reduction through `sumcheckOracleLens` with
`OracleReduction.liftContextLegacy`, and its `Simple.oracleVerifier` ignored the prover message,
checking the `D`-sum of the input oracle directly. For that verifier `hSimpleBridge` was false
whenever `(m : R) ≠ 0`, and so was `(★)`. Canonical ArkLib replaced that verifier with the
message-reading one above, which retired the counterexample.

No `sorry`/`admit`.
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

/-- **The per-round `toReduction = reduction` bridge, with two historical hypotheses.**

The hypotheses are unused: the prover sides agree definitionally and the verifier half is canonical
ArkLib's `oracleVerifier_eq_verifier`. They are kept so existing callers still elaborate.

* `coh` — the routing coherence for the downstream lens `sumcheckOracleLens i`, proved as
  `SingleRoundCohWired.coh_proven_inst`;
* `hSimpleBridge` — the simple-level bridge, proved canonically as
  `Simple.oracleReduction_eq_reduction`.

The unconditional statement is `SingleRound.oracleReduction_toReduction_eq_reduction`
(`Logup/Security/BridgeAndAppendResiduals.lean`). -/
theorem singleRound_toReduction_eq_reduction_of (i : Fin n)
    (coh : OracleVerifier.LiftContextCoherent (sumcheckOracleLens R n deg D oSpec i)
      (Simple.oracleReduction R deg D oSpec).verifier)
    (hSimpleBridge :
      (Simple.oracleReduction R deg D oSpec).toReduction = Simple.reduction R deg D oSpec) :
    (oracleReduction R n deg D oSpec i).toReduction = reduction R n deg D oSpec i := by
  apply Reduction.ext
  · rfl
  · exact oracleVerifier_eq_verifier (R := R) (n := n) (deg := deg)
      (D := D) (oSpec := oSpec) i

/-- **The `∀ i`-form `hPerRound`, with two historical hypotheses.**

This is the shape consumed by `Sumcheck.Spec.oracleReductionToReduction_of_perRound`
(`OracleCompletenessUncond.lean`). Both hypotheses are unused; the unconditional form is
`SingleRound.oracleReduction_toReduction_eq_reduction`
(`Logup/Security/BridgeAndAppendResiduals.lean`). -/
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
