/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Sumcheck.Spec.SimpleRoundCoherent
import ArkLib.ProofSystem.Sumcheck.Spec.SingleRoundFaithful
import ArkLib.ProofSystem.Sumcheck.Spec.SingleRoundBridge

/-! # Wiring the proven `CubeFiber` into the per-round bridge (#13)

`coh_proven` (`SingleRoundFaithful`) is exactly the `hRoundFaithful` that
`SimpleRoundCoherent.coh_of` consumes — now a theorem, not a hypothesis. So the per-round
`LiftContextCoherent` (`coh`) is **unconditional**, and the per-round bridge
`(oracleReduction i).toReduction = reduction i` reduces from the two residuals `{coh, hSimpleBridge}`
down to the SINGLE Simple-level base bridge `hSimpleBridge`
(`Simple.oracleReduction.toReduction = Simple.reduction`, the single-round verifier-fusion). -/

open OracleComp OracleSpec ProtocolSpec
namespace Sumcheck.Spec.SingleRound
noncomputable section
variable {R : Type} [CommSemiring R] {n : ℕ} {deg : ℕ} {m : ℕ} {D : Fin m ↪ R}
  {ι : Type} {oSpec : OracleSpec ι} [DecidableEq R] [SampleableType R]

/-- The per-round `LiftContextCoherent`, UNCONDITIONALLY (fed the proven `coh_proven`). The `coh`
residual of `hPerRound` is hereby discharged. -/
@[reducible] def coh_proven_inst (i : Fin n) :
    OracleVerifier.LiftContextCoherent (sumcheckOracleLens R n deg D oSpec i)
      (Simple.oracleReduction R deg D oSpec).verifier :=
  simpleRound_liftContextCoherent i (coh_proven i)

/-- **The per-round bridge, reduced to ONLY `hSimpleBridge`.** With `coh` discharged via the proven
`CubeFiber`, `(oracleReduction i).toReduction = reduction i` follows from the single remaining
residual `hSimpleBridge` (the Simple-level single-round verifier-fusion). -/
theorem perRound_of_simpleBridge
    (hSimpleBridge : (Simple.oracleReduction R deg D oSpec).toReduction = Simple.reduction R deg D oSpec)
    (i : Fin n) :
    (oracleReduction R n deg D oSpec i).toReduction = reduction R n deg D oSpec i :=
  singleRound_toReduction_eq_reduction_of i (coh_proven_inst i) hSimpleBridge

end
end Sumcheck.Spec.SingleRound
