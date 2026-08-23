/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Spartan.SecondSumcheckWithTarget
import ArkLib.ProofSystem.Spartan.SumcheckDeterminismWitnesses

/-!
# Failing-determinism witnesses for the carried sum-check phases (issue #329, X-lane)

The `hV` witnesses the tight composed rbr-KS fold consumes at the two carried sum-check seams,
mirroring `SumcheckDeterminismWitnesses` at the target-preserving lenses: the compiled carried
sum-check verifiers are failing-deterministic, via the coherence comm
(`LiftContextCoherent.toVerifier_comm`) and `Verifier.liftContext_failingDet` on the proven
full-sum-check failing-determinism.

(The carried *short*-round witnesses are the compiled closed forms already landed:
`sendEvalClaimWithTarget_toVerifier_closed`, `linearCombinationWithTarget_toVerifier_closed`
in `MidChainWithTarget.lean`, and `prependRLCTargetWithTarget_toVerifier_pure` in
`TightMidLeaves.lean`.)
-/

open OracleComp OracleSpec ProtocolSpec

namespace Spartan.Spec

variable {R : Type 0} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [Inhabited R]
  [SampleableType R] (pp : PublicParams)
variable {ι : Type} (oSpec : OracleSpec ι)

/-- **`hV₃` witness (tight chain): the carried first sum-check verifier is
failing-deterministic.** -/
theorem firstSumcheckWithTarget_toVerifier_isFailingDet :
    (firstSumcheckReductionWithTarget (R := R) pp oSpec).verifier.toVerifier.IsFailingDet := by
  letI coh : OracleVerifier.LiftContextCoherent (firstSumcheckOracleLensWithTarget pp oSpec)
      (Sumcheck.Spec.oracleVerifier R 3 (boolEmbedding R) pp.ℓ_m oSpec) := by
    change OracleVerifier.LiftContextCoherent (firstSumcheckOracleLensWithTarget pp oSpec)
      (Sumcheck.Spec.oracleReduction R 3 (boolEmbedding R) pp.ℓ_m oSpec).verifier
    exact firstSumcheckCoherentWithTarget (R := R) pp oSpec
  show ((Sumcheck.Spec.oracleVerifier R 3 (boolEmbedding R) pp.ℓ_m oSpec).liftContext
    (firstSumcheckOracleLensWithTarget pp oSpec)).toVerifier.IsFailingDet
  rw [OracleVerifier.liftContext_toVerifier_comm]
  obtain ⟨v?, hv⟩ := sumcheckFull_toVerifier_isFailingDet oSpec 3 (boolEmbedding R) pp.ℓ_m
  exact ⟨_, Verifier.liftContext_failingDet _ _ v? hv⟩

/-- **`hV₇` witness (tight chain): the carried second sum-check verifier is
failing-deterministic.** -/
theorem secondSumcheckWithTarget_toVerifier_isFailingDet :
    (secondSumcheckReductionWithTarget (R := R) pp oSpec).verifier.toVerifier.IsFailingDet := by
  letI coh : OracleVerifier.LiftContextCoherent (secondSumcheckOracleLensWithTarget pp oSpec)
      (Sumcheck.Spec.oracleVerifier R 2 (boolEmbedding R) pp.ℓ_n oSpec) := by
    change OracleVerifier.LiftContextCoherent (secondSumcheckOracleLensWithTarget pp oSpec)
      (Sumcheck.Spec.oracleReduction R 2 (boolEmbedding R) pp.ℓ_n oSpec).verifier
    exact secondSumcheckCoherentWithTarget (R := R) pp oSpec
  show ((Sumcheck.Spec.oracleVerifier R 2 (boolEmbedding R) pp.ℓ_n oSpec).liftContext
    (secondSumcheckOracleLensWithTarget pp oSpec)).toVerifier.IsFailingDet
  rw [OracleVerifier.liftContext_toVerifier_comm]
  obtain ⟨v?, hv⟩ := sumcheckFull_toVerifier_isFailingDet oSpec 2 (boolEmbedding R) pp.ℓ_n
  exact ⟨_, Verifier.liftContext_failingDet _ _ v? hv⟩

end Spartan.Spec

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms Spartan.Spec.firstSumcheckWithTarget_toVerifier_isFailingDet
#print axioms Spartan.Spec.secondSumcheckWithTarget_toVerifier_isFailingDet
