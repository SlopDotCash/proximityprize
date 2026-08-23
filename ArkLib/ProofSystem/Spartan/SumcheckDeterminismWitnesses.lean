/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Spartan.FirstSumcheckReduction
import ArkLib.ProofSystem.Spartan.FirstSumcheckFaithful
import ArkLib.ProofSystem.Spartan.SecondSumcheckReduction
import ArkLib.ProofSystem.Spartan.SecondSumcheckFaithful
import ArkLib.ProofSystem.Sumcheck.Spec.RbrKnowledgeSoundnessOracle
import ArkLib.OracleReduction.Composition.Sequential.SeqComposeFailingDet

/-!
# Spartan sum-check determinism witnesses (`hV₃`/`hV₇` of the rbr fold, issue #114)

The two failing-determinism witnesses consumed by the composed rbr-KS fold
(`ComposedRbrKnowledgeSoundness.lean`): the Spartan first/second sum-check verifiers — the
`liftContext` lifts of the full multi-round sum-check oracle verifier — compile to
failing-deterministic `toVerifier`s.

Chain: per-round `oracleVerifier_toVerifier_failingDet` → the n-ary
`seqCompose_toVerifier_isFailingDet` → `liftContext_toVerifier_comm` (via the proven
`first/secondSumcheckCoherent` instances) → `Verifier.liftContext_failingDet`.
-/

open OracleComp OracleSpec ProtocolSpec

namespace Spartan.Spec

variable {R : Type 0} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [Inhabited R]
  [SampleableType R] (pp : PublicParams)
variable {ι : Type} (oSpec : OracleSpec ι)

/-- **The full multi-round sum-check oracle verifier compiles failing-deterministically**
(any degree, any round count): n-ary composition of the per-round failing-det collapses. -/
theorem sumcheckFull_toVerifier_isFailingDet (deg : ℕ) {m : ℕ} (D : Fin m ↪ R) (n : ℕ) :
    (Sumcheck.Spec.oracleVerifier R deg D n oSpec).toVerifier.IsFailingDet :=
  OracleVerifier.seqCompose_toVerifier_isFailingDet
    (Stmt := Sumcheck.Spec.StatementRound R n)
    (OStmt := fun _ => Sumcheck.Spec.OracleStatement R n deg)
    (Sumcheck.Spec.SingleRound.oracleVerifier R n deg D oSpec)
    (fun i => ⟨_, Sumcheck.Spec.SingleRound.oracleVerifier_toVerifier_failingDet
      (R := R) (n := n) (deg := deg) (D := D) (oSpec := oSpec) i⟩)

/-- **`hV₃` witness: the Spartan first sum-check verifier is failing-deterministic.** -/
theorem firstSumcheck_toVerifier_isFailingDet :
    (firstSumcheckReduction (R := R) pp oSpec).verifier.toVerifier.IsFailingDet := by
  letI coh : OracleVerifier.LiftContextCoherent (firstSumcheckOracleLens pp oSpec)
      (Sumcheck.Spec.oracleVerifier R 3 (boolEmbedding R) pp.ℓ_m oSpec) := by
    change OracleVerifier.LiftContextCoherent (firstSumcheckOracleLens pp oSpec)
      (Sumcheck.Spec.oracleReduction R 3 (boolEmbedding R) pp.ℓ_m oSpec).verifier
    exact firstSumcheckCoherent (R := R) pp oSpec
  show ((Sumcheck.Spec.oracleVerifier R 3 (boolEmbedding R) pp.ℓ_m oSpec).liftContext
    (firstSumcheckOracleLens pp oSpec)).toVerifier.IsFailingDet
  rw [OracleVerifier.liftContext_toVerifier_comm]
  obtain ⟨v?, hv⟩ := sumcheckFull_toVerifier_isFailingDet oSpec 3 (boolEmbedding R) pp.ℓ_m
  exact ⟨_, Verifier.liftContext_failingDet _ _ v? hv⟩

/-- **`hV₇` witness: the Spartan second sum-check verifier is failing-deterministic.** -/
theorem secondSumcheck_toVerifier_isFailingDet :
    (secondSumcheckReduction (R := R) pp oSpec).verifier.toVerifier.IsFailingDet := by
  letI coh : OracleVerifier.LiftContextCoherent (secondSumcheckOracleLens pp oSpec)
      (Sumcheck.Spec.oracleVerifier R 2 (boolEmbedding R) pp.ℓ_n oSpec) := by
    change OracleVerifier.LiftContextCoherent (secondSumcheckOracleLens pp oSpec)
      (Sumcheck.Spec.oracleReduction R 2 (boolEmbedding R) pp.ℓ_n oSpec).verifier
    exact secondSumcheckCoherent (R := R) pp oSpec
  show ((Sumcheck.Spec.oracleVerifier R 2 (boolEmbedding R) pp.ℓ_n oSpec).liftContext
    (secondSumcheckOracleLens pp oSpec)).toVerifier.IsFailingDet
  rw [OracleVerifier.liftContext_toVerifier_comm]
  obtain ⟨v?, hv⟩ := sumcheckFull_toVerifier_isFailingDet oSpec 2 (boolEmbedding R) pp.ℓ_n
  exact ⟨_, Verifier.liftContext_failingDet _ _ v? hv⟩

end Spartan.Spec

#print axioms Spartan.Spec.sumcheckFull_toVerifier_isFailingDet
#print axioms Spartan.Spec.firstSumcheck_toVerifier_isFailingDet
#print axioms Spartan.Spec.secondSumcheck_toVerifier_isFailingDet
