/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.RingSwitching.BatchingPhase
import ArkLib.OracleReduction.Composition.Sequential.AppendRbrKnowledgeOracleLift

/-!
# Determinism witness for the RingSwitching batching verifier (issue #29)

The rbr (knowledge) soundness append keystones consume a determinism witness
`hVerify : V₁.toVerifier = ⟨fun stmt tr => pure (verify stmt tr)⟩` for the left verifier of each
seam. This file supplies it for the batching phase: the batching oracle verifier is
deterministic-total (its single oracle query is answered from the transcript, and the `unless`
check returns the designated `failureState` *statement*, not an `OptionT` failure), so its
compiled `toVerifier` is literally pure.

Built by feeding the proven `simulateQ` collapse `oracleVerifier_verify_collapse`
(`BatchingPhase.lean`) through the generic bridge `OracleVerifier.toVerifier_eq_pure_of_collapse`
(`AppendRbrKnowledgeOracleLift.lean`).
-/

open OracleSpec OracleComp ProtocolSpec
open Sumcheck.Structured
open scoped NNReal

noncomputable section
namespace RingSwitching.BatchingPhase

variable (κ : ℕ) [NeZero κ]
variable (L : Type) [CommRing L] [Nontrivial L] [Fintype L] [DecidableEq L]
  [SampleableType L]
variable (K : Type) [CommRing K] [Fintype K] [DecidableEq K]
variable [Algebra K L]
variable (P : RingSwitchingProfile K L κ)
variable (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']
variable (h_l : ℓ = ℓ' + κ)
variable (aOStmtIn : AbstractOStmtIn L ℓ')

/-- The batching verifier's deterministic statement-level verdict: accept (with the batched
sumcheck-target statement) if Check 1 passes, else the designated `failureState`. This is exactly
the value computed by `oracleVerifier_verify_collapse`. -/
def batchingVerifyFn
    (p : BatchingStmtIn L ℓ × ∀ j, aOStmtIn.OStmtIn j)
    (tr : FullTranscript (pSpecBatching (κ := κ) (L := L) (K := K) (P := P))) :
    Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) 0 :=
  if performCheckOriginalEvaluation κ L K P ℓ ℓ' h_l p.1.original_claim p.1.t_eval_point
      (FullTranscript.messages tr ⟨0, by rfl⟩) then
    { ctx := { t_eval_point := p.1.t_eval_point,
               original_claim := p.1.original_claim,
               s_hat := FullTranscript.messages tr ⟨0, by rfl⟩,
               r_batching := FullTranscript.challenges tr ⟨1, by rfl⟩ },
      sumcheck_target := compute_s0 κ L K P
        (FullTranscript.messages tr ⟨0, by rfl⟩)
        (FullTranscript.challenges tr ⟨1, by rfl⟩),
      challenges := Fin.elim0 }
  else failureState κ L K P ℓ ℓ' p.1 (FullTranscript.messages tr ⟨0, by rfl⟩)

/-- **Determinism witness for the batching verifier.** Its compiled `toVerifier` is literally the
pure verifier on `batchingVerifyFn` (paired with the deterministic `oStmtOut` routing) — the exact
`hVerify` input of the rbr (knowledge) soundness append keystones, for the seams whose left phase
is the batching protocol. -/
theorem batchingOracleVerifier_toVerifier_pure :
    (oracleVerifier κ L K P ℓ ℓ' h_l (aOStmtIn := aOStmtIn)).toVerifier
      = ⟨fun p tr => pure (batchingVerifyFn κ L K P ℓ ℓ' h_l aOStmtIn p tr,
          fun i => match h : (oracleVerifier κ L K P ℓ ℓ' h_l (aOStmtIn := aOStmtIn)).embed i with
            | Sum.inl j =>
                ((oracleVerifier κ L K P ℓ ℓ' h_l (aOStmtIn := aOStmtIn)).hEq i ▸ h ▸ p.2 j)
            | Sum.inr j =>
                ((oracleVerifier κ L K P ℓ ℓ' h_l (aOStmtIn := aOStmtIn)).hEq i ▸ h ▸
                  tr.messages j))⟩ :=
  OracleVerifier.toVerifier_eq_pure_of_collapse _ _ (fun stmt oStmt tr => by
    rw [oracleVerifier_verify_collapse]
    unfold batchingVerifyFn
    exact (apply_ite pure _ _ _).symm)

end RingSwitching.BatchingPhase
end

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms RingSwitching.BatchingPhase.batchingOracleVerifier_toVerifier_pure
