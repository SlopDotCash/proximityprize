/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Security.SumcheckRejectionCore
import ArkLib.ProofSystem.Sumcheck.Spec.SingleRoundCohWired
import ArkLib.ProofSystem.Sumcheck.Spec.SeqComposeRbrSoundness

/-!
# Pointwise rejection of the composed sum-check verifier (issue #13, pieces C+D)

* `liftedRound_run_failure` (C): the **lifted** round-`i` sum-check oracle verifier
  (`SingleRound.oracleVerifier i = Simple.oracleVerifier.liftContext (sumcheckOracleLens i)`)
  rejects outright (`run = failure`) on any statement outside `relationRound i.castSucc`.
  Chain: the proven coherence commute (`liftContext_toVerifier_comm` with `coh_proven_inst`)
  exposes the lifted run as Simple's run on the lens projection; the projection is Simple-bad by
  `simpleProj_mem_iff` (right-to-left); Simple rejects by `verifier_run_failure_of_badSum`; and
  the `OptionT` bind short-circuits the failure.

* `composedSumcheck_run_failure` (D): the **composed** sum-check oracle verifier
  (`seqCompose` of the lifted rounds) rejects outright on any statement outside
  `relationRound 0`. Chain: the proven binary verifier fusion collapses `toVerifier` of the
  oracle-level `seqCompose` to `Verifier.seqCompose` of the per-round `toVerifier`s; the head
  unfolds to `append (V 0) rest`, whose `verify` runs round `0` first; round `0` fails by (C),
  and the `OptionT` bind short-circuits.

No `sorry`; axiom audit at the bottom.
-/

open Polynomial MvPolynomial OracleComp OracleSpec ProtocolSpec Finset
open scoped NNReal ENNReal

namespace Sumcheck.Spec

variable {ι : Type} (oSpec : OracleSpec ι)
variable (R : Type) [CommSemiring R] (deg : ℕ) {m : ℕ} (D : Fin m ↪ R)
  [DecidableEq R] [SampleableType R]

/-- `OptionT` over `OracleComp` short-circuits `failure` through `bind`. -/
private theorem optionT_failure_bind {α β : Type}
    (f : α → OptionT (OracleComp oSpec) β) :
    (failure : OptionT (OracleComp oSpec) α) >>= f = failure := by
  apply OptionT.ext
  simp [OptionT.run_bind]

/-- **(C) The lifted round-`i` sum-check verifier rejects bad round claims outright.** -/
theorem liftedRound_run_failure {n : ℕ} (i : Fin n)
    (stmt : StatementRound R n i.castSucc) (oStmt : ∀ j, OracleStatement R n deg j)
    (hBad : ((stmt, oStmt), ()) ∉ relationRound R n deg D i.castSucc)
    (tr : (SingleRound.pSpec R deg).FullTranscript) :
    ((SingleRound.oracleVerifier R n deg D oSpec i).toVerifier).run (stmt, oStmt) tr =
      (failure : OptionT (OracleComp oSpec) _) := by
  -- The projected Simple statement is bad (right-to-left transport of the relation iff).
  have hProjBad : ¬ (((SingleRound.oStmtLens R n deg D i).proj (stmt, oStmt)), ())
      ∈ SingleRound.Simple.inputRelation R deg D := fun hMem =>
    hBad ((SingleRound.simpleProj_mem_iff R deg D n i stmt oStmt).mp hMem)
  -- Unfold the bad membership into the sum hypothesis of the rejection core.
  have hSumBad : ¬ ((∑ x ∈ (univ.map D),
      (((((SingleRound.oStmtLens R n deg D i).proj (stmt, oStmt)).2) ()).1.eval x))
        = ((SingleRound.oStmtLens R n deg D i).proj (stmt, oStmt)).1) := fun hsum =>
    hProjBad (by
      simp only [SingleRound.Simple.inputRelation, Set.mem_setOf_eq]
      exact hsum)
  -- Simple rejects the projected statement.
  have hSimpleFail := SingleRound.Simple.verifier_run_failure_of_badSum oSpec R deg D
    ((SingleRound.oStmtLens R n deg D i).proj (stmt, oStmt)).1
    ((SingleRound.oStmtLens R n deg D i).proj (stmt, oStmt)).2
    hSumBad tr
  -- Commute `toVerifier` through the lift (proven coherence), expose the projected Simple run.
  have hcomm := OracleVerifier.liftContext_toVerifier_comm
    (stmtLens := SingleRound.sumcheckOracleLens R n deg D oSpec i)
    (V := (SingleRound.Simple.oracleReduction R deg D oSpec).verifier)
    (coh := SingleRound.coh_proven_inst i)
  show (((SingleRound.Simple.oracleReduction R deg D oSpec).verifier.liftContext
      (SingleRound.sumcheckOracleLens R n deg D oSpec i)).toVerifier).run (stmt, oStmt) tr = _
  rw [hcomm]
  -- Unfold the lifted run: Simple's run on the projection, post-composed with the lift.
  -- (`sumcheckOracleLens.toLens = oStmtLens` and `run = verify` definitionally; structure eta
  -- identifies the projected pair with its component re-pairing.)
  show (((SingleRound.Simple.oracleReduction R deg D oSpec).verifier.toVerifier).run
      ((SingleRound.oStmtLens R n deg D i).proj (stmt, oStmt)) tr) >>= _ = _
  have hSimpleFail' : (((SingleRound.Simple.oracleReduction R deg D oSpec).verifier.toVerifier).run
      ((SingleRound.oStmtLens R n deg D i).proj (stmt, oStmt)) tr)
      = (failure : OptionT (OracleComp oSpec) _) := hSimpleFail
  rw [hSimpleFail']
  exact optionT_failure_bind oSpec _

/-- **(D) The composed sum-check verifier rejects bad round-`0` claims outright.** -/
theorem composedSumcheck_run_failure {n' : ℕ}
    (stmt : StatementRound R (n' + 1) 0) (oStmt : ∀ j, OracleStatement R (n' + 1) deg j)
    (hBad : ((stmt, oStmt), ()) ∉ relationRound R (n' + 1) deg D (0 : Fin (n' + 2)))
    (tr : (pSpec R deg (n' + 1)).FullTranscript) :
    ((oracleVerifier R deg D (n' + 1) oSpec).toVerifier).run (stmt, oStmt) tr =
      (failure : OptionT (OracleComp oSpec) _) := by
  -- Fuse `toVerifier` through the oracle-level `seqCompose` (proven binary fusion).
  rw [show (oracleVerifier R deg D (n' + 1) oSpec).toVerifier
      = Verifier.seqCompose
          (fun j => StatementRound R (n' + 1) j × (∀ k, OracleStatement R (n' + 1) deg k))
          (fun j => (SingleRound.oracleVerifier R (n' + 1) deg D oSpec j).toVerifier) from
    OracleVerifier.seqCompose_toVerifier_of_binary_for_rbr
      (OracleVerifier.binaryVerifierFusionForRbr_holds oSpec) _ _ _ _ _ _]
  -- Head unfold: the composed verify runs round `0` first; it fails; the bind short-circuits.
  show ((SingleRound.oracleVerifier R (n' + 1) deg D oSpec 0).toVerifier.verify
      (stmt, oStmt) _) >>= _ = _
  have h0 : ((SingleRound.oracleVerifier R (n' + 1) deg D oSpec 0).toVerifier).run
      (stmt, oStmt) (ProtocolSpec.FullTranscript.fst (show ((SingleRound.pSpec R deg) ++ₚ (ProtocolSpec.seqCompose (fun _ : Fin n' => SingleRound.pSpec R deg))).FullTranscript from tr)) = failure := by
    exact liftedRound_run_failure oSpec R deg D 0 stmt oStmt hBad _
  rw [show (SingleRound.oracleVerifier R (n' + 1) deg D oSpec 0).toVerifier.verify
      (stmt, oStmt) (ProtocolSpec.FullTranscript.fst (show ((SingleRound.pSpec R deg) ++ₚ (ProtocolSpec.seqCompose (fun _ : Fin n' => SingleRound.pSpec R deg))).FullTranscript from tr))
      = ((SingleRound.oracleVerifier R (n' + 1) deg D oSpec 0).toVerifier).run
        (stmt, oStmt) (ProtocolSpec.FullTranscript.fst (show ((SingleRound.pSpec R deg) ++ₚ (ProtocolSpec.seqCompose (fun _ : Fin n' => SingleRound.pSpec R deg))).FullTranscript from tr)) from rfl]
  rw [h0]
  exact optionT_failure_bind oSpec _

end Sumcheck.Spec

/- Axiom audit. -/
#print axioms Sumcheck.Spec.liftedRound_run_failure
#print axioms Sumcheck.Spec.composedSumcheck_run_failure
