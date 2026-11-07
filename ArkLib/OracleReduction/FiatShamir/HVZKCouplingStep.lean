/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.HVZKCouplingFoundations
import ArkLib.ToMathlib.OracleCompEvalDistBindComm

/-!
# Per-round coupling step for the basic Fiat-Shamir HVZK coupling (#116)

This file proves the `succ`-step kernel of the `runToRoundFS` ↔ `runToRound` prover-run induction
underlying the basic Fiat-Shamir HVZK coupling (`FiatShamir/HVZKTransferReduction.lean`, reduced to
the coupling identity in PR #272):

`processRound_step_coupling` — running one Fiat-Shamir round `processRoundFS j` (challenges answered
by the canonical uniform `fsChallengeUniformImpl`) and projecting to its messages induces the SAME
distribution as running one interactive round `processRound j` (challenges from the verifier
`challengeQueryImpl`) and projecting to its messages, for any starting partial transcript and prover
state.

Both prover rounds split on the round direction `pSpec.dir j`:

* `P_to_V`: both rounds `sendMessage` then update state identically — a direct `congr` match (the
  message is appended to the transcript; `Fin.dconcat_eq_snoc`/`Fin.lastCases` reconciles the
  `MessagesUpTo` view).
* `V_to_P`: `processRoundFS` draws `receiveChallenge` *then* the challenge while interactive
  `processRound` draws the challenge *then* `receiveChallenge`. After `StateT.run`, both challenge
  draws reduce to the same fresh uniform `$ᵗ` (the committed challenge atoms), and the two draws are
  independent, so `OracleComp.evalDist_bind_comm` swaps `processRoundFS`'s order to match. The
  transcript views are reconciled with the canonical `Transcript.toMessagesUpTo_concat_*`
  lemmas, and native monad laws distribute the state pairing.

This is the genuine distributional kernel of the coupling; it is `axiom`-clean (depends only on
`propext`, `Classical.choice`, `Quot.sound`).
-/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace Reduction

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} [∀ i, VCVCompatible (pSpec.Challenge i)]
  (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)

-- The historical step equality observes every event in the retained execution payload.
private local instance (i : Fin (n + 1)) :
    MeasurableSpace (MessagesUpTo i pSpec × P.PrvState i × σ) := ⊤

/-- **Per-round coupling step.** One Fiat-Shamir round (canonical uniform challenge implementation),
projected to its messages, has the same `evalDist` as one interactive round (verifier challenges),
projected to its messages — for any starting partial transcript `t` and prover state `st`. The
`succ`-step of the `runToRoundFS` ↔ `runToRound` coupling induction (#116). -/
theorem processRound_step_coupling (impl : QueryImpl oSpec (StateT σ ProbComp))
    (stmt : StmtIn) (j : Fin n)
    (t : Transcript j.castSucc pSpec) (st : P.PrvState j.castSucc) (σ' : σ) :
    evalDist ((fun r => (r.1.1, r.1.2.2, r.2)) <$>
        (StateT.run (simulateQ (impl.addLift (fsChallengeUniformImpl (σ := σ)) :
            QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
          (P.processRoundFS j (pure (t.toMessagesUpTo, stmt, st)))) σ'))
      = evalDist ((fun r => (r.1.1.toMessagesUpTo, r.1.2, r.2)) <$>
        (StateT.run (simulateQ (impl.addLift challengeQueryImpl :
            QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
          (P.processRound j (pure (t, st)))) σ')) := by
  with_unfolding_all
    simp only [Prover.processRoundFS, Prover.processRound, pure_bind]
    split
    · rename_i hDirFS
      split
      · rename_i hDirInt
        -- The challenge draw is independent of the prover's receive step. Native measure
        -- commutation swaps the draws; the canonical transcript-view lemma reconciles messages.
        simp only [simulateQ_bind, simulateQ_map, StateT.run_bind, StateT.run_map, map_bind,
          _root_.map_pure, bind_pure_comp, Function.comp,
          simulateQ_addLift_fsChallengeUniform_query_run,
          simulateQ_addLift_challengeQueryImpl_getChallenge_run]
        simp only [QueryImpl.addLift_def, QueryImpl.liftTarget_self,
          QueryImpl.simulateQ_add_liftComp_left, ← OracleComp.liftComp_eq_liftM,
          fsChallengeUniformImpl, challengeQueryImpl, StateT.run, StateT.run_map, map_bind,
          _root_.map_pure, bind_pure_comp, Function.comp]
        simp only [Functor.map_map, Function.comp, ← bind_pure_comp, bind_assoc, pure_bind]
        have hext : ∀ (cc : pSpec.Challenge ⟨j, hDirInt⟩),
            (Transcript.concat cc t).toMessagesUpTo = t.toMessagesUpTo.extend hDirFS :=
          fun cc => Transcript.toMessagesUpTo_concat_challenge t hDirFS cc
        dsimp only [ProtocolSpec.fsChallengeOracle, ProtocolSpec.srChallengeOracle,
          OracleSpec.ofFn, OracleSpec.Range, OracleInterface.toOracleSpec,
          OracleInterface.Response, ProtocolSpec.challengeOracleInterfaceSR]
        simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply, hext]
        exact OracleComp.evalDist_bind_comm _ _ _
      · rename_i hDirInt
        exact absurd (hDirFS.symm.trans hDirInt) (by decide)
    · rename_i hDirFS
      split
      · rename_i hDirInt
        exact absurd (hDirInt.symm.trans hDirFS) (by decide)
      · rename_i hDirInt
        -- both `P_to_V`: identical `sendMessage`; the appended message reconciles under the
        -- `MessagesUpTo` view (`Fin.dconcat_eq_snoc`/`Fin.lastCases`).
        simp only [QueryImpl.addLift_def, QueryImpl.liftTarget_self, ← OracleComp.liftComp_eq_liftM,
          QueryImpl.simulateQ_add_liftComp_left, simulateQ_bind, simulateQ_pure, simulateQ_map,
          StateT.run_bind, StateT.run_pure, StateT.run_map, evalDist_bind, evalDist_pure,
          evalDist_map, map_bind, _root_.map_pure, Function.comp, bind_pure_comp]
        simp only [Functor.map_map, Function.comp]
        congr 2
        funext p
        congr 1
        exact (Transcript.toMessagesUpTo_concat_message t hDirFS p.1.1).symm

end Reduction

#print axioms Reduction.processRound_step_coupling
