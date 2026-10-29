/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.HVZKCouplingStep

/-!
# Prover-run coupling for the basic Fiat-Shamir HVZK coupling (#116)

Assembles the per-round `processRound_step_coupling` (HVZKCouplingStep) into the full prover-run
coupling `coupling_run`: running the Fiat-Shamir prover `runToRoundFS` (challenges from the canonical
uniform `fsChallengeUniformImpl`) up to any round, projected to its messages, induces the SAME
`evalDist` as running the interactive prover `runToRound` (verifier challenges) up to that round,
projected to its messages.

Proved by `Fin.induction` over rounds: the base case is the trivial empty run; the `succ` step peels
one round (`runToRoundFS_succ` / `runToRound_succ` + `processRound_pure_bind`), distributes
`evalDist` over the `simulateQ`/`StateT.run` bind, and factors each side through its round projection
to the common per-round continuation `G` — the FS side via `step_FS_indep` (the projected FS round
ignores the carried `StmtIn`), the interactive side via `processRound_step_coupling` — closing with
the inductive hypothesis. Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

open OracleComp OracleSpec ProtocolSpec

namespace Reduction

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} [∀ i, VCVCompatible (pSpec.Challenge i)]
  (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)

/-- `processRound j` is a Kleisli bind: `processRound j m = m >>= fun r => processRound j (pure r)`. -/
theorem processRound_pure_bind (j : Fin n)
    (m : OracleComp (oSpec + [pSpec.Challenge]ₒ) (pSpec.Transcript j.castSucc × P.PrvState j.castSucc)) :
    P.processRound j m = m >>= fun r => P.processRound j (pure r) := by
  unfold Prover.processRound
  simp only [pure_bind]

-- Retain the original all-events observation of messages, private state and shared state.
private local instance (i : Fin (n + 1)) :
    MeasurableSpace (pSpec.MessagesUpTo i × P.PrvState i × σ) := ⊤

/-- The projected FS round is independent of the carried input statement, already as a program. -/
private theorem step_FS_indep_run (impl : QueryImpl oSpec (StateT σ ProbComp)) (j : Fin n)
    (m : pSpec.MessagesUpTo j.castSucc) (s s' : StmtIn) (st : P.PrvState j.castSucc) (σ'' : σ) :
    (fun r => (r.1.1, r.1.2.2, r.2)) <$>
        (simulateQ (impl.addLift (fsChallengeUniformImpl (σ := σ)) :
            QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
          (P.processRoundFS j (pure (m, s, st)))).run σ'' =
      (fun r => (r.1.1, r.1.2.2, r.2)) <$>
        (simulateQ (impl.addLift (fsChallengeUniformImpl (σ := σ)) :
            QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
          (P.processRoundFS j (pure (m, s', st)))).run σ'' := by
  simp only [Prover.processRoundFS, pure_bind]
  split
  all_goals rename_i heq
  all_goals
    simp only [heq, simulateQ_bind, simulateQ_map, StateT.run_bind, StateT.run_map, map_bind,
      _root_.map_pure, bind_pure_comp, Function.comp,
      simulateQ_addLift_fsChallengeUniform_query_run]
    simp only [QueryImpl.addLift_def, QueryImpl.liftTarget_self,
      QueryImpl.simulateQ_add_liftComp_left, ← OracleComp.liftComp_eq_liftM,
      fsChallengeUniformImpl, StateT.run, StateT.run_map, map_bind, _root_.map_pure,
      bind_pure_comp, Function.comp, Functor.map_map]
  all_goals rfl

/-- The projected FS round's native measure is independent of the carried input statement. -/
theorem step_FS_indep (impl : QueryImpl oSpec (StateT σ ProbComp)) (j : Fin n)
    (m : pSpec.MessagesUpTo j.castSucc) (s s' : StmtIn) (st : P.PrvState j.castSucc) (σ'' : σ) :
    𝒟[(fun r => (r.1.1, r.1.2.2, r.2)) <$>
        (simulateQ (impl.addLift (fsChallengeUniformImpl (σ := σ)) :
            QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
          (P.processRoundFS j (pure (m, s, st)))).run σ''] =
      𝒟[(fun r => (r.1.1, r.1.2.2, r.2)) <$>
        (simulateQ (impl.addLift (fsChallengeUniformImpl (σ := σ)) :
            QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
          (P.processRoundFS j (pure (m, s', st)))).run σ''] := by
  rw [step_FS_indep_run P impl j m s s' st σ'']

/-- The prover-run coupling, by induction over rounds. -/
theorem coupling_run (impl : QueryImpl oSpec (StateT σ ProbComp))
    (stmt : StmtIn) (wit : WitIn) (j : Fin (n + 1)) (σ' : σ) :
    evalDist ((fun r => (r.1.1, r.1.2.2, r.2)) <$>
        StateT.run (simulateQ (impl.addLift (fsChallengeUniformImpl (σ := σ)) :
            QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
          (P.runToRoundFS j stmt (P.input (stmt, wit)))) σ')
      = evalDist ((fun r => (r.1.1.toMessagesUpTo, r.1.2, r.2)) <$>
        StateT.run (simulateQ (impl.addLift challengeQueryImpl :
            QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
          (P.runToRound j stmt wit)) σ') := by
  induction j using Fin.induction with
  | zero =>
    simp only [Prover.runToRoundFS, Prover.runToRound, Fin.induction_zero]
    simp only [simulateQ_pure, StateT.run_pure, _root_.map_pure, evalDist_pure]
    rfl
  | succ j ih =>
    let G : pSpec.MessagesUpTo j.castSucc × P.PrvState j.castSucc × σ →
        ProbComp (pSpec.MessagesUpTo j.succ × P.PrvState j.succ × σ) :=
      fun q => (fun r => (r.1.1, r.1.2.2, r.2)) <$>
        (simulateQ (impl.addLift (fsChallengeUniformImpl (σ := σ)) :
            QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
          (P.processRoundFS j (pure (q.1, stmt, q.2.1)))).run q.2.2
    rw [runToRoundFS_succ, Prover.runToRound_succ, processRound_pure_bind]
    simp only [simulateQ_bind, StateT.run_bind, map_bind]
    have hL : ∀ x : (pSpec.MessagesUpTo j.castSucc × StmtIn × P.PrvState j.castSucc) × σ,
        (fun r => (r.1.1, r.1.2.2, r.2)) <$>
            (simulateQ (impl.addLift (fsChallengeUniformImpl (σ := σ)) :
                QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
              (P.processRoundFS j (pure x.1))).run x.2 = G (x.1.1, x.1.2.2, x.2) := by
      rintro ⟨⟨m, s, st⟩, state⟩
      exact step_FS_indep_run P impl j m s stmt st state
    simp_rw [hL]
    rw [← bind_map_left]
    apply EvalDistEq.evalDist_eq
    apply EvalDistEq.trans ((EvalDistEq.of_evalDist_eq ih).bind_left G)
    rw [bind_map_left]
    apply EvalDistEq.symm
    apply EvalDistEq.bind_right
    rintro ⟨⟨t, st⟩, state⟩
    exact EvalDistEq.of_evalDist_eq (processRound_step_coupling P impl stmt j t st state).symm

#print axioms step_FS_indep
#print axioms coupling_run
end Reduction
