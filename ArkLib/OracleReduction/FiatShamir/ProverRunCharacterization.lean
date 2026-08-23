/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.ChallengeOracleSampling

/-!
# Characterization of the Fiat-Shamir prover run (#116)

Building blocks for coupling the honest Fiat-Shamir transcript distribution to the interactive one
(the remaining `coupling` kernel of the basic-FS HVZK transfer). Both the interactive prover
(`Prover.runToRound`) and the Fiat-Shamir prover (`Prover.runToRoundFS`) are `Fin.induction`s over
the rounds whose per-round step (`Prover.processRound` / `Prover.processRoundFS`) sends a message on
`P_to_V` rounds and consumes a challenge on `V_to_P` rounds; they differ only in *how* the challenge
is obtained (interactive challenge oracle vs Fiat-Shamir challenge oracle) and in *what* is stored
(full transcript vs message bundle).

This file records:

* `dir_eq_PtoV_of_isEmpty_challengeIdx` — when there are no challenge rounds, every round is `P_to_V`.
* `processRoundFS_of_PtoV` / `processRound_of_PtoV` — the per-round step collapses to a bare
  `sendMessage`/`concat` on a `P_to_V` round.
* `evalWithAnswerFn_processRoundFS` — evaluating one Fiat-Shamir round against a fixed answer table
  `g` peels the previous round's result and then processes round `i` deterministically (the
  `V_to_P` branch reads `g` at the challenge query point). This is the recursion step used to drive
  the eager-table coupling.
-/

open ProtocolSpec OracleComp OracleSpec

set_option linter.unusedSectionVars false

namespace ProtocolSpec

/-- Extracting the messages of a transcript extended by a `P_to_V` message equals extending the
extracted messages by that message: `toMessagesUpTo` commutes with `concat` on message rounds.
(`Transcript.concat` is `Fin.snoc`; `MessagesUpTo.concat` is `Fin.dconcat`; these agree.) -/
theorem toMessagesUpTo_concat {n : ℕ} {pSpec : ProtocolSpec n} {m : Fin n}
    (h : pSpec.dir m = .P_to_V)
    (T : Transcript m.castSucc pSpec) (msg : pSpec.Message ⟨m, h⟩) :
    (Transcript.concat msg T).toMessagesUpTo = MessagesUpTo.concat T.toMessagesUpTo h msg := by
  funext j
  obtain ⟨i, hi⟩ := j
  simp only [Transcript.toMessagesUpTo, Transcript.concat, MessagesUpTo.concat,
    MessagesUpTo.concat']
  revert hi
  induction i using Fin.lastCases with
  | last => intro _; simp [Fin.snoc_last, Fin.dconcat_last]
  | cast k => intro _; simp [Fin.snoc_castSucc, Fin.dconcat_castSucc]

namespace MessagesUpTo

/-- When the protocol has no challenge rounds, the Fiat-Shamir partial transcript derivation never
queries the challenge oracle: it is a pure assembly of the messages into a transcript. -/
theorem deriveTranscriptSRAux_noChallenge {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type}
    {oSpec : OracleSpec ι} {StmtIn : Type} [IsEmpty pSpec.ChallengeIdx]
    (stmt : StmtIn) (k : Fin (n + 1)) (messages : pSpec.MessagesUpTo k) (j : Fin (k + 1)) :
    ∃ t, deriveTranscriptSRAux (oSpec := oSpec) stmt k messages j = pure t := by
  induction j using Fin.induction with
  | zero =>
    refine ⟨fun i => i.elim0, ?_⟩
    simp only [deriveTranscriptSRAux, Fin.induction_zero]
  | succ i ih =>
    obtain ⟨t, ht⟩ := ih
    simp only [deriveTranscriptSRAux] at ht ⊢
    rw [Fin.induction_succ, ht, pure_bind]
    split
    · next hd => exact (IsEmpty.false (⟨i.castLE (by omega), hd⟩ : pSpec.ChallengeIdx)).elim
    · next _ => exact ⟨_, rfl⟩

end MessagesUpTo

namespace Messages

/-- When the protocol has no challenge rounds, the Fiat-Shamir full-transcript derivation is a pure
assembly of the messages into a transcript (no challenge oracle query). -/
theorem deriveTranscriptFS_noChallenge {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type}
    {oSpec : OracleSpec ι} {StmtIn : Type} [IsEmpty pSpec.ChallengeIdx]
    (stmt : StmtIn) (messages : pSpec.Messages) :
    ∃ t, Messages.deriveTranscriptFS (oSpec := oSpec) stmt messages = pure t :=
  MessagesUpTo.deriveTranscriptSRAux_noChallenge stmt (Fin.last n) messages (Fin.last n)

end Messages

end ProtocolSpec

namespace Reduction

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)] [∀ i, VCVCompatible (pSpec.Message i)]
  [DecidableEq StmtIn] [∀ i, DecidableEq (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Challenge i)]

/-- When the protocol has no challenge rounds, every round sends a prover message. -/
theorem dir_eq_PtoV_of_isEmpty_challengeIdx [IsEmpty pSpec.ChallengeIdx] (j : Fin n) :
    pSpec.dir j = .P_to_V := by
  rcases hd : pSpec.dir j with _ | _
  · rfl
  · exact (IsEmpty.false (⟨j, hd⟩ : pSpec.ChallengeIdx)).elim

/-- The Fiat-Shamir round step on a `P_to_V` round is a bare `sendMessage` followed by a
message-bundle `concat`: no challenge oracle is queried. -/
theorem processRoundFS_of_PtoV
    (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) (j : Fin n)
    (hj : pSpec.dir j = .P_to_V)
    (cur : OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)
      (pSpec.MessagesUpTo j.castSucc × StmtIn × P.PrvState j.castSucc)) :
    P.processRoundFS j cur =
      (do
        let x ← cur
        let ⟨msg, newState⟩ ← P.sendMessage ⟨j, hj⟩ x.2.2
        return ⟨x.1.concat hj msg, x.2.1, newState⟩) := by
  unfold Prover.processRoundFS
  congr 1
  funext x
  obtain ⟨messages, stmtIn, state⟩ := x
  dsimp only
  split
  · next hd => exact Direction.noConfusion (hd.symm.trans hj)
  · next _ => rfl

/-- The interactive round step on a `P_to_V` round is a bare `sendMessage` followed by a transcript
`concat`: no challenge oracle is queried. -/
theorem processRound_of_PtoV
    (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) (j : Fin n)
    (hj : pSpec.dir j = .P_to_V)
    (cur : OracleComp (oSpec + [pSpec.Challenge]ₒ)
      (pSpec.Transcript j.castSucc × P.PrvState j.castSucc)) :
    P.processRound j cur =
      (do
        let x ← cur
        let ⟨msg, newState⟩ ← P.sendMessage ⟨j, hj⟩ x.2
        return ⟨x.1.concat msg, newState⟩) := by
  unfold Prover.processRound
  congr 1
  funext x
  obtain ⟨transcript, state⟩ := x
  dsimp only
  split
  · next hd => exact Direction.noConfusion (hd.symm.trans hj)
  · next _ => rfl

/-- Running the Fiat-Shamir prover to round `i.succ`, then interpreting every Fiat-Shamir query by a
fixed answer table `g`, peels the previous-round result and processes round `i` (the `V_to_P` branch
reads `g` at the round's challenge query point). The deterministic recursion step behind the
eager challenge-table coupling. -/
theorem evalWithAnswerFn_processRoundFS
    (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) (i : Fin n)
    (cur : OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)
      (pSpec.MessagesUpTo i.castSucc × StmtIn × P.PrvState i.castSucc))
    (g : (q : (oSpec + fsChallengeOracle StmtIn pSpec).Domain) →
      (oSpec + fsChallengeOracle StmtIn pSpec).Range q) :
    evalWithAnswerFn (QueryImpl.ofFn g) (P.processRoundFS i cur) =
      (let r := evalWithAnswerFn (QueryImpl.ofFn g) cur
       evalWithAnswerFn (QueryImpl.ofFn g)
        (match hd : pSpec.dir i with
        | .V_to_P => do
            let f ← P.receiveChallenge ⟨i, hd⟩ r.2.2
            let challenge ← query (spec := fsChallengeOracle StmtIn pSpec) ⟨⟨i, hd⟩, ⟨r.2.1, r.1⟩⟩
            return ⟨r.1.extend hd, r.2.1, f challenge⟩
        | .P_to_V => do
            let ⟨msg, newState⟩ ← P.sendMessage ⟨i, hd⟩ r.2.2
            return ⟨r.1.concat hd msg, r.2.1, newState⟩)) := by
  unfold Prover.processRoundFS
  rw [evalWithAnswerFn_bind]
  rfl

/-- Interactive analogue of `evalWithAnswerFn_processRoundFS`: running the interactive prover one
round against a fixed answer table peels the previous-round result and processes round `i` (the
`V_to_P` branch reads the challenge from the table). -/
theorem evalWithAnswerFn_processRound
    (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) (i : Fin n)
    (cur : OracleComp (oSpec + [pSpec.Challenge]ₒ)
      (pSpec.Transcript i.castSucc × P.PrvState i.castSucc))
    (g : (q : (oSpec + [pSpec.Challenge]ₒ).Domain) → (oSpec + [pSpec.Challenge]ₒ).Range q) :
    evalWithAnswerFn (QueryImpl.ofFn g) (P.processRound i cur) =
      (let r := evalWithAnswerFn (QueryImpl.ofFn g) cur
       evalWithAnswerFn (QueryImpl.ofFn g)
        (match hd : pSpec.dir i with
        | .V_to_P => do
            let challenge ← pSpec.getChallenge ⟨i, hd⟩
            letI newState := (← P.receiveChallenge ⟨i, hd⟩ r.2) challenge
            return ⟨r.1.concat challenge, newState⟩
        | .P_to_V => do
            let ⟨msg, newState⟩ ← P.sendMessage ⟨i, hd⟩ r.2
            return ⟨r.1.concat msg, newState⟩)) := by
  unfold Prover.processRound
  rw [evalWithAnswerFn_bind]
  rfl

/-- Evaluating a lifted empty-shared-oracle computation against any answer table is independent of
the table — and even of which appended oracle the lift targets. (An `OracleComp []ₒ` makes no
queries, so the answer table is never consulted.) -/
theorem eval_liftComp_emptySpec_cross {ι₁ ι₂ : Type} {s₁ : OracleSpec ι₁} {s₂ : OracleSpec ι₂}
    {α : Type} (oa : OracleComp []ₒ α) (f : QueryImpl ([]ₒ + s₁) Id) (g : QueryImpl ([]ₒ + s₂) Id) :
    evalWithAnswerFn f (OracleComp.liftComp oa ([]ₒ + s₁)) =
      evalWithAnswerFn g (OracleComp.liftComp oa ([]ₒ + s₂)) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp [evalWithAnswerFn]
  | query_bind t k ih => exact PEmpty.elim t

/-- When an oracle spec has empty query domain (no query is possible), simulating any computation
over it through a stateful probabilistic implementation collapses to a `pure` of its deterministic
value — equal to evaluating it against any total answer table. The bridge from the deterministic
`evalWithAnswerFn` semantics to the probabilistic `simulateQ`/`honestTranscriptDist` semantics in
the query-free case. -/
theorem simulateQ_run'_eq_pure_of_isEmpty_domain {ι : Type} {spec : OracleSpec ι}
    [IsEmpty spec.Domain] {σ α : Type} (impl : QueryImpl spec (StateT σ ProbComp))
    (comp : OracleComp spec α) (s : σ) (f : QueryImpl spec Id) :
    (simulateQ impl comp).run' s = pure (evalWithAnswerFn f comp) := by
  induction comp using OracleComp.inductionOn with
  | pure a =>
    rw [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure]
    rfl
  | query_bind t k ih => exact (IsEmpty.false t).elim

set_option maxHeartbeats 1000000 in
/-- **Challenge-free prover-run correspondence.** When the protocol has no challenge rounds and no
shared oracle (`oSpec = []ₒ`), the Fiat-Shamir prover run and the interactive prover run produce the
same messages (the FS message bundle is the interactive transcript's messages via `toMessagesUpTo`),
the same prover state, and carry the input statement — evaluated against any answer tables, since
neither run queries a challenge oracle. The prover half of the challenge-free basic-FS HVZK coupling.
-/
theorem prover_correspondence [IsEmpty pSpec.ChallengeIdx]
    (P : Prover []ₒ StmtIn WitIn StmtOut WitOut pSpec) (stmt : StmtIn) (wit : WitIn) (i : Fin (n + 1))
    (gFS : (q : ([]ₒ + fsChallengeOracle StmtIn pSpec).Domain) →
      ([]ₒ + fsChallengeOracle StmtIn pSpec).Range q)
    (gInt : (q : ([]ₒ + [pSpec.Challenge]ₒ).Domain) → ([]ₒ + [pSpec.Challenge]ₒ).Range q) :
    (evalWithAnswerFn (QueryImpl.ofFn gFS)
        (P.runToRoundFS i stmt (P.input (stmt, wit)))).1 =
      (evalWithAnswerFn (QueryImpl.ofFn gInt) (P.runToRound i stmt wit)).1.toMessagesUpTo ∧
    (evalWithAnswerFn (QueryImpl.ofFn gFS)
        (P.runToRoundFS i stmt (P.input (stmt, wit)))).2.2 =
      (evalWithAnswerFn (QueryImpl.ofFn gInt) (P.runToRound i stmt wit)).2 ∧
    (evalWithAnswerFn (QueryImpl.ofFn gFS)
        (P.runToRoundFS i stmt (P.input (stmt, wit)))).2.1 = stmt := by
  induction i using Fin.induction with
  | zero =>
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [Prover.runToRoundFS, Prover.runToRound, Fin.induction_zero, evalWithAnswerFn_pure]
    · exact Subsingleton.elim _ _
  | succ i ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih
    have hd : pSpec.dir i = .P_to_V := dir_eq_PtoV_of_isEmpty_challengeIdx i
    have hFS : P.runToRoundFS i.succ stmt (P.input (stmt, wit))
        = P.processRoundFS i (P.runToRoundFS i.castSucc stmt (P.input (stmt, wit))) := by
      simp only [Prover.runToRoundFS, Fin.induction_succ]
    have hInt : P.runToRound i.succ stmt wit
        = P.processRound i (P.runToRound i.castSucc stmt wit) := by
      simp only [Prover.runToRound, Fin.induction_succ]
    rw [hFS, processRoundFS_of_PtoV P i hd, hInt, processRound_of_PtoV P i hd]
    simp only [evalWithAnswerFn_bind]
    have hsend : evalWithAnswerFn (QueryImpl.ofFn gFS)
          (P.sendMessage ⟨i, hd⟩ (evalWithAnswerFn (QueryImpl.ofFn gFS)
            (P.runToRoundFS i.castSucc stmt (P.input (stmt, wit)))).2.2)
        = evalWithAnswerFn (QueryImpl.ofFn gInt)
          (P.sendMessage ⟨i, hd⟩ (evalWithAnswerFn (QueryImpl.ofFn gInt)
            (P.runToRound i.castSucc stmt wit)).2) := by
      rw [ih2]
      exact eval_liftComp_emptySpec_cross _ _ _
    refine ⟨?_, ?_, ?_⟩
    · rw [hsend, ih1]; exact (toMessagesUpTo_concat hd _ _).symm
    · exact congrArg Prod.snd hsend
    · exact ih3

end Reduction

#print axioms Reduction.dir_eq_PtoV_of_isEmpty_challengeIdx
#print axioms Reduction.processRoundFS_of_PtoV
#print axioms Reduction.processRound_of_PtoV
#print axioms Reduction.evalWithAnswerFn_processRoundFS
