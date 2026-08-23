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
  remaining step distributes the interactive side's `StateT.run` σ-pairing
  `(fun c => (c, σ')) <$> $ᵗ` — proven via the local `hd`/`hf` lemmas, applied with `erw` so the
  rewrite goes through the challenge-index `dir j = V_to_P` proof that sits (proof-irrelevantly) in
  the dependent map-lambda's binder type, where plain `rw`/`simp` cannot unify. Finally `rfl` closes
  the residual (proof irrelevance of `MessagesUpTo.extend` + `Prod` projection reduction).

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
  simp only [Prover.processRoundFS, Prover.processRound, pure_bind]
  split
  · rename_i hDirFS
    split
    · rename_i hDirInt
      -- both `V_to_P`. FS side reduces fully to `$ᵗ` (committed FS atom); the interactive
      -- `getChallenge` draw reduces by the committed challenge atom. After `StateT.run` the challenge
      -- draw is INDEPENDENT of `receiveChallenge`, so `evalDist_bind_comm` swaps FS's
      -- `do receiveChallenge; $ᵗ` to match int's `do $ᵗ; receiveChallenge`. Then the int's σ-pairing
      -- challenge draw is distributed (`hd`/`hf`, via `erw` for the proof-in-binder) and the
      -- messages reconcile (`hext`: the `V_to_P` challenge is not a message — `Fin.dconcat_eq_snoc`/
      -- `Fin.lastCases` twin of the `P_to_V` case).
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
          (Transcript.concat cc t).toMessagesUpTo = t.toMessagesUpTo.extend hDirFS := by
        intro cc
        funext idx
        obtain ⟨i, hi⟩ := idx
        simp only [MessagesUpTo.extend, MessagesUpTo.concat', Transcript.concat,
          Transcript.toMessagesUpTo, Fin.dconcat_eq_snoc]
        induction i using Fin.lastCases with
        | last =>
          exact absurd (hDirInt.symm.trans (show pSpec.dir j = Direction.P_to_V from hi))
            (by decide)
        | cast i' => simp only [Fin.snoc_castSucc]
      rw [evalDist_bind_comm]
      simp only [evalDist_bind, evalDist_pure, evalDist_map, map_bind, _root_.map_pure,
        bind_pure_comp, bind_assoc, pure_bind, hext, Function.comp]
      have hd : ∀ {T : Type} (x : ProbComp T),
          evalDist ((fun a => (a, σ')) <$> x) = evalDist x >>= fun a => pure (a, σ') := by
        intro T x
        rw [evalDist_map, ← bind_pure_comp]
      -- the int's σ-pairing draw matches `hd` up to the challenge-index proof (defeq by proof
      -- irrelevance, in the dependent lambda's binder); `erw` rewrites up to reducible defeq.
      erw [hd]
      have hf : ∀ {α' β' : Type} (p : SPMF α') (F : α' × σ → SPMF β'),
          (p >>= fun a => pure (a, σ')) >>= F = p >>= fun a => F (a, σ') := by
        intro α' β' p F
        rw [bind_assoc]
        simp only [pure_bind]
      erw [hf]
      rfl
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
      congr 1
      funext p
      congr 1
      funext idx
      obtain ⟨i, hi⟩ := idx
      simp only [Transcript.concat, Transcript.toMessagesUpTo, MessagesUpTo.concat,
        MessagesUpTo.concat', Fin.dconcat_eq_snoc]
      induction i using Fin.lastCases with
      | last => simp only [Fin.snoc_last]
      | cast i' => simp only [Fin.snoc_castSucc]

end Reduction
