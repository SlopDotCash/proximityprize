/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.SeamDecompositionRun
import ArkLib.OracleReduction.Execution

/-!
# Log-carrying seam factoring for the round-by-round knowledge experiment (issues #13 / #114 / #116)

Companion to `SeamDecompositionRun.lean`.  The round-by-round **knowledge** per-round event (used in
`rbrKnowledgeSoundness`, see `RoundByRound.lean`) runs the prover via `Prover.runWithLogToRound`,
which carries the prover's query log:

`runWithLogToRound i stmt wit = WriterT.run (simulateQ loggingOracle (runToRound i stmt wit))`.

The seam-factoring infrastructure of `SeamDecompositionRun.lean` is stated entirely over the
*log-free* `runToRound`.  This file bridges the gap.

The key structural fact is that the knowledge per-round **event is log-blind**: it inspects only the
transcript and challenge, discarding `proveQueryLog`.  We exploit this rather than fight a full HEq
transport through the `WriterT`/`loggingOracle` layer.  Two reusable bricks:

* `runWithLogToRound_bind_discardLog` — binding `runWithLogToRound` and discarding *both* the
  prover state and the query log collapses to binding `runToRound` and discarding the prover state.
  This is the `loggingOracle.run_simulateQ_bind_fst` log-collapse specialised to the prover run.
* `map_runWithLog_body_eq_run_body` — the log-carrying knowledge experiment body, post-composed with
  the log-discarding projection `(transcript, challenge, log) ↦ (transcript, challenge)`, equals the
  log-free soundness experiment body verbatim (same `simulateQ`/`run'`).  Hence the log-carrying
  experiment with a log-blind event reduces to the proven log-free seam game.

These are reusable for any log-carrying per-round game whose event ignores the log (knowledge
soundness #13/#114, knowledge-soundness FS transfer #116).  All declarations are axiom-clean and
`sorry`-free.
-/

open OracleComp OracleSpec ProtocolSpec

universe u

namespace Prover

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}

/-- **Log-collapse of a bind that discards the prover state and the query log.** Since
`runWithLogToRound i = WriterT.run (simulateQ loggingOracle (runToRound i))`, binding it and feeding
the continuation only the *transcript* (discarding both the prover state and the query log) is the
same as binding the log-free `runToRound`.  Specialises `loggingOracle.run_simulateQ_bind_fst`.

This is the core reusable brick: the knowledge per-round game's continuation
(`fun ⟨⟨transcript, _⟩, proveQueryLog⟩ => …`) uses only `transcript`, so this lemma rewrites the
log-carrying run away. -/
theorem runWithLogToRound_bind_discardLog {β : Type}
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (i : Fin (n + 1)) (stmt : StmtIn) (wit : WitIn)
    (k : pSpec.Transcript i → OracleComp (oSpec + [pSpec.Challenge]ₒ) β) :
    (prover.runWithLogToRound i stmt wit >>=
        fun x => k x.1.1) =
      (prover.runToRound i stmt wit >>= fun x => k x.1) := by
  unfold Prover.runWithLogToRound
  -- Collapse the writer-log layer: binding and projecting the first component of the
  -- `loggingOracle` run is binding the underlying `runToRound`.
  exact loggingOracle.run_simulateQ_bind_fst (prover.runToRound i stmt wit) (fun x => k x.1)

end Prover

namespace OracleReduction

variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}
  {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]
  (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- **The log-carrying knowledge experiment body equals the log-free soundness experiment body**
after discarding the log component of the result.

The left side is the body of the round-by-round *knowledge* per-round game
(`appendRbrKnowledgeSoundnessPerRoundResidual` / `rbrKnowledgeSoundness`): it runs
`runWithLogToRound`, samples the challenge under the simulated challenge oracle, and returns
`(transcript, challenge, proveQueryLog)`.  Mapping that result by the log-discarding projection
`(t, c, log) ↦ (t, c)` yields exactly the body of the *soundness* per-round game (which uses the
log-free `runToRound` and returns `(transcript, challenge)`).

Hence any event that is **blind to the query log** has the same probability under the log-carrying
game as under the proven log-free seam game.  This is the bridge that lets the whole log-free seam
toolkit of `SeamDecompositionRun.lean` apply to the knowledge experiment. -/
theorem map_runWithLog_body_eq_run_body
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (i : pSpec.ChallengeIdx) (stmt : StmtIn) (wit : WitIn) (s : σ) :
    ((fun x : pSpec.Transcript i.1.castSucc × pSpec.Challenge i ×
          QueryLog (oSpec + [pSpec.Challenge]ₒ) => (x.1, x.2.1)) <$>
        (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (do
            let ⟨⟨transcript, _⟩, proveQueryLog⟩ ← prover.runWithLogToRound i.1.castSucc stmt wit
            let challenge ← liftComp (pSpec.getChallenge i) _
            return (transcript, challenge, proveQueryLog))).run' s)
      = (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (do
            let ⟨transcript, _⟩ ← prover.runToRound i.1.castSucc stmt wit
            let challenge ← liftComp (pSpec.getChallenge i) _
            return (transcript, challenge))).run' s := by
  -- Push the log-discarding map inside `run'` and `simulateQ`.
  rw [← StateT.run'_map', ← simulateQ_map]
  congr 1
  -- The mapped inner computation: rewrite the final `return (t, c, log)` to `return (t, c)`.
  simp only [map_bind, map_pure]
  congr 1
  -- Now: `runWithLogToRound idx >>= fun ⟨⟨t,_⟩,log⟩ => (getChallenge >>= fun c => return (t, c))`,
  -- which discards both prover state and log — collapse via `runWithLogToRound_bind_discardLog`.
  exact Prover.runWithLogToRound_bind_discardLog prover i.1.castSucc stmt wit
    (fun transcript => do
      let challenge ← liftComp (pSpec.getChallenge i) _
      pure (transcript, challenge))

open scoped ENNReal in
/-- **Log-free reduction of a round-by-round knowledge per-round experiment** for *any* log-blind
event `Q` on `(transcript, challenge)`.  The log-carrying `runWithLogToRound` experiment has the same
event-probability as the log-free `runToRound` game.  Generic over the protocol/prover; specialises to
both the appended composite (over `pSpec₁ ++ₚ pSpec₂`) and the inner protocols. -/
theorem rbrKnowledge_logfree_reduce
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (i : pSpec.ChallengeIdx) (stmt : StmtIn) (wit : WitIn) (init : ProbComp σ)
    (Q : pSpec.Transcript i.1.castSucc × pSpec.Challenge i → Prop) :
    Pr[fun ⟨transcript, challenge, _proveQueryLog⟩ => Q (transcript, challenge)
      | do
        (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (do
            let ⟨⟨transcript, _⟩, proveQueryLog⟩ ← prover.runWithLogToRound i.1.castSucc stmt wit
            let challenge ← liftComp (pSpec.getChallenge i) _
            return (transcript, challenge, proveQueryLog))).run' (← init)]
      = Pr[Q
        | do
          (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
            (do
              let ⟨transcript, _⟩ ← prover.runToRound i.1.castSucc stmt wit
              let challenge ← liftComp (pSpec.getChallenge i) _
              return (transcript, challenge))).run' (← init)] := by
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  refine tsum_congr fun s => ?_
  congr 1
  rw [← map_runWithLog_body_eq_run_body impl prover i stmt wit s, probEvent_map]
  rfl

end OracleReduction
