/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.Security.ZeroKnowledge

/-!
# Perfect HVZK for the statement-echo non-interactive reduction (issue #112)

A substantive perfect zero-knowledge instance beyond the trivial identity reduction: the
single-message "echo" reduction (prover replays the public statement) is perfect HVZK for any
relation, with the explicit public-replay simulator and an exact transcript-distribution
equality (error 0). `echo_perfectHVZK` + corollaries.
-/


noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace Issue112ZK

variable {ι : Type} {oSpec : OracleSpec ι}
  {Statement Witness : Type} {σ : Type}

/-- The single-message protocol spec: one prover-to-verifier message of type `Statement`. -/
abbrev echoPSpec (Statement : Type) : ProtocolSpec 1 := ⟨!v[.P_to_V], !v[Statement]⟩

/-- `echoPSpec` is prover-only (the unique round is a P_to_V message). -/
instance : ProtocolSpec.ProverOnly (echoPSpec Statement) where
  prover_first' := rfl

/-- The "statement echo" prover for the single-message reduction: it keeps `(stmt, wit)` as state,
  sends the statement as its one message, and outputs the input context unchanged. No randomness,
  no oracle queries, no witness in the message. -/
def echoProver : Prover oSpec Statement Witness Statement Witness (echoPSpec Statement) where
  PrvState := fun _ => Statement × Witness
  input := _root_.id
  sendMessage | ⟨0, _⟩ => fun state => pure (state.1, state)
  receiveChallenge | ⟨0, h⟩ => nomatch h
  output := pure

/-- The verifier for the echo reduction: accept and return the input statement. -/
def echoVerifier : Verifier oSpec Statement Statement (echoPSpec Statement) where
  verify := fun stmt _ => pure stmt

/-- The "statement echo" non-interactive reduction. -/
def echoReduction : Reduction oSpec Statement Witness Statement Witness (echoPSpec Statement) where
  prover := echoProver
  verifier := echoVerifier

/-- The transcript carrying a single message `m` for the echo protocol spec. -/
def echoTranscript (m : Statement) : FullTranscript (echoPSpec Statement) :=
  fun i => match i with | ⟨0, _⟩ => m

/-- Running the echo reduction is a `pure`: the transcript is the input statement, the prover output
  is the input context, the verifier output is the input statement. No randomness, no oracle
  queries, no failure. -/
theorem echoReduction_run (stmt : Statement) (wit : Witness) :
    (echoReduction : Reduction oSpec Statement Witness _ _ _).run stmt wit =
      pure ⟨⟨echoTranscript stmt, stmt, wit⟩, stmt⟩ := by
  rw [Reduction.run_of_prover_first]
  simp only [echoReduction, echoProver, echoVerifier]
  rfl

/-- The simulator for the echo reduction: from the input statement alone, emit the transcript whose
  single message is that statement. This is the "replay the public data" simulator — it never sees
  the witness. -/
def echoSimulator :
    Reduction.TranscriptSimulator oSpec Statement (echoPSpec Statement) :=
  fun stmt => pure (echoTranscript stmt)

/-- The honest transcript distribution of the echo reduction equals (in `evalDist`) the simulated
  one: `pure (echoTranscript stmt)`. The honest computation still samples and discards the ambient
  initialization state, so this is an `evalDist` (PMF) equality rather than a raw term equality. -/
theorem honestTranscriptDist_echo_evalDist
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (stmt : Statement) (wit : Witness) :
    evalDist (Reduction.honestTranscriptDist init impl
        (echoReduction : Reduction oSpec Statement Witness _ _ _) stmt wit) =
      evalDist (pure (echoTranscript stmt) :
        OptionT ProbComp (FullTranscript (echoPSpec Statement))) := by
  apply evalDist_ext
  intro transcript
  classical
  unfold Reduction.honestTranscriptDist
  simp only [echoReduction_run, map_pure, OptionT.run_pure, simulateQ_pure, StateT.run'_eq,
    StateT.run_pure, bind_pure_comp]
  rw [OptionT.probOutput_eq, OptionT.probOutput_eq]
  simp [probOutput_map_const, HasEvalPMF.probFailure_eq_zero]

/-- **Main theorem.** The single-message "statement echo" reduction satisfies PERFECT
  honest-verifier zero-knowledge for any input relation, with the public-statement-replay simulator.
  The honest and simulated transcript distributions are exactly equal (error 0). -/
theorem echo_perfectHVZK
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set (Statement × Witness)) :
    Reduction.perfectHVZK init impl rel
      (echoReduction : Reduction oSpec Statement Witness _ _ _)
      echoSimulator := by
  intro stmt wit _
  exact (honestTranscriptDist_echo_evalDist init impl stmt wit).symm

/-- The echo reduction satisfies statistical HVZK with error `0` (equivalently, any error). -/
theorem echo_statisticalHVZK
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set (Statement × Witness)) (ε : ℝ≥0) :
    Reduction.statisticalHVZK init impl rel
      (echoReduction : Reduction oSpec Statement Witness _ _ _)
      echoSimulator ε :=
  (echo_perfectHVZK init impl rel).statisticalHVZK ε

/-- The echo reduction is honest-verifier zero-knowledge (a simulator achieving perfect HVZK
  exists) for any input relation. -/
theorem echo_isHVZK
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set (Statement × Witness)) :
    Reduction.isHVZK init impl rel
      (echoReduction : Reduction oSpec Statement Witness _ _ _) :=
  ⟨echoSimulator, echo_perfectHVZK init impl rel⟩

/-- The echo reduction is statistically HVZK with any error bound. -/
theorem echo_isStatHVZK
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set (Statement × Witness)) (ε : ℝ≥0) :
    Reduction.isStatHVZK init impl rel
      (echoReduction : Reduction oSpec Statement Witness _ _ _) ε :=
  (echo_isHVZK init impl rel).isStatHVZK ε

#print axioms honestTranscriptDist_echo_evalDist
#print axioms echo_perfectHVZK
#print axioms echo_statisticalHVZK
#print axioms echo_isHVZK
#print axioms echo_isStatHVZK

end Issue112ZK
