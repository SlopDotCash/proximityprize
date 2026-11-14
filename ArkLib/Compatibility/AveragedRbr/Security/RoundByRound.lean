/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Security.RoundByRound
import ArkLib.Compatibility.AveragedRbr.Security.RbrGame

/-!
# Historical prover-averaged round-by-round contracts

These declarations preserve downstream proofs of the prover-averaged game.
They come from ArkLib 1040ed0e6f208de9afd1a1aa56888ccd830c0964 before #1421.
-/

section

noncomputable section

open OracleComp OracleSpec ProtocolSpec

open scoped NNReal ProbabilityTheory

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

namespace Verifier

section RoundByRound

/-- **Prover-averaged round-by-round soundness** with respect to input language `langIn`, output
language `langOut`, and error `rbrSoundnessError`: there is a state function for the verifier and
the two languages such that, for every statement `stmtIn ∉ langIn`, every initial witness, every
prover, and every challenge round `i`, the probability that

  - the state function is false for the partial transcript output by the prover, and
  - the state function is true for that transcript extended by the next (random) challenge

is at most `rbrSoundnessError i`. Implied by `rbrSoundness` with the same error
(`rbrSoundness_implies_rbrSoundnessAveraged`). -/
def rbrSoundnessAveraged (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0) : Prop :=
  ∃ stateFunction : verifier.StateFunction init impl langIn langOut,
  ∀ stmtIn ∉ langIn,
  ∀ WitIn WitOut : Type,
  ∀ witIn : WitIn,
  ∀ prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec,
  ∀ i : pSpec.ChallengeIdx,
    Pr{let ⟨transcript, challenge⟩ ← do
      (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        (do
          let ⟨transcript, _⟩ ← prover.runToRound i.1.castSucc stmtIn witIn
          let challenge ← liftComp (pSpec.getChallenge i) _
          return (transcript, challenge))).run' (← init)}[
      ¬ stateFunction i.1.castSucc stmtIn transcript ∧
        stateFunction i.1.succ stmtIn (transcript.concat challenge)] ≤
      rbrSoundnessError i

/-- **Prover-averaged round-by-round knowledge soundness**: the knowledge analogue of
`rbrSoundnessAveraged`, with the bad-transition event of `rbrKnowledgeSoundness` evaluated at the
prefix a prover produces inside the game. Implied by `rbrKnowledgeSoundness` with the same error
(`rbrKnowledgeSoundness_implies_rbrKnowledgeSoundnessAveraged`). Like that notion, it quantifies
over unconstrained extractors and carries no efficiency content. -/
def rbrKnowledgeSoundnessAveraged (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0) : Prop :=
  ∃ WitMid : Fin (n + 1) → Type,
  ∃ extractor : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid,
  ∃ kSF : verifier.KnowledgeStateFunction init impl relIn relOut extractor,
  ∀ stmtIn : StmtIn,
  ∀ witIn : WitIn,
  ∀ prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec,
  ∀ i : pSpec.ChallengeIdx,
    Pr{let ⟨transcript, challenge, _proveQueryLog⟩ ← do
      (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        (do
          let ⟨⟨transcript, _⟩, proveQueryLog⟩ ← prover.runWithLogToRound i.1.castSucc stmtIn witIn
          let challenge ← liftComp (pSpec.getChallenge i) _
          return (transcript, challenge, proveQueryLog))).run' (← init)}[
      ∃ witMid,
        ¬ kSF i.1.castSucc stmtIn transcript
          (extractor.extractMid i.1 stmtIn (transcript.concat challenge) witMid) ∧
          kSF i.1.succ stmtIn (transcript.concat challenge) witMid] ≤
      rbrKnowledgeError i

/-- `rbrKnowledgeSoundnessAveraged` for one exact intermediate-witness family, extractor, and
knowledge state function, retained in the proposition type. The predicate bounds only the error;
it includes no cost bound for the stages of this extractor. -/
def rbrKnowledgeSoundnessAveragedWith
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (WitMid : Fin (n + 1) → Type)
    (extractor : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid)
    (kSF : verifier.KnowledgeStateFunction init impl relIn relOut extractor)
    (rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0) : Prop :=
  ∀ stmtIn : StmtIn,
  ∀ witIn : WitIn,
  ∀ prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec,
  ∀ i : pSpec.ChallengeIdx,
    Pr{let ⟨transcript, challenge, _proveQueryLog⟩ ← do
      (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        (do
          let ⟨⟨transcript, _⟩, proveQueryLog⟩ ←
            prover.runWithLogToRound i.1.castSucc stmtIn witIn
          let challenge ← liftComp (pSpec.getChallenge i) _
          return (transcript, challenge, proveQueryLog))).run' (← init)}[
      ∃ witMid,
        ¬ kSF i.1.castSucc stmtIn transcript
          (extractor.extractMid i.1 stmtIn (transcript.concat challenge) witMid) ∧
          kSF i.1.succ stmtIn (transcript.concat challenge) witMid] ≤
      rbrKnowledgeError i

/-- Round-by-round soundness implies its prover-averaged variant with the same error: the
averaged game's prefix distribution is a mixture, and the challenge is drawn independently of the
prefix, so the mixture probability is dominated by the per-prefix bound (mixture bound
`ProtocolSpec.prEvent_simulateQ_addLift_getChallenge_bind_le`). -/
theorem rbrSoundness_implies_rbrSoundnessAveraged
    {langIn : Set StmtIn} {langOut : Set StmtOut}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0}
    (h : rbrSoundness init impl langIn langOut verifier rbrSoundnessError) :
    rbrSoundnessAveraged init impl langIn langOut verifier rbrSoundnessError := by
  obtain ⟨sF, hsF⟩ := h
  refine ⟨sF, fun stmtIn hstmt WitIn WitOut witIn prover i => ?_⟩
  exact ProtocolSpec.prEvent_simulateQ_addLift_getChallenge_bind_le
    init impl (prover.runToRound i.1.castSucc stmtIn witIn) i
    (fun tr c => (tr.1, c))
    (fun x => ¬ sF i.1.castSucc stmtIn x.1 ∧ sF i.1.succ stmtIn (x.1.concat x.2))
    (fun tr => hsF stmtIn hstmt i tr.1)

/-- Round-by-round knowledge soundness implies its prover-averaged variant with the same error
(same mixture argument as `rbrSoundness_implies_rbrSoundnessAveraged`). -/
theorem rbrKnowledgeSoundness_implies_rbrKnowledgeSoundnessAveraged
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0}
    (h : rbrKnowledgeSoundness init impl relIn relOut verifier rbrKnowledgeError) :
    rbrKnowledgeSoundnessAveraged init impl relIn relOut verifier rbrKnowledgeError := by
  obtain ⟨WitMid, extractor, kSF, hkSF⟩ := h
  refine ⟨WitMid, extractor, kSF, fun stmtIn witIn prover i => ?_⟩
  exact ProtocolSpec.prEvent_simulateQ_addLift_getChallenge_bind_le
    init impl (prover.runWithLogToRound i.1.castSucc stmtIn witIn) i
    (fun tr c => (tr.1.1, c, tr.2))
    (fun x => ∃ witMid,
      ¬ kSF i.1.castSucc stmtIn x.1
        (extractor.extractMid i.1 stmtIn (x.1.concat x.2.1) witMid) ∧
        kSF i.1.succ stmtIn (x.1.concat x.2.1) witMid)
    (fun tr => hkSF stmtIn i tr.1.1)

/-- The extractor-specific round-by-round knowledge contract implies its prover-averaged variant
without hiding the extractor or knowledge state function. -/
theorem rbrKnowledgeSoundnessWith_implies_rbrKnowledgeSoundnessAveragedWith
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {WitMid : Fin (n + 1) → Type}
    {extractor : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid}
    {kSF : verifier.KnowledgeStateFunction init impl relIn relOut extractor}
    {rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0}
    (h : rbrKnowledgeSoundnessWith init impl relIn relOut verifier
      WitMid extractor kSF rbrKnowledgeError) :
    rbrKnowledgeSoundnessAveragedWith init impl relIn relOut verifier
      WitMid extractor kSF rbrKnowledgeError := by
  intro stmtIn witIn prover i
  exact ProtocolSpec.prEvent_simulateQ_addLift_getChallenge_bind_le
    init impl (prover.runWithLogToRound i.1.castSucc stmtIn witIn) i
    (fun tr c => (tr.1.1, c, tr.2))
    (fun x => ∃ witMid,
      ¬ kSF i.1.castSucc stmtIn x.1
        (extractor.extractMid i.1 stmtIn (x.1.concat x.2.1) witMid) ∧
        kSF i.1.succ stmtIn (x.1.concat x.2.1) witMid)
    (fun tr => h stmtIn i tr.1.1)

end RoundByRound

end Verifier

open Verifier

section OracleProtocol

variable
  {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type}
  {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type}
  [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
  [Oₛₒ : ∀ i, OracleInterface (OStmtOut i)]
  [∀ i, OracleInterface (pSpec.Message i)]

namespace OracleVerifier

/-- Prover-averaged round-by-round soundness (`Verifier.rbrSoundnessAveraged`) of an oracle
verifier: that of the verifier it induces. -/
def rbrSoundnessAveraged
    (langIn : Set (StmtIn × ∀ i, OStmtIn i))
    (langOut : Set (StmtOut × ∀ i, OStmtOut i))
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec)
    (rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0) : Prop :=
  verifier.toVerifier.rbrSoundnessAveraged init impl langIn langOut rbrSoundnessError

/-- Prover-averaged round-by-round knowledge soundness (`Verifier.rbrKnowledgeSoundnessAveraged`)
of an oracle verifier: that of the verifier it induces. -/
def rbrKnowledgeSoundnessAveraged
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut))
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec)
    (rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0) : Prop :=
  verifier.toVerifier.rbrKnowledgeSoundnessAveraged init impl relIn relOut rbrKnowledgeError

/-- Extractor-specific prover-averaged round-by-round knowledge soundness
(`Verifier.rbrKnowledgeSoundnessAveragedWith`) of an oracle verifier. -/
def rbrKnowledgeSoundnessAveragedWith
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut))
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec)
    (WitMid : Fin (n + 1) → Type)
    (extractor : Extractor.RoundByRound oSpec
      (StmtIn × (∀ i, OStmtIn i)) WitIn WitOut pSpec WitMid)
    (kSF : verifier.KnowledgeStateFunction init impl relIn relOut extractor)
    (rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0) : Prop :=
  verifier.toVerifier.rbrKnowledgeSoundnessAveragedWith init impl relIn relOut
    WitMid extractor kSF rbrKnowledgeError

end OracleVerifier

end OracleProtocol

variable {Statement : Type} {ιₛ : Type} {OStatement : ιₛ → Type} {Witness : Type}
  [∀ i, OracleInterface (OStatement i)]
  [∀ i, OracleInterface (pSpec.Message i)]

namespace OracleProof

/-- Prover-averaged round-by-round knowledge soundness (`Verifier.rbrKnowledgeSoundnessAveraged`)
of an oracle proof, with the empty output-oracle family discharged explicitly. -/
def rbrKnowledgeSoundnessAveraged
    (relIn : Set ((Statement × ∀ i, OStatement i) × Witness))
    (verifier : OracleProofVerifier oSpec Statement OStatement pSpec)
    (rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0) : Prop := by
  exact OracleVerifier.rbrKnowledgeSoundnessAveraged (Oₛₒ := fun i => nomatch i) init impl
    relIn acceptRejectOracleRel verifier rbrKnowledgeError

variable {init impl} in
/-- Round-by-round knowledge soundness of an oracle proof implies its prover-averaged variant
`OracleProof.rbrKnowledgeSoundnessAveraged`, with the same error. -/
theorem rbrKnowledgeSoundness_implies_rbrKnowledgeSoundnessAveraged
    {relIn : Set ((Statement × ∀ i, OStatement i) × Witness)}
    {verifier : OracleProofVerifier oSpec Statement OStatement pSpec}
    {rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0}
    (h : rbrKnowledgeSoundness init impl relIn verifier rbrKnowledgeError) :
    rbrKnowledgeSoundnessAveraged init impl relIn verifier rbrKnowledgeError :=
  Verifier.rbrKnowledgeSoundness_implies_rbrKnowledgeSoundnessAveraged init impl h

end OracleProof

section Trivial

/-- The identity / trivial verifier is perfectly round-by-round sound. -/
@[simp]
lemma Verifier.id_rbrSoundnessAveraged {lang : Set Statement} :
    (Verifier.id : Verifier oSpec Statement _ _).rbrSoundnessAveraged init impl lang lang 0 := by
  refine ⟨Verifier.StateFunction.id init impl, ?_⟩
  intro _ _ _ _ _ _ i
  exact Fin.elim0 i.1

/-- The identity / trivial verifier is perfectly round-by-round knowledge sound. -/
@[simp]
lemma Verifier.id_rbrKnowledgeSoundnessAveraged {rel : Set (Statement × Witness)} :
    (Verifier.id : Verifier oSpec Statement _ _).rbrKnowledgeSoundnessAveraged
      init impl rel rel 0 := by
  refine ⟨_, _, Verifier.KnowledgeStateFunction.id init impl, ?_⟩
  intro stmtIn witIn prover i
  exact Fin.elim0 i.1

/-- The identity / trivial oracle verifier is perfectly round-by-round knowledge sound. -/
@[simp]
lemma OracleVerifier.id_rbrKnowledgeSoundnessAveraged
    {rel : Set ((Statement × ∀ i, OStatement i) × Witness)} :
    (OracleVerifier.id :
      OracleVerifier oSpec Statement OStatement _ _ _).rbrKnowledgeSoundnessAveraged
        init impl rel rel 0 := by
  exact Verifier.id_rbrKnowledgeSoundnessAveraged init impl (rel := rel)

end Trivial

end

end
