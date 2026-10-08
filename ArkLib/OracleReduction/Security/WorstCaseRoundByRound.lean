/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Alexander Hicks
-/
import ArkLib.OracleReduction.Security.RoundByRound
import ArkLib.OracleReduction.Security.RbrGame

/-!
# Worst-case round-by-round security

Native adaptation of the prefix-wise bounds and their averaged-game implications from
ArkLib reviewed head `9b0b5c962d97a9a0a9388c0bcc7e70d503e9ddd9`.
The implication goes from a bound for every fixed prefix to the existing native game;
no converse or arbitrary-verifier composition theorem is asserted.
-/
set_option autoImplicit false
noncomputable section
open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ENNReal ProbabilityTheory
variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- The round-by-round extraction-failure event at challenge `i`: some intermediate witness
satisfies the knowledge state after the challenge, while its extraction fails it before. This is
the event `Verifier.rbrKnowledgeSoundnessWorstCase` bounds, named so that per-protocol bounds can
state it. -/
@[reducible]
def rbrExtractionFailureEvent {WitMid : Fin (n + 1) → Type}
    (kSF : (m : Fin (n + 1)) → StmtIn → Transcript m pSpec → WitMid m → Prop)
    (extractor : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid)
    (i : pSpec.ChallengeIdx) (stmtIn : StmtIn)
    (transcript : Transcript i.1.castSucc pSpec) (challenge : pSpec.Challenge i) : Prop :=
  ∃ witMid : WitMid i.1.succ,
    ¬ kSF i.1.castSucc stmtIn transcript
      (extractor.extractMid i.1 stmtIn (transcript.concat challenge) witMid) ∧
    kSF i.1.succ stmtIn (transcript.concat challenge) witMid

namespace Verifier

/-- Round-by-round knowledge soundness for one exact intermediate-witness
family, extractor, and knowledge-state function.  Unlike
`rbrKnowledgeSoundness`, these proof objects remain visible in the proposition
type and can therefore be inspected by downstream clients. -/
def rbrKnowledgeSoundnessWith
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
    Pr[fun ⟨transcript, challenge, _proveQueryLog⟩ =>
      ∃ witMid,
        ¬ kSF i.1.castSucc stmtIn transcript
          (extractor.extractMid i.1 stmtIn (transcript.concat challenge) witMid) ∧
          kSF i.1.succ stmtIn (transcript.concat challenge) witMid
    | do
      (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        (do
          let ⟨⟨transcript, _⟩, proveQueryLog⟩ ← prover.runWithLogToRound i.1.castSucc stmtIn witIn
          let challenge ← liftComp (pSpec.getChallenge i) _
          return (transcript, challenge, proveQueryLog))).run' (← init)] ≤
      rbrKnowledgeError i

/-- The existential RBR contract is exactly existence of the corresponding
extractor-specific contract. -/
theorem rbrKnowledgeSoundness_iff_exists_with
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0) :
    rbrKnowledgeSoundness init impl relIn relOut verifier rbrKnowledgeError ↔
      ∃ WitMid : Fin (n + 1) → Type,
      ∃ extractor : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid,
      ∃ kSF : verifier.KnowledgeStateFunction init impl relIn relOut extractor,
        rbrKnowledgeSoundnessWith init impl relIn relOut verifier
          WitMid extractor kSF rbrKnowledgeError := by
  rfl

/-! ### Worst-case-per-prefix variants

The standard literature definition of round-by-round (knowledge) soundness bounds the bad
transition probability for **every fixed transcript prefix**, quantified *before* the
challenge draw. ArkLib's `rbrSoundness` / `rbrKnowledgeSoundness` above instead sample the
prefix inside the game (via the prover run under the simulated oracles) and bound the
resulting **mixture** over prefixes — a formally weaker property with the same error
constants (safe direction: averaged ≤ worst-case). The definitions below are the faithful
worst-case forms, and the two implication theorems discharge the averaged forms from them
via the master mixture bound
`ProtocolSpec.prEvent_simulateQ_addLift_getChallenge_bind_le`
(`ArkLib/OracleReduction/Security/RbrGame.lean`).

Practical consequence: a protocol proven in the worst-case form gets the averaged form for
free, so prefer proving the worst-case variant. It is also the easier obligation to discharge
— it carries no prover quantifier at all, so one reasons about a fixed prefix and the fresh
challenge only. Conversely, a result established solely in the averaged form does **not**
yield the worst-case one; the implication runs in one direction. -/

/-- **Worst-case-per-prefix round-by-round soundness**, the standard literature shape: for
*every fixed* transcript prefix — not a prover-sampled one — the probability over only the
fresh challenge of a bad transition (state function false at the prefix, true after appending
the challenge) is at most the round error.
Implies `rbrSoundness` with the same error
(`rbrSoundnessWorstCase_implies_rbrSoundness`). -/
def rbrSoundnessWorstCase (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0) : Prop :=
  ∃ stateFunction : verifier.StateFunction init impl langIn langOut,
  ∀ stmtIn ∉ langIn,
  ∀ i : pSpec.ChallengeIdx,
  ∀ transcript : Transcript i.1.castSucc pSpec,
    Pr{let challenge ← $ᵗ (pSpec.Challenge i)}[
      ¬ stateFunction i.1.castSucc stmtIn transcript ∧
        stateFunction i.1.succ stmtIn (transcript.concat challenge)] ≤ rbrSoundnessError i

/-- **Worst-case-per-prefix round-by-round knowledge soundness**, the standard literature shape:
the knowledge analogue of `rbrSoundnessWorstCase`, with the bad-transition event of
`rbrKnowledgeSoundness` evaluated at every fixed transcript prefix over only the fresh
challenge. Implies `rbrKnowledgeSoundness` with the same error
(`rbrKnowledgeSoundnessWorstCase_implies_rbrKnowledgeSoundness`). -/
def rbrKnowledgeSoundnessWorstCase (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0) : Prop :=
  ∃ WitMid : Fin (n + 1) → Type,
  ∃ extractor : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid,
  ∃ kSF : verifier.KnowledgeStateFunction init impl relIn relOut extractor,
  ∀ stmtIn : StmtIn,
  ∀ i : pSpec.ChallengeIdx,
  ∀ transcript : Transcript i.1.castSucc pSpec,
    Pr{let challenge ← $ᵗ (pSpec.Challenge i)}[
      ∃ witMid,
        ¬ kSF i.1.castSucc stmtIn transcript
          (extractor.extractMid i.1 stmtIn (transcript.concat challenge) witMid) ∧
          kSF i.1.succ stmtIn (transcript.concat challenge) witMid] ≤ rbrKnowledgeError i

/-- Worst-case-per-prefix RBR knowledge soundness for one exact
intermediate-witness family, extractor, and knowledge-state function. -/
def rbrKnowledgeSoundnessWorstCaseWith
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (WitMid : Fin (n + 1) → Type)
    (extractor : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid)
    (kSF : verifier.KnowledgeStateFunction init impl relIn relOut extractor)
    (rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0) : Prop :=
  ∀ stmtIn : StmtIn,
  ∀ i : pSpec.ChallengeIdx,
  ∀ transcript : Transcript i.1.castSucc pSpec,
    Pr{let challenge ← $ᵗ (pSpec.Challenge i)}[
      ∃ witMid,
        ¬ kSF i.1.castSucc stmtIn transcript
          (extractor.extractMid i.1 stmtIn (transcript.concat challenge) witMid) ∧
          kSF i.1.succ stmtIn (transcript.concat challenge) witMid] ≤ rbrKnowledgeError i

/-- The existential worst-case RBR contract is exactly existence of the
corresponding extractor-specific contract. -/
theorem rbrKnowledgeSoundnessWorstCase_iff_exists_with
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0) :
    rbrKnowledgeSoundnessWorstCase init impl relIn relOut verifier rbrKnowledgeError ↔
      ∃ WitMid : Fin (n + 1) → Type,
      ∃ extractor : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid,
      ∃ kSF : verifier.KnowledgeStateFunction init impl relIn relOut extractor,
        rbrKnowledgeSoundnessWorstCaseWith init impl relIn relOut verifier
          WitMid extractor kSF rbrKnowledgeError := by
  rfl

/-- Worst-case-per-prefix rbr soundness implies the (averaged) `rbrSoundness`, with the
same error: the averaged game's prefix distribution is a mixture, and the challenge is
drawn independently of the prefix, so the mixture probability is dominated by the
per-prefix supremum (master bound
`ProtocolSpec.prEvent_simulateQ_addLift_getChallenge_bind_le`). -/
theorem rbrSoundnessWorstCase_implies_rbrSoundness
    {langIn : Set StmtIn} {langOut : Set StmtOut}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0}
    (h : rbrSoundnessWorstCase init impl langIn langOut verifier rbrSoundnessError) :
    rbrSoundness init impl langIn langOut verifier rbrSoundnessError := by
  obtain ⟨sF, hsF⟩ := h
  refine ⟨sF, fun stmtIn hstmt WitIn WitOut witIn prover i => ?_⟩
  have hbound := ProtocolSpec.prEvent_simulateQ_addLift_getChallenge_bind_le
    init impl (prover.runToRound i.1.castSucc stmtIn witIn) i
    (fun tr c => (tr.1, c))
    (fun x => ¬ sF i.1.castSucc stmtIn x.1 ∧ sF i.1.succ stmtIn (x.1.concat x.2))
    (fun tr => hsF stmtIn hstmt i tr.1)
  have ht : ({True} : Set Prop) = {p | p} := by ext p; simp
  simp only [prEvent_eq_evalDist_of_discrete, ht, evalDist_apply_setOf,
    bind_pure_comp, probEvent_map, Function.comp_def] at hbound
  simpa only [← map_bind, probEvent_map, Function.comp_def, bind_pure_comp] using hbound

/-- Worst-case-per-prefix rbr knowledge soundness implies the (averaged)
`rbrKnowledgeSoundness`, with the same error (same mixture argument as
`rbrSoundnessWorstCase_implies_rbrSoundness`). -/
theorem rbrKnowledgeSoundnessWorstCase_implies_rbrKnowledgeSoundness
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0}
    (h : rbrKnowledgeSoundnessWorstCase init impl relIn relOut verifier rbrKnowledgeError) :
    rbrKnowledgeSoundness init impl relIn relOut verifier rbrKnowledgeError := by
  obtain ⟨WitMid, extractor, kSF, hkSF⟩ := h
  refine ⟨WitMid, extractor, kSF, fun stmtIn witIn prover i => ?_⟩
  have hbound := ProtocolSpec.prEvent_simulateQ_addLift_getChallenge_bind_le
    init impl (prover.runWithLogToRound i.1.castSucc stmtIn witIn) i
    (fun tr c => (tr.1.1, c, tr.2))
    (fun x => ∃ witMid,
      ¬ kSF i.1.castSucc stmtIn x.1
        (extractor.extractMid i.1 stmtIn (x.1.concat x.2.1) witMid) ∧
        kSF i.1.succ stmtIn (x.1.concat x.2.1) witMid)
    (fun tr => hkSF stmtIn i tr.1.1)
  have ht : ({True} : Set Prop) = {p | p} := by ext p; simp
  simp only [prEvent_eq_evalDist_of_discrete, ht, evalDist_apply_setOf,
    bind_pure_comp, probEvent_map, Function.comp_def] at hbound
  simpa only [← map_bind, probEvent_map, Function.comp_def, bind_pure_comp] using hbound

/-- The exact-object worst-case RBR contract implies the exact-object averaged
contract without hiding the extractor or knowledge-state function. -/
theorem rbrKnowledgeSoundnessWorstCaseWith_implies_rbrKnowledgeSoundnessWith
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {WitMid : Fin (n + 1) → Type}
    {extractor : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid}
    {kSF : verifier.KnowledgeStateFunction init impl relIn relOut extractor}
    {rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0}
    (h : rbrKnowledgeSoundnessWorstCaseWith init impl relIn relOut verifier
      WitMid extractor kSF rbrKnowledgeError) :
    rbrKnowledgeSoundnessWith init impl relIn relOut verifier
      WitMid extractor kSF rbrKnowledgeError := by
  intro stmtIn witIn prover i
  have hbound := ProtocolSpec.prEvent_simulateQ_addLift_getChallenge_bind_le
    init impl (prover.runWithLogToRound i.1.castSucc stmtIn witIn) i
    (fun tr c => (tr.1.1, c, tr.2))
    (fun x => ∃ witMid,
      ¬ kSF i.1.castSucc stmtIn x.1
        (extractor.extractMid i.1 stmtIn (x.1.concat x.2.1) witMid) ∧
        kSF i.1.succ stmtIn (x.1.concat x.2.1) witMid)
    (fun tr => h stmtIn i tr.1.1)
  have ht : ({True} : Set Prop) = {p | p} := by ext p; simp
  simp only [prEvent_eq_evalDist_of_discrete, ht, evalDist_apply_setOf,
    bind_pure_comp, probEvent_map, Function.comp_def] at hbound
  simpa only [← map_bind, probEvent_map, Function.comp_def, bind_pure_comp] using hbound

end Verifier
end
