/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Security.Basic

/-!
  # State-Restoration Security Definitions

  This file defines state-restoration security notions for (oracle) reductions.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

variable {ι : Type}

namespace Prover

/-- The type for the **state-restoration** prover in the soundness game.

Such a prover has query access to challenge oracles that can return the `i`-th challenge, for all
`i : pSpec.ChallengeIdx`, given the input statement and the transcript up to that point.
It returns an input statement, and a full transcript of interaction.

This is different from the state-restoration prover type in the knowledge soundness game, which
additionally needs to output an output witness. -/
def StateRestoration.Soundness (oSpec : OracleSpec ι) (StmtIn : Type)
    {n : ℕ} (pSpec : ProtocolSpec n) :=
  OracleComp (oSpec + (srChallengeOracle StmtIn pSpec)) (StmtIn × pSpec.Messages)

/-- The type for the **state-restoration** prover in the knowledge soundness game.

Such a prover has query access to challenge oracles that can return the `i`-th challenge, for all
`i : pSpec.ChallengeIdx`, given the input statement and the transcript up to that point.
It returns an input statement, a full transcript of interaction, and an output witness.

Note that the output witness is an addition compared to the state-restoration soundness prover
type. -/
def StateRestoration.KnowledgeSoundness (oSpec : OracleSpec ι) (StmtIn WitOut : Type)
    {n : ℕ} (pSpec : ProtocolSpec n) :=
  OracleComp (oSpec + (srChallengeOracle StmtIn pSpec)) (StmtIn × pSpec.Messages × WitOut)

end Prover

namespace OracleProver

/-- The type for the **state-restoration** oracle prover (in an oracle reduction) in the soundness
  game.

This is a wrapper around the state-restoration prover type in the soundness game for the associated
reduction. -/
@[reducible]
def StateRestoration.Soundness (oSpec : OracleSpec ι)
    (StmtIn : Type) {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type)
    {n : ℕ} {pSpec : ProtocolSpec n} :=
  Prover.StateRestoration.Soundness oSpec (StmtIn × (∀ i, OStmtIn i)) pSpec

/-- The type for the **state-restoration** oracle prover (in an oracle reduction) in the knowledge
  soundness game.

This is a wrapper around the state-restoration prover type in the knowledge soundness game for the
associated reduction. -/
@[reducible]
def StateRestoration.KnowledgeSoundness (oSpec : OracleSpec ι)
    (StmtIn : Type) {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type) (WitOut : Type)
    {n : ℕ} {pSpec : ProtocolSpec n} :=
  Prover.StateRestoration.KnowledgeSoundness oSpec (StmtIn × (∀ i, OStmtIn i)) WitOut pSpec

end OracleProver

namespace Extractor

/-- A straightline extractor for state-restoration. -/
def StateRestoration (oSpec : OracleSpec ι)
    (StmtIn WitIn WitOut : Type) {n : ℕ} (pSpec : ProtocolSpec n) :=
  StmtIn → -- input statement
  WitOut → -- output witness
  pSpec.FullTranscript → -- transcript
  QueryLog (oSpec + (srChallengeOracle StmtIn pSpec)) → -- prover's query log
  QueryLog oSpec → -- verifier's query log
  OracleComp oSpec WitIn -- an oracle computation that outputs an input witness

end Extractor

variable {oSpec : OracleSpec ι}
  {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
  {WitIn : Type}
  {StmtOut : Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} [Oₛₒ : ∀ i, OracleInterface (OStmtOut i)]
  {WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
  [DecidableEq StmtIn] [∀ i, DecidableEq (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Challenge i)]
  (init : ProbComp (QueryImpl (srChallengeOracle StmtIn pSpec) Id))
  (impl : QueryImpl oSpec (StateT (QueryImpl (srChallengeOracle StmtIn pSpec) Id) ProbComp))

/-- The state-restoration game for soundness. Basically a wrapper around the state-restoration
  prover to derive the full transcript from the messages output by the prover, with the challenges
  computed from the state-restoration oracle. -/
def srSoundnessGame (P : Prover.StateRestoration.Soundness oSpec StmtIn pSpec) :
    OracleComp (oSpec + (srChallengeOracle StmtIn pSpec))
      (pSpec.FullTranscript × StmtIn) := do
  let ⟨stmtIn, messages⟩ ← P
  let transcript ← messages.deriveTranscriptSR stmtIn
  return ⟨transcript, stmtIn⟩

/-- The state-restoration game for knowledge soundness. Basically a wrapper around the
    state-restoration prover (for knowledge soundness) to derive the full transcript from the
    messages output by the prover, with the challenges computed from the state-restoration oracle.
-/
def srKnowledgeSoundnessGame
    (P : Prover.StateRestoration.KnowledgeSoundness oSpec StmtIn WitOut pSpec) :
    OracleComp (oSpec + (srChallengeOracle StmtIn pSpec))
      (pSpec.FullTranscript × StmtIn × WitOut) := do
  let ⟨stmtIn, messages, witOut⟩ ← P
  let transcript ← messages.deriveTranscriptSR stmtIn
  return ⟨transcript, stmtIn, witOut⟩

namespace Verifier

namespace StateRestoration

/-- State-restoration soundness -/
def soundness
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (srSoundnessError : ENNReal) : Prop :=
  ∀ srProver : Prover.StateRestoration.Soundness oSpec StmtIn pSpec,
  Pr[ fun | ⟨stmtIn, some stmtOut⟩ => stmtOut ∈ langOut ∧ stmtIn ∉ langIn | _ => False
    | do (simulateQ (impl.addLift srChallengeQueryImpl' : QueryImpl _ (StateT _ ProbComp))
        <| (do
    let ⟨transcript, stmtIn⟩ ← srSoundnessGame srProver
    let stmtOut ← liftComp (verifier.run stmtIn transcript) _
    return (stmtIn, stmtOut))).run' (← init)
  ] ≤ srSoundnessError

omit [DecidableEq StmtIn] [∀ i, DecidableEq (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Challenge i)] in
/-- State-restoration soundness is monotone in the allowed soundness error. -/
theorem soundness.mono_error
    {langIn : Set StmtIn} {langOut : Set StmtOut}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {srSoundnessError₁ srSoundnessError₂ : ENNReal}
    (hSound : soundness init impl langIn langOut verifier srSoundnessError₁)
    (hle : srSoundnessError₁ ≤ srSoundnessError₂) :
    soundness init impl langIn langOut verifier srSoundnessError₂ := by
  intro srProver
  exact le_trans (hSound srProver) hle

omit [DecidableEq StmtIn] [∀ i, DecidableEq (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Challenge i)] in
/-- State-restoration soundness is monotone under enlarging the honest input language and shrinking
the accepting output language. -/
theorem soundness.mono_languages
    {langIn langIn' : Set StmtIn} {langOut langOut' : Set StmtOut}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {srSoundnessError : ENNReal}
    (hSound : soundness init impl langIn langOut verifier srSoundnessError)
    (hIn : langIn ⊆ langIn') (hOut : langOut' ⊆ langOut) :
    soundness init impl langIn' langOut' verifier srSoundnessError := by
  intro srProver
  refine le_trans ?_ (hSound srProver)
  exact probEvent_mono fun event _ hevent => by
    rcases event with ⟨stmtIn, stmtOut?⟩
    cases stmtOut? with
    | none => exact False.elim hevent
    | some stmtOut =>
        exact ⟨hOut hevent.1, fun hmem => hevent.2 (hIn hmem)⟩

omit [DecidableEq StmtIn] [∀ i, DecidableEq (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Challenge i)] in
/-- State-restoration soundness can simultaneously transport languages and relax the target
soundness error. -/
theorem soundness.mono_languages_error
    {langIn langIn' : Set StmtIn} {langOut langOut' : Set StmtOut}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {srSoundnessError₁ srSoundnessError₂ : ENNReal}
    (hSound : soundness init impl langIn langOut verifier srSoundnessError₁)
    (hIn : langIn ⊆ langIn') (hOut : langOut' ⊆ langOut)
    (hle : srSoundnessError₁ ≤ srSoundnessError₂) :
    soundness init impl langIn' langOut' verifier srSoundnessError₂ := by
  intro srProver
  refine le_trans ?_ (le_trans (hSound srProver) hle)
  exact probEvent_mono fun event _ hevent => by
    rcases event with ⟨stmtIn, stmtOut?⟩
    cases stmtOut? with
    | none => exact False.elim hevent
    | some stmtOut =>
        exact ⟨hOut hevent.1, fun hmem => hevent.2 (hIn hmem)⟩

/-- State-restoration knowledge soundness (w/ straightline extractor). -/
def knowledgeSoundness
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (srKnowledgeSoundnessError : ENNReal) : Prop :=
  ∃ srExtractor : Extractor.StateRestoration oSpec StmtIn WitIn WitOut pSpec,
  ∀ srProver : Prover.StateRestoration.KnowledgeSoundness oSpec StmtIn WitOut pSpec,
    Pr[ fun | ⟨stmtIn, witIn, some stmtOut, witOut⟩ =>
              (stmtOut, witOut) ∈ relOut ∧ (stmtIn, witIn) ∉ relIn
            | _ => False
    | do
      (simulateQ (impl.addLift srChallengeQueryImpl' : QueryImpl _ (StateT _ ProbComp))
          <| (do
            let ⟨transcript, stmtIn, witOut⟩ ← srKnowledgeSoundnessGame srProver
            let stmtOut ← liftComp (verifier.run stmtIn transcript) _
            -- The state-restoration game currently supplies default query logs; a strengthened SR
            -- game can thread the actual prover/verifier logs through this call.
            let witIn ← srExtractor stmtIn witOut transcript default default
            return (stmtIn, witIn, stmtOut, witOut))).run' (← init)
    ] ≤ srKnowledgeSoundnessError

omit [DecidableEq StmtIn] [∀ i, DecidableEq (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Challenge i)] in
/-- State-restoration knowledge soundness is monotone in the allowed knowledge-soundness error. -/
theorem knowledgeSoundness.mono_error
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {srKnowledgeSoundnessError₁ srKnowledgeSoundnessError₂ : ENNReal}
    (hSound : knowledgeSoundness init impl relIn relOut verifier srKnowledgeSoundnessError₁)
    (hle : srKnowledgeSoundnessError₁ ≤ srKnowledgeSoundnessError₂) :
    knowledgeSoundness init impl relIn relOut verifier srKnowledgeSoundnessError₂ := by
  obtain ⟨srExtractor, hSound⟩ := hSound
  exact ⟨srExtractor, fun srProver => le_trans (hSound srProver) hle⟩

omit [DecidableEq StmtIn] [∀ i, DecidableEq (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Challenge i)] in
/-- State-restoration knowledge soundness is monotone under enlarging the valid input relation and
shrinking the valid output relation. -/
theorem knowledgeSoundness.mono_relations
    {relIn relIn' : Set (StmtIn × WitIn)} {relOut relOut' : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {srKnowledgeSoundnessError : ENNReal}
    (hSound : knowledgeSoundness init impl relIn relOut verifier srKnowledgeSoundnessError)
    (hIn : relIn ⊆ relIn') (hOut : relOut' ⊆ relOut) :
    knowledgeSoundness init impl relIn' relOut' verifier srKnowledgeSoundnessError := by
  obtain ⟨srExtractor, hSound⟩ := hSound
  refine ⟨srExtractor, fun srProver => ?_⟩
  refine le_trans ?_ (hSound srProver)
  exact probEvent_mono fun event _ hevent => by
    rcases event with ⟨stmtIn, witIn, stmtOut?, witOut⟩
    cases stmtOut? with
    | none => exact False.elim hevent
    | some stmtOut =>
        exact ⟨hOut hevent.1, fun hmem => hevent.2 (hIn hmem)⟩

omit [DecidableEq StmtIn] [∀ i, DecidableEq (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Challenge i)] in
/-- State-restoration knowledge soundness can simultaneously transport relations and relax the
target knowledge-soundness error. -/
theorem knowledgeSoundness.mono_relations_error
    {relIn relIn' : Set (StmtIn × WitIn)} {relOut relOut' : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {srKnowledgeSoundnessError₁ srKnowledgeSoundnessError₂ : ENNReal}
    (hSound : knowledgeSoundness init impl relIn relOut verifier srKnowledgeSoundnessError₁)
    (hIn : relIn ⊆ relIn') (hOut : relOut' ⊆ relOut)
    (hle : srKnowledgeSoundnessError₁ ≤ srKnowledgeSoundnessError₂) :
    knowledgeSoundness init impl relIn' relOut' verifier srKnowledgeSoundnessError₂ := by
  obtain ⟨srExtractor, hSound⟩ := hSound
  refine ⟨srExtractor, fun srProver => ?_⟩
  refine le_trans ?_ (le_trans (hSound srProver) hle)
  exact probEvent_mono fun event _ hevent => by
    rcases event with ⟨stmtIn, witIn, stmtOut?, witOut⟩
    cases stmtOut? with
    | none => exact False.elim hevent
    | some stmtOut =>
        exact ⟨hOut hevent.1, fun hmem => hevent.2 (hIn hmem)⟩

#print axioms soundness.mono_error
#print axioms soundness.mono_languages
#print axioms soundness.mono_languages_error
#print axioms knowledgeSoundness.mono_error
#print axioms knowledgeSoundness.mono_relations
#print axioms knowledgeSoundness.mono_relations_error

end StateRestoration

end Verifier

namespace OracleVerifier



end OracleVerifier

end
