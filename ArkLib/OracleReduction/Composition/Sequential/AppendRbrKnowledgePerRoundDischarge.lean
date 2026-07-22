/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.Composition.Sequential.AppendRbrKnowledgeStateFunction
import ArkLib.OracleReduction.Composition.Sequential.AppendRbrKnowledgePhase2ReconcileProof

/-!
# Discharge of `Verifier.appendRbrKnowledgeSoundnessPerRoundResidual` (issue #340)

The per-round bound residual of the unconditional rbr knowledge-soundness append keystone
(`AppendRbrKnowledgeStateFunction.lean:944`) is a **theorem** in the deterministic-`V₁` /
`Subsingleton σ` / prover-message-seam regime — the regime of every in-tree stateless consumer
(transparent-BCS, `oSpec = []ₒ` RingSwitching, the STIR/Spartan seam chains).

This is pure composition of three proven pieces, no new mathematics:
* `appendRbrKnowledgeSoundnessPerRound` — the per-round residual from `hBound₁` + the phase-2
  residual (the phase split, log-free reduction, and phase-1 seam analysis, all proven);
* `appendRbrKnowledgeSoundnessPhase2_subsingleton` — the phase-2 residual from `hBound₂` + the
  seam reconciliation (the Subsingleton bind split + amnesiac re-injection, proven);
* `appendRbrKnowledgePhase2SeamReconcile_proof` — the seam reconciliation itself
  (`AppendRbrKnowledgePhase2ReconcileProof.lean`, proven).

With this, every conditional provider chain of the residual bottoms out in proven theorems for
the consumer regime, completing the #340 disposition of the per-round item.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- **Discharge of `appendRbrKnowledgeSoundnessPerRoundResidual`** in the deterministic-`V₁` /
`Subsingleton σ` / prover-message-seam regime: the per-round appended knowledge flip bound holds
given the two destructured inner per-round bounds `hBound₁` / `hBound₂`, a lossless reachable
`init`, nonempty intermediate types, and the message-seam direction facts.  Composition of the
proven `appendRbrKnowledgeSoundnessPerRound`, `appendRbrKnowledgeSoundnessPhase2_subsingleton`,
and `appendRbrKnowledgePhase2SeamReconcile_proof`. -/
theorem appendRbrKnowledgeSoundnessPerRoundResidual_msg_subsingleton [Subsingleton σ]
    {WitMid₁ : Fin (m+1)→Type} {WitMid₂ : Fin (n+1)→Type}
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}
    {E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ WitMid₁}
    {E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ WitMid₂}
    (kSF₁ : V₁.KnowledgeStateFunction init impl rel₁ rel₂ E₁)
    (kSF₂ : V₂.KnowledgeStateFunction init impl rel₂ rel₃ E₂)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩)
    (hInit : ∃ s, s ∈ support init) (hInitNF : Pr[⊥ | init] = 0)
    (hNE₂ : Nonempty Stmt₂) (hNEW₂ : Nonempty Wit₂)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    {rbrKnowledgeError₁ : pSpec₁.ChallengeIdx → ℝ≥0}
    {rbrKnowledgeError₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (hBound₁ : ∀ stmtIn : Stmt₁, ∀ witIn : Wit₁,
      ∀ prover : Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁, ∀ i : pSpec₁.ChallengeIdx,
        Pr[fun ⟨transcript, challenge, _proveQueryLog⟩ =>
          ∃ witMid,
            ¬ kSF₁.toFun i.1.castSucc stmtIn transcript
              (E₁.extractMid i.1 stmtIn (transcript.concat challenge) witMid) ∧
              kSF₁.toFun i.1.succ stmtIn (transcript.concat challenge) witMid
        | do
          (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
            (do
              let ⟨⟨transcript, _⟩, proveQueryLog⟩ ←
                prover.runWithLogToRound i.1.castSucc stmtIn witIn
              let challenge ← liftComp (pSpec₁.getChallenge i) _
              return (transcript, challenge, proveQueryLog))).run' (← init)] ≤
          rbrKnowledgeError₁ i)
    (hBound₂ : ∀ stmtIn : Stmt₂, ∀ witIn : Wit₂,
      ∀ prover : Prover oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂, ∀ i : pSpec₂.ChallengeIdx,
        Pr[fun ⟨transcript, challenge, _proveQueryLog⟩ =>
          ∃ witMid,
            ¬ kSF₂.toFun i.1.castSucc stmtIn transcript
              (E₂.extractMid i.1 stmtIn (transcript.concat challenge) witMid) ∧
              kSF₂.toFun i.1.succ stmtIn (transcript.concat challenge) witMid
        | do
          (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
            (do
              let ⟨⟨transcript, _⟩, proveQueryLog⟩ ←
                prover.runWithLogToRound i.1.castSucc stmtIn witIn
              let challenge ← liftComp (pSpec₂.getChallenge i) _
              return (transcript, challenge, proveQueryLog))).run' (← init)] ≤
          rbrKnowledgeError₂ i) :
    appendRbrKnowledgeSoundnessPerRoundResidual (init := init) (impl := impl) V₁ V₂ kSF₁ kSF₂
      verify hVerify hInit (rbrKnowledgeError₁ := rbrKnowledgeError₁)
      (rbrKnowledgeError₂ := rbrKnowledgeError₂) :=
  appendRbrKnowledgeSoundnessPerRound V₁ V₂ kSF₁ kSF₂ verify hVerify hInit hNE₂ hNEW₂
    hBound₁
    (appendRbrKnowledgeSoundnessPhase2_subsingleton V₁ V₂ kSF₁ kSF₂ verify hVerify hInit
      hNEW₂ hInitNF hn hDir hDir₂ hBound₂
      (appendRbrKnowledgePhase2SeamReconcile_proof V₁ V₂ kSF₁ kSF₂ verify hVerify hInit
        (fun hn' => by exact hDir₂)))

end Verifier

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms Verifier.appendRbrKnowledgeSoundnessPerRoundResidual_msg_subsingleton
