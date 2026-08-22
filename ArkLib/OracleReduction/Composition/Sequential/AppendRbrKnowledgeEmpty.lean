/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.AppendRbrKnowledgeStateFunction

/-!
# Empty-seam rbr knowledge-soundness append keystone

For a 0-round right phase the phase-2 challenge indices are empty, so the unconditional keystone's
sole residual (`appendRbrKnowledgeSoundnessPhase2Residual`, quantified over `pSpec₂.ChallengeIdx`)
is vacuous. The empty-seam keystone is therefore residual-free.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec 0}
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- **Empty-seam rbr knowledge-soundness append keystone (residual-free).** Appending a 0-round
verifier preserves rbr knowledge soundness: the phase-2 residual of
`append_rbrKnowledgeSoundness_keystone_unconditional` quantifies over `pSpec₂.ChallengeIdx`,
which is empty for a 0-round phase. -/
theorem append_rbrKnowledgeSoundness_keystone_empty
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}
    {rbrKnowledgeError₁ : pSpec₁.ChallengeIdx → ℝ≥0}
    {rbrKnowledgeError₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩)
    (hInit : ∃ s, s ∈ support init)
    (hNE₂ : Nonempty Stmt₂) (hNEW₂ : Nonempty Wit₂)
    (h₁ : V₁.rbrKnowledgeSoundness init impl rel₁ rel₂ rbrKnowledgeError₁)
    (h₂ : V₂.rbrKnowledgeSoundness init impl rel₂ rel₃ rbrKnowledgeError₂) :
    (V₁.append V₂).rbrKnowledgeSoundness init impl rel₁ rel₃
      (Sum.elim rbrKnowledgeError₁ rbrKnowledgeError₂ ∘ ChallengeIdx.sumEquiv.symm) :=
  append_rbrKnowledgeSoundness_keystone_unconditional V₁ V₂ verify hVerify hInit hNE₂ hNEW₂ h₁ h₂
    (fun _kSF₁ _kSF₂ _stmtIn _witIn _prover i₂ => Fin.elim0 i₂.1)

end Verifier
