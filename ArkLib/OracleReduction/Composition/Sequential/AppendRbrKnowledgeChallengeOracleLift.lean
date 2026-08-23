/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.AppendRbrKnowledgeChallenge
import ArkLib.OracleReduction.Composition.Sequential.AppendRbrKnowledgeOracleLift

/-!
# OracleVerifier-level challenge-seam rbr knowledge-soundness append keystone (issue #114)

Lifts the Protocol-level challenge-seam keystone
`Verifier.append_rbrKnowledgeSoundness_keystone_subsingleton_challenge`
(`AppendRbrKnowledgeChallenge.lean`) to the `OracleVerifier` level, mirroring the message-seam
lift `OracleVerifier.append_rbrKnowledgeSoundness_subsingleton`
(`AppendRbrKnowledgeOracleLift.lean`): `OracleVerifier.rbrKnowledgeSoundness` is definitionally
`toVerifier`-level, and `OracleReduction.oracleVerifier_append_toVerifier` identifies the appended
oracle verifier's `toVerifier` with `Verifier.append` of the components' `toVerifier`s.

**Residual-free.** Both former named residuals of the challenge keystone are discharged
in-library: `hReconcile` (the phase-2 inner seam reconciliation) by
`appendRbrKnowledgePhase2SeamReconcile_proof_pos`, and `hSeamZero` (the per-round flip bound at
the seam challenge itself, `i₂ = 0`) by `appendRbrKnowledgeSeamZero_proven`
(`AppendRbrKnowledgeSeamZero.lean`). The former named `Prop`
`Verifier.appendRbrKnowledgeSeamZeroResidual` that fold-level assemblies used to thread per
challenge seam is deleted: no keystone requires it anymore.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace OracleVerifier

variable {ι : Type} {oSpec : OracleSpec ι}
    {Stmt₁ : Type} {ιₛ₁ : Type} {OStmt₁ : ιₛ₁ → Type}
    [Oₛ₁ : ∀ i, OracleInterface (OStmt₁ i)]
    {Wit₁ : Type}
    {Stmt₂ : Type} {ιₛ₂ : Type} {OStmt₂ : ιₛ₂ → Type}
    [Oₛ₂ : ∀ i, OracleInterface (OStmt₂ i)]
    {Wit₂ : Type}
    {Stmt₃ : Type} {ιₛ₃ : Type} {OStmt₃ : ιₛ₃ → Type}
    [Oₛ₃ : ∀ i, OracleInterface (OStmt₃ i)]
    {Wit₃ : Type}
    {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    [Oₘ₁ : ∀ i, OracleInterface (pSpec₁.Message i)]
    [Oₘ₂ : ∀ i, OracleInterface (pSpec₂.Message i)]
    [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel₁ : Set ((Stmt₁ × ∀ i, OStmt₁ i) × Wit₁)}
    {rel₂ : Set ((Stmt₂ × ∀ i, OStmt₂ i) × Wit₂)}
    {rel₃ : Set ((Stmt₃ × ∀ i, OStmt₃ i) × Wit₃)}

/-- **OracleVerifier-level challenge-seam rbr knowledge-soundness append keystone
(deterministic-`V₁`, `Subsingleton σ`) — RESIDUAL-FREE.** The `V_to_P`-seam companion of
`OracleVerifier.append_rbrKnowledgeSoundness_subsingleton`: discharges the appended oracle
verifier's rbr knowledge soundness from the per-phase bounds alone (the former `hReconcile` is
discharged by `appendRbrKnowledgePhase2SeamReconcile_proof_pos`, the former `hSeamZero` by
`appendRbrKnowledgeSeamZero_proven`), instantiated at the components' compiled (`toVerifier`)
forms. Proof: `OracleVerifier.rbrKnowledgeSoundness` is definitionally `toVerifier`-level;
rewrite the appended `toVerifier` via the proven `oracleVerifier_append_toVerifier` and apply the
Protocol-level challenge keystone. -/
theorem append_rbrKnowledgeSoundness_subsingleton_challenge [Subsingleton σ]
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    [OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁]
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂)
    {rbrKnowledgeError₁ : pSpec₁.ChallengeIdx → ℝ≥0}
    {rbrKnowledgeError₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (verify : (Stmt₁ × ∀ i, OStmt₁ i) → pSpec₁.FullTranscript → (Stmt₂ × ∀ i, OStmt₂ i))
    (hVerify : V₁.toVerifier = ⟨fun stmt tr => pure (verify stmt tr)⟩)
    (hInit : ∃ s, s ∈ support init) (hInitNF : Pr[⊥ | init] = 0)
    (hNE₂ : Nonempty (Stmt₂ × ∀ i, OStmt₂ i)) (hNEW₂ : Nonempty Wit₂)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .V_to_P)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .V_to_P)
    (h₁ : V₁.rbrKnowledgeSoundness init impl rel₁ rel₂ rbrKnowledgeError₁)
    (h₂ : V₂.rbrKnowledgeSoundness init impl rel₂ rel₃ rbrKnowledgeError₂) :
      (OracleVerifier.append (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁ V₂).rbrKnowledgeSoundness
        init impl rel₁ rel₃
        (Sum.elim rbrKnowledgeError₁ rbrKnowledgeError₂ ∘ ChallengeIdx.sumEquiv.symm) := by
  unfold OracleVerifier.rbrKnowledgeSoundness at h₁ h₂ ⊢
  rw [OracleReduction.oracleVerifier_append_toVerifier]
  exact Verifier.append_rbrKnowledgeSoundness_keystone_subsingleton_challenge
    V₁.toVerifier V₂.toVerifier verify hVerify hInit hInitNF hNE₂ hNEW₂ hn hDir hDir₂ h₁ h₂

end OracleVerifier

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms OracleVerifier.append_rbrKnowledgeSoundness_subsingleton_challenge
