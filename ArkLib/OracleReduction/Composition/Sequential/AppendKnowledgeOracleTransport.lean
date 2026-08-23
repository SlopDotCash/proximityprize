/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.AppendToVerifierKeystone

/-!
# Oracle-level append knowledge soundness: transport from the plain layer

`OracleVerifier.knowledgeSoundness` is *defined* as knowledge soundness of the underlying
`toVerifier`, and the proven verifier-fusion keystone
`OracleReduction.oracleVerifier_append_toVerifier` identifies the `toVerifier` of an appended
oracle verifier with the plain append of the `toVerifier`s.  Hence the oracle-level named residual
`OracleVerifier.appendKnowledgeSoundnessResidual` (Append.lean) is *equivalent* to its plain-layer
counterpart `Verifier.appendKnowledgeSoundnessResidual` on `V₁.toVerifier` / `V₂.toVerifier`.

This file records that transport (`append_knowledgeSoundness_of_toVerifier`,
`appendKnowledgeSoundnessResidual_of_plain`): any discharge of the plain straightline-KS append
residual transfers verbatim to the oracle layer.  No new probabilistic content — the entire load
is carried by the proven fusion equation.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace OracleVerifier

variable {ι : Type} {oSpec : OracleSpec ι} {m n : ℕ}
    {Stmt₁ : Type} {ιₛ₁ : Type} {OStmt₁ : ιₛ₁ → Type} [Oₛ₁ : ∀ i, OracleInterface (OStmt₁ i)]
    {Wit₁ : Type}
    {Stmt₂ : Type} {ιₛ₂ : Type} {OStmt₂ : ιₛ₂ → Type} [Oₛ₂ : ∀ i, OracleInterface (OStmt₂ i)]
    {Wit₂ : Type}
    {Stmt₃ : Type} {ιₛ₃ : Type} {OStmt₃ : ιₛ₃ → Type} [Oₛ₃ : ∀ i, OracleInterface (OStmt₃ i)]
    {Wit₃ : Type}
    {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    [Oₘ₁ : ∀ i, OracleInterface (pSpec₁.Message i)]
    [Oₘ₂ : ∀ i, OracleInterface (pSpec₂.Message i)]
    [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel₁ : Set ((Stmt₁ × ∀ i, OStmt₁ i) × Wit₁)}
    {rel₂ : Set ((Stmt₂ × ∀ i, OStmt₂ i) × Wit₂)}
    {rel₃ : Set ((Stmt₃ × ∀ i, OStmt₃ i) × Wit₃)}

/-- **Oracle-level appended knowledge soundness from the plain layer.**  Knowledge soundness of an
appended oracle verifier *is* (definitionally + via the proven fusion
`oracleVerifier_append_toVerifier`) knowledge soundness of the plain append of the `toVerifier`s.
Any plain-layer append-KS theorem therefore transports to the oracle layer with no further work. -/
theorem append_knowledgeSoundness_of_toVerifier
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    [OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁]
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂)
    {knowledgeError : ℝ≥0}
    (hPlain : (Verifier.append V₁.toVerifier V₂.toVerifier).knowledgeSoundness
      init impl rel₁ rel₃ knowledgeError) :
    (OracleVerifier.append (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁ V₂).knowledgeSoundness
      init impl rel₁ rel₃ knowledgeError := by
  unfold OracleVerifier.knowledgeSoundness
  rw [OracleReduction.oracleVerifier_append_toVerifier]
  exact hPlain

/-- **The oracle-level append-KS named residual reduces to the plain-layer one.**  Discharges
`OracleVerifier.appendKnowledgeSoundnessResidual` from any discharge of
`Verifier.appendKnowledgeSoundnessResidual` on the `toVerifier`s (e.g. the message-seam /
deterministic-`V₁` discharge `Verifier.append_knowledgeSoundness_msg_residual`). -/
theorem appendKnowledgeSoundnessResidual_of_plain
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    [OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁]
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂)
    {knowledgeError₁ knowledgeError₂ : ℝ≥0}
    (h₁ : V₁.knowledgeSoundness init impl rel₁ rel₂ knowledgeError₁)
    (h₂ : V₂.knowledgeSoundness init impl rel₂ rel₃ knowledgeError₂)
    (hPlain : Verifier.appendKnowledgeSoundnessResidual (init := init) (impl := impl)
      (rel₁ := rel₁) (rel₂ := rel₂) (rel₃ := rel₃) V₁.toVerifier V₂.toVerifier h₁ h₂) :
    OracleVerifier.appendKnowledgeSoundnessResidual (init := init) (impl := impl)
      (rel₁ := rel₁) (rel₂ := rel₂) (rel₃ := rel₃) V₁ V₂ h₁ h₂ :=
  append_knowledgeSoundness_of_toVerifier V₁ V₂ hPlain

end OracleVerifier

-- Axiom audit: transport lemmas must be axiom-clean.
#print axioms OracleVerifier.append_knowledgeSoundness_of_toVerifier
#print axioms OracleVerifier.appendKnowledgeSoundnessResidual_of_plain
