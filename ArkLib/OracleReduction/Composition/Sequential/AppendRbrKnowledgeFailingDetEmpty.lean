/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.AppendRbrKnowledgeFailingDet
import ArkLib.OracleReduction.Composition.Sequential.AppendRbrKnowledgeEmpty

/-!
# Failing-deterministic empty-seam rbr knowledge-soundness append keystone

Combines the **optionization reduction** (`AppendRbrKnowledgeFailingDet.lean`) with the
**residual-free empty-seam keystone** (`AppendRbrKnowledgeEmpty.lean`): appending a
*failing*-deterministic left verifier (`⟨fun s tr => OptionT.mk (pure (verify? s tr))⟩`) to a
0-round right phase is round-by-round knowledge sound with the additive `Sum.elim` error,
with **no** `Subsingleton σ`, **no** lossless-`init` (`hInitNF`), and **no** seam-direction
hypotheses: the phase-2 residual quantifies over the (empty) `pSpec₂.ChallengeIdx`, so it is
vacuous, and the optionization transports are state-regime-free.

Proof shape (mirroring `Verifier.append_rbrKnowledgeSoundness_failingDet_subsingleton`): rewrite
the failing-det seam into the total-det seam over `Option Stmt₂` via
`append_failingDet_eq_optionized` (where the determinism witness is `rfl` and
`Nonempty (Option Stmt₂)` is free via `none`), transport the per-phase bounds by
`failingDet_optionized_rbrKnowledgeSoundness` / `optionLift_rbrKnowledgeSoundness`, and apply
`append_rbrKnowledgeSoundness_keystone_empty`. The `OracleVerifier` lift is the standard 3-line
`oracleVerifier_append_toVerifier` plumbing.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped ENNReal NNReal

universe u

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
    {m : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec 0}
    [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- **Failing-deterministic empty-seam rbr knowledge-soundness append keystone
(residual-free).** Appending a *failing*-deterministic left verifier to a 0-round right phase is
round-by-round knowledge sound with the additive `Sum.elim` error — no `Subsingleton σ`, no
lossless-`init`, and no seam-direction hypotheses: the empty keystone's phase-2 residual is
vacuous (no phase-2 challenges) and the optionization transports are state-regime-free.

Proof: rewrite the seam by `append_failingDet_eq_optionized` into the total-deterministic seam
over `Option Stmt₂` (where the determinism witness is `rfl` and `Nonempty (Option Stmt₂)` is free
via `none`), transport `h₁`/`h₂` by `failingDet_optionized_rbrKnowledgeSoundness` /
`optionLift_rbrKnowledgeSoundness`, and apply the residual-free empty keystone. -/
theorem append_rbrKnowledgeSoundness_failingDet_empty
    [Inhabited Stmt₂]
    (verify? : Stmt₁ → pSpec₁.FullTranscript → Option Stmt₂)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}
    {err₁ : pSpec₁.ChallengeIdx → ℝ≥0} {err₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (hInit : ∃ s, s ∈ support init)
    (hNEW₂ : Nonempty Wit₂)
    (h₁ : Verifier.rbrKnowledgeSoundness init impl rel₁ rel₂
      (⟨fun s tr => OptionT.mk (pure (verify? s tr))⟩ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) err₁)
    (h₂ : V₂.rbrKnowledgeSoundness init impl rel₂ rel₃ err₂) :
    (Verifier.append
        (⟨fun s tr => OptionT.mk (pure (verify? s tr))⟩ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
        V₂).rbrKnowledgeSoundness init impl rel₁ rel₃
      (Sum.elim err₁ err₂ ∘ ChallengeIdx.sumEquiv.symm) := by
  rw [append_failingDet_eq_optionized]
  exact append_rbrKnowledgeSoundness_keystone_empty
    (⟨fun s tr => pure (verify? s tr)⟩ : Verifier oSpec Stmt₁ (Option Stmt₂) pSpec₁)
    V₂.optionLift verify? rfl hInit ⟨none⟩ hNEW₂
    (failingDet_optionized_rbrKnowledgeSoundness verify? h₁)
    (optionLift_rbrKnowledgeSoundness V₂ h₂)

end Verifier

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
    {m : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec 0}
    [Oₘ₁ : ∀ i, OracleInterface (pSpec₁.Message i)]
    [Oₘ₂ : ∀ i, OracleInterface (pSpec₂.Message i)]
    [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel₁ : Set ((Stmt₁ × ∀ i, OStmt₁ i) × Wit₁)}
    {rel₂ : Set ((Stmt₂ × ∀ i, OStmt₂ i) × Wit₂)}
    {rel₃ : Set ((Stmt₃ × ∀ i, OStmt₃ i) × Wit₃)}

/-- **OracleVerifier-level failing-deterministic empty-seam rbr knowledge-soundness append
keystone (residual-free).** The OracleVerifier companion of
`Verifier.append_rbrKnowledgeSoundness_failingDet_empty`: discharges the
`OracleVerifier.appendRbrKnowledgeSoundnessResidual` for seams whose left verifier compiles to a
*failing*-deterministic `toVerifier` and whose right phase is 0-round — with no `Subsingleton σ`,
no lossless-`init`, and no seam-direction hypotheses. One-shot from
`oracleVerifier_append_toVerifier` + the Protocol-level failing-det empty capstone. -/
theorem append_rbrKnowledgeSoundness_failingDet_empty
    [Inhabited (Stmt₂ × ∀ i, OStmt₂ i)]
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    [OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁]
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂)
    {rbrKnowledgeError₁ : pSpec₁.ChallengeIdx → ℝ≥0}
    {rbrKnowledgeError₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (verify? : (Stmt₁ × ∀ i, OStmt₁ i) → pSpec₁.FullTranscript →
      Option (Stmt₂ × ∀ i, OStmt₂ i))
    (hVerify : V₁.toVerifier = ⟨fun p tr => OptionT.mk (pure (verify? p tr))⟩)
    (hInit : ∃ s, s ∈ support init)
    (hNEW₂ : Nonempty Wit₂)
    (h₁ : V₁.rbrKnowledgeSoundness init impl rel₁ rel₂ rbrKnowledgeError₁)
    (h₂ : V₂.rbrKnowledgeSoundness init impl rel₂ rel₃ rbrKnowledgeError₂) :
      (OracleVerifier.append (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁ V₂).rbrKnowledgeSoundness
        init impl rel₁ rel₃
        (Sum.elim rbrKnowledgeError₁ rbrKnowledgeError₂ ∘ ChallengeIdx.sumEquiv.symm) := by
  unfold OracleVerifier.rbrKnowledgeSoundness at h₁ h₂ ⊢
  rw [OracleReduction.oracleVerifier_append_toVerifier, hVerify]
  rw [hVerify] at h₁
  exact Verifier.append_rbrKnowledgeSoundness_failingDet_empty verify? V₂.toVerifier
    hInit hNEW₂ h₁ h₂

end OracleVerifier

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms Verifier.append_rbrKnowledgeSoundness_failingDet_empty
#print axioms OracleVerifier.append_rbrKnowledgeSoundness_failingDet_empty
