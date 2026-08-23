/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.AppendToVerifierKeystone
import ArkLib.OracleReduction.Composition.Sequential.AppendPerfectCompletenessEmpty

/-!
# Oracle-level append perfect completeness at an empty trailing seam (#114)

The `pSpec₂ : ProtocolSpec 0` analogue of `OracleReduction.append_perfectCompleteness_keystone`
(message seam, `AppendToVerifierKeystone.lean`) and
`OracleReduction.append_perfectCompleteness_challenge_keystone` (challenge seam,
`AppendChallengeKeystoneOracle.lean`): perfect completeness of `R₁.append R₂` for **oracle**
reductions whose trailing protocol is empty (a zero-round adapter/check phase).

This is the third and final seam case the right-associated Spartan composed-PC fold (#114) needs:
its innermost append is `secondSumcheck ▷ finalCheck` where `finalCheck` is a `ProtocolSpec 0`
`CheckClaim` phase, so neither the message-seam nor the challenge-seam keystone applies (both
require `0 < n`). The verifier-fusion residual is seam-agnostic and already discharged
(`appendToReductionResidual_proof`); the probabilistic content is the unconditional
`Reduction.append_perfectCompleteness_empty_proof`. No seam-direction hypotheses are needed.
-/

open OracleComp OracleSpec ProtocolSpec

namespace OracleReduction

variable {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
    {m : ℕ}
    {Stmt₁ : Type} {ιₛ₁ : Type} {OStmt₁ : ιₛ₁ → Type}
    [Oₛ₁ : ∀ i, OracleInterface (OStmt₁ i)]
    {Wit₁ : Type}
    {Stmt₂ : Type} {ιₛ₂ : Type} {OStmt₂ : ιₛ₂ → Type}
    [Oₛ₂ : ∀ i, OracleInterface (OStmt₂ i)]
    {Wit₂ : Type}
    {Stmt₃ : Type} {ιₛ₃ : Type} {OStmt₃ : ιₛ₃ → Type}
    [Oₛ₃ : ∀ i, OracleInterface (OStmt₃ i)]
    {Wit₃ : Type}
    {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec 0}
    [Oₘ₁ : ∀ i, OracleInterface ((pSpec₁.Message i))]
    [Oₘ₂ : ∀ i, OracleInterface ((pSpec₂.Message i))]
    [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel₁ : Set ((Stmt₁ × ∀ i, OStmt₁ i) × Wit₁)}
    {rel₂ : Set ((Stmt₂ × ∀ i, OStmt₂ i) × Wit₂)}
    {rel₃ : Set ((Stmt₃ × ∀ i, OStmt₃ i) × Wit₃)}

/-- **Oracle-level append perfect completeness — UNCONDITIONAL (empty trailing seam).** Perfect
completeness of `R₁.append R₂` for oracle reductions with an empty trailing protocol
(`pSpec₂ : ProtocolSpec 0`), from the two component perfect-completenesses and the
`NeverFail`/support-faithfulness side conditions. No seam-direction hypotheses: the trailing block
has no rounds. The verifier-fusion residual is discharged internally by the seam-agnostic
`appendToReductionResidual_proof`; the probabilistic content is the `Reduction`-level
`Reduction.append_perfectCompleteness_empty_proof`. This is the empty-tail case of the #114
composed fold (`secondSumcheck ▷ finalCheck`). -/
theorem append_perfectCompleteness_empty_keystone
    (R₁ : OracleReduction oSpec Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂ pSpec₁)
    [OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) R₁.verifier]
    (R₂ : OracleReduction oSpec Stmt₂ OStmt₂ Wit₂ Stmt₃ OStmt₃ Wit₃ pSpec₂)
    (h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (h₂ : R₂.perfectCompleteness init impl rel₂ rel₃)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β))
    [(oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Fintype]
    [(oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Inhabited]
    [(oSpec + [pSpec₁.Challenge]ₒ).Fintype] [(oSpec + [pSpec₁.Challenge]ₒ).Inhabited]
    [(oSpec + [pSpec₂.Challenge]ₒ).Fintype] [(oSpec + [pSpec₂.Challenge]ₒ).Inhabited] :
    (R₁.append R₂).perfectCompleteness init impl rel₁ rel₃ := by
  change Reduction.perfectCompleteness init impl rel₁ rel₃ (R₁.append R₂).toReduction
  rw [show (R₁.append R₂).toReduction = R₁.toReduction.append R₂.toReduction from
    appendToReductionResidual_proof R₁ R₂]
  exact Reduction.append_perfectCompleteness_empty_proof R₁.toReduction R₂.toReduction
    h₁ h₂ hInit hImplSupp

end OracleReduction

#print axioms OracleReduction.append_perfectCompleteness_empty_keystone
