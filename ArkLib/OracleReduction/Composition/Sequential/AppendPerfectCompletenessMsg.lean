/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.AppendPerfectCompletenessProof

/-!
# Message-seam perfect completeness compatibility

The three historical names below retain their original hypotheses and conclusions. Their common
completed construction is owned by `append_perfectCompleteness_msg_proof`; the duplicate support
proof and private machinery are archived in the integration audit. This module introduces no
residual or admitted construction. The retired aggregate response classes are explicit pointwise
finite/inhabited response families.
-/

open OracleComp OracleSpec ProtocolSpec

namespace Reduction

variable {ι : Type} {oSpec : OracleSpec ι} [∀ q, Fintype ((oSpec).Range q)] [∀ q, Inhabited ((oSpec).Range q)]
  {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}


/-- Historical message-seam spelling of the completed perfect-completeness theorem. -/
theorem append_perfectCompleteness_message
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (h₂ : R₂.perfectCompleteness init impl rel₂ rel₃)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    [∀ q, Fintype (((oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)).Range q)]
    [∀ q, Inhabited (((oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)).Range q)]
    [∀ q, Fintype (((oSpec + [pSpec₁.Challenge]ₒ)).Range q)] [∀ q, Inhabited (((oSpec + [pSpec₁.Challenge]ₒ)).Range q)]
    [∀ q, Fintype (((oSpec + [pSpec₂.Challenge]ₒ)).Range q)] [∀ q, Inhabited (((oSpec + [pSpec₂.Challenge]ₒ)).Range q)]
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) :
    (R₁.append R₂).perfectCompleteness init impl rel₁ rel₃ :=
  append_perfectCompleteness_msg_proof R₁ R₂ h₁ h₂ hn hDir hDir₂ hInit hImplSupp

/-- Historical message-seam spelling of the completed perfect-completeness theorem. -/
theorem reductionAppendPerfectCompletenessResidual_of_message
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (h₂ : R₂.perfectCompleteness init impl rel₂ rel₃)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    [∀ q, Fintype (((oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)).Range q)]
    [∀ q, Inhabited (((oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)).Range q)]
    [∀ q, Fintype (((oSpec + [pSpec₁.Challenge]ₒ)).Range q)] [∀ q, Inhabited (((oSpec + [pSpec₁.Challenge]ₒ)).Range q)]
    [∀ q, Fintype (((oSpec + [pSpec₂.Challenge]ₒ)).Range q)] [∀ q, Inhabited (((oSpec + [pSpec₂.Challenge]ₒ)).Range q)]
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) :
    reductionAppendPerfectCompletenessResidual R₁ R₂ h₁ h₂ :=
  append_perfectCompleteness_msg_proof R₁ R₂ h₁ h₂ hn hDir hDir₂ hInit hImplSupp

/-- Historical message-seam spelling of the completed perfect-completeness theorem. -/
theorem reduction_append_perfectCompleteness_msg
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (h₂ : R₂.perfectCompleteness init impl rel₂ rel₃)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    [∀ q, Fintype (((oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)).Range q)]
    [∀ q, Inhabited (((oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)).Range q)]
    [∀ q, Fintype (((oSpec + [pSpec₁.Challenge]ₒ)).Range q)] [∀ q, Inhabited (((oSpec + [pSpec₁.Challenge]ₒ)).Range q)]
    [∀ q, Fintype (((oSpec + [pSpec₂.Challenge]ₒ)).Range q)] [∀ q, Inhabited (((oSpec + [pSpec₂.Challenge]ₒ)).Range q)]
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) :
    (R₁.append R₂).perfectCompleteness init impl rel₁ rel₃ :=
  append_perfectCompleteness_msg_proof R₁ R₂ h₁ h₂ hn hDir hDir₂ hInit hImplSupp

end Reduction

#print axioms Reduction.append_perfectCompleteness_message
#print axioms Reduction.reductionAppendPerfectCompletenessResidual_of_message
#print axioms Reduction.reduction_append_perfectCompleteness_msg
