/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.AppendCompletenessMsgKeystone
import ArkLib.OracleReduction.Composition.Sequential.AppendRbrKnowledgePhase2ReconcileProof

/-!
# Discharges of the named `Append.lean` residuals via the proven keystones

Three of the named residual `Prop`s of `Append.lean` are exactly the conclusions of keystones
that have since been **proven unconditionally** (in their natural message-seam regimes), but no
declaration with the residual as its *result-type head* existed, so the residual census still
counted them open. This file supplies those providers — each is definitional from its keystone:

* `Reduction.reductionAppendCompletenessResidual` (error-bearing reduction-level append
  completeness) ← `Reduction.append_completeness_msg`
  (`AppendCompletenessMsgKeystone.lean`), message-seam + honest-`impl` side conditions
  (state-preserving / never-failing / value-blind).
* `OracleReduction.appendPerfectCompletenessResidual` (oracle-level append perfect completeness)
  ← `OracleReduction.append_perfectCompleteness_keystone` (`AppendToVerifierKeystone.lean`),
  message-seam + lossless `init` + support-faithful `impl`; the verifier-fusion bridge is already
  internal to the keystone.
* `Verifier.appendRbrKnowledgeSoundnessResidual` (round-by-round knowledge-soundness append)
  ← `Verifier.append_rbrKnowledgeSoundness_keystone_subsingleton_unconditional`
  (`AppendRbrKnowledgePhase2ReconcileProof.lean`), deterministic-`V₁` / `Subsingleton σ`
  (stateless) message-seam regime.

No `sorry`, no new axioms: each proof term is a direct application of the proven keystone.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped ENNReal NNReal

section ReductionDischarge

namespace Reduction

variable {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
  {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}

/-- **Discharge of the named residual `Reduction.reductionAppendCompletenessResidual`
(message-seam case).** The error-bearing append-completeness conclusion
`(R₁.append R₂).completeness … (e₁ + e₂)` — threaded as a hypothesis by
`Reduction.reduction_append_completeness` — is a *theorem* under the message-seam direction facts
and the standard honest-`impl` side conditions (state-preserving / never-failing / value-blind,
the same triple carried by the proven soundness keystone `append_soundness_msg`). Direct from the
keystone `Reduction.append_completeness_msg`. -/
theorem reductionAppendCompletenessResidual_msg
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    {completenessError₁ completenessError₂ : ℝ≥0}
    (h₁ : R₁.completeness init impl rel₁ rel₂ completenessError₁)
    (h₂ : R₂.completeness init impl rel₂ rel₃ completenessError₂)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    reductionAppendCompletenessResidual R₁ R₂ h₁ h₂ :=
  append_completeness_msg R₁ R₂ h₁ h₂ hn hDir hDir₂ himplSP himplNF himplVB

end Reduction

end ReductionDischarge

section VerifierDischarge

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}

/-- **Discharge of the named residual `Verifier.appendRbrKnowledgeSoundnessResidual`**
(deterministic-`V₁` / `Subsingleton σ` / prover-message-seam regime). The round-by-round
knowledge-soundness append conclusion — threaded as a hypothesis by
`Verifier.append_rbrKnowledgeSoundness` — is a *theorem* given the determinism witness for `V₁`
(`verify`/`hVerify`, which supplies the very seam-statement map the composite extractor and
knowledge state function thread), a reachable lossless `init`, nonempty intermediate types, and
the message-seam direction facts. Direct from the keystone
`append_rbrKnowledgeSoundness_keystone_subsingleton_unconditional`. -/
theorem appendRbrKnowledgeSoundnessResidual_msg_subsingleton [Subsingleton σ]
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {rbrKnowledgeError₁ : pSpec₁.ChallengeIdx → ℝ≥0}
    {rbrKnowledgeError₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩)
    (hInit : ∃ s, s ∈ support init) (hInitNF : Pr[⊥ | init] = 0)
    (hNE₂ : Nonempty Stmt₂) (hNEW₂ : Nonempty Wit₂)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    (h₁ : V₁.rbrKnowledgeSoundness init impl rel₁ rel₂ rbrKnowledgeError₁)
    (h₂ : V₂.rbrKnowledgeSoundness init impl rel₂ rel₃ rbrKnowledgeError₂) :
    appendRbrKnowledgeSoundnessResidual V₁ V₂ h₁ h₂ :=
  append_rbrKnowledgeSoundness_keystone_subsingleton_unconditional V₁ V₂ verify hVerify
    hInit hInitNF hNE₂ hNEW₂ hn hDir hDir₂ h₁ h₂

end Verifier

end VerifierDischarge

section OracleReductionDischarge

namespace OracleReduction

variable {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
  {Stmt₁ Stmt₂ Stmt₃ Wit₁ Wit₂ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [Oₘ₁ : ∀ i, OracleInterface (pSpec₁.Message i)] [Oₘ₂ : ∀ i, OracleInterface (pSpec₂.Message i)]
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {ιₛ₁ : Type} {OStmt₁ : ιₛ₁ → Type} [Oₛ₁ : ∀ i, OracleInterface (OStmt₁ i)]
  {ιₛ₂ : Type} {OStmt₂ : ιₛ₂ → Type} [Oₛ₂ : ∀ i, OracleInterface (OStmt₂ i)]
  {ιₛ₃ : Type} {OStmt₃ : ιₛ₃ → Type} [Oₛ₃ : ∀ i, OracleInterface (OStmt₃ i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {rel₁ : Set ((Stmt₁ × ∀ i, OStmt₁ i) × Wit₁)}
  {rel₂ : Set ((Stmt₂ × ∀ i, OStmt₂ i) × Wit₂)}
  {rel₃ : Set ((Stmt₃ × ∀ i, OStmt₃ i) × Wit₃)}

/-- **Discharge of the named residual `OracleReduction.appendPerfectCompletenessResidual`
(message-seam case).** The oracle-level append perfect-completeness conclusion — threaded as a
hypothesis by `OracleReduction.append_perfectCompleteness` — is a *theorem* under the
message-seam direction facts, a lossless `init`, and a support-faithful `impl`; the
verifier-fusion bridge `appendToReductionResidual` is discharged internally by the keystone.
Direct from `OracleReduction.append_perfectCompleteness_keystone`
(`AppendToVerifierKeystone.lean`). -/
theorem appendPerfectCompletenessResidual_msg
    (R₁ : OracleReduction oSpec Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂ pSpec₁)
    [OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) R₁.verifier]
    (R₂ : OracleReduction oSpec Stmt₂ OStmt₂ Wit₂ Stmt₃ OStmt₃ Wit₃ pSpec₂)
    (h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (h₂ : R₂.perfectCompleteness init impl rel₂ rel₃)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β))
    [(oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Fintype]
    [(oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Inhabited]
    [(oSpec + [pSpec₁.Challenge]ₒ).Fintype] [(oSpec + [pSpec₁.Challenge]ₒ).Inhabited]
    [(oSpec + [pSpec₂.Challenge]ₒ).Fintype] [(oSpec + [pSpec₂.Challenge]ₒ).Inhabited] :
    appendPerfectCompletenessResidual R₁ R₂ h₁ h₂ :=
  append_perfectCompleteness_keystone R₁ R₂ h₁ h₂ hn hDir hDir₂ hInit hImplSupp

end OracleReduction

end OracleReductionDischarge

-- Axiom audit: each discharge must be axiom-clean (no `sorryAx`).
#print axioms Reduction.reductionAppendCompletenessResidual_msg
#print axioms Verifier.appendRbrKnowledgeSoundnessResidual_msg_subsingleton
#print axioms OracleReduction.appendPerfectCompletenessResidual_msg
