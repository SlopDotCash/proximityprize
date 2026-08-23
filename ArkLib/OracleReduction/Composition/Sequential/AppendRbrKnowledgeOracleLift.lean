/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.AppendRbrKnowledgePhase2ReconcileProof
import ArkLib.OracleReduction.Composition.Sequential.AppendToVerifierKeystone

/-!
# OracleVerifier-level round-by-round knowledge-soundness append keystone (issue #29 / #13 / #114)

Lifts the fully-unconditional Protocol-level keystone
`Verifier.append_rbrKnowledgeSoundness_keystone_subsingleton_unconditional`
(`AppendRbrKnowledgePhase2ReconcileProof.lean`) to the `OracleVerifier` level — the form that
`RingSwitching.FullRingSwitching.fullOracleVerifier_rbrKnowledgeSoundness` consumes.

The lift is definitional plumbing, not new probability: `OracleVerifier.rbrKnowledgeSoundness`
*is* `toVerifier`-level (`Security/RoundByRound.lean`), and the proven
`OracleReduction.oracleVerifier_append_toVerifier` identifies the appended oracle verifier's
`toVerifier` with the `Verifier.append` of the components' `toVerifier`s. Composing the two
discharges the `OracleVerifier.appendRbrKnowledgeSoundnessResidual` of `Append.lean` for the
deterministic-`V₁`, message-seam, `Subsingleton σ` (stateless) regime — which is exactly the
RingSwitching (`oSpec = []ₒ`) and transparent-BCS instantiation.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped ENNReal NNReal

universe u

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

/-- **OracleVerifier-level rbr knowledge-soundness append keystone (unconditional, deterministic-`V₁`
message-seam `Subsingleton σ` regime).** Discharges `OracleVerifier.appendRbrKnowledgeSoundnessResidual`
(`Append.lean`) — no residual hypothesis — given:
* the determinism witness for `V₁`'s compiled (`toVerifier`) form (`verify`/`hVerify`; supplied for the
  RingSwitching batching/core verifiers by their `verify_collapse` lemmas),
* a reachable, lossless `init` over a `Subsingleton` simulation state (the stateless regime; e.g.
  `σ = Unit`, `init = pure ()`, which is how the `oSpec = []ₒ` RingSwitching instantiations run),
* the message-seam direction facts, and
* the two per-phase rbr knowledge-soundness bounds.

Proof: `OracleVerifier.rbrKnowledgeSoundness` is definitionally `toVerifier`-level; rewrite the appended
`toVerifier` via the proven `oracleVerifier_append_toVerifier` and apply the unconditional Protocol-level
keystone. -/
theorem append_rbrKnowledgeSoundness_subsingleton [Subsingleton σ]
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
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    (h₁ : V₁.rbrKnowledgeSoundness init impl rel₁ rel₂ rbrKnowledgeError₁)
    (h₂ : V₂.rbrKnowledgeSoundness init impl rel₂ rel₃ rbrKnowledgeError₂) :
      (OracleVerifier.append (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁ V₂).rbrKnowledgeSoundness
        init impl rel₁ rel₃
        (Sum.elim rbrKnowledgeError₁ rbrKnowledgeError₂ ∘ ChallengeIdx.sumEquiv.symm) := by
  unfold OracleVerifier.rbrKnowledgeSoundness at h₁ h₂ ⊢
  rw [OracleReduction.oracleVerifier_append_toVerifier]
  exact Verifier.append_rbrKnowledgeSoundness_keystone_subsingleton_unconditional
    V₁.toVerifier V₂.toVerifier verify hVerify hInit hInitNF hNE₂ hNEW₂ hn hDir hDir₂ h₁ h₂

/-- **Discharge of the named residual `OracleVerifier.appendRbrKnowledgeSoundnessResidual`**
(`Append.lean`) in the deterministic-`V₁` / `Subsingleton σ` / prover-message-seam regime. The
residual's conclusion is precisely the keystone's, so this is definitional from
`append_rbrKnowledgeSoundness_subsingleton`. With this,
`OracleVerifier.append_rbrKnowledgeSoundness` no longer needs an unproved hypothesis in the
stateless regime. -/
theorem appendRbrKnowledgeSoundnessResidual_msg_subsingleton [Subsingleton σ]
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
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    (h₁ : V₁.rbrKnowledgeSoundness init impl rel₁ rel₂ rbrKnowledgeError₁)
    (h₂ : V₂.rbrKnowledgeSoundness init impl rel₂ rel₃ rbrKnowledgeError₂) :
    appendRbrKnowledgeSoundnessResidual (init := init) (impl := impl) V₁ V₂ h₁ h₂ :=
  append_rbrKnowledgeSoundness_subsingleton V₁ V₂ verify hVerify hInit hInitNF hNE₂ hNEW₂
    hn hDir hDir₂ h₁ h₂

/-- **Generic determinism witness from a `simulateQ` collapse.** If an oracle verifier's `verify`,
simulated against the transcript-message oracle, collapses to `pure (v (stmt, oStmt) tr)` for every
input (the shape of the RingSwitching `*_verify_collapse` lemmas), then its compiled `toVerifier` is
literally the pure verifier on `v` paired with the deterministic `oStmtOut` routing — the exact
`hVerify` input of the rbr (knowledge) soundness append keystones. -/
theorem toVerifier_eq_pure_of_collapse
    {ιₛᵢ ιₛₒ : Type} {StmtIn StmtOut : Type}
    {OStmtIn : ιₛᵢ → Type} [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
    {OStmtOut : ιₛₒ → Type}
    {n' : ℕ} {pSpec : ProtocolSpec n'} [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]
    (V : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec)
    (v : (StmtIn × ∀ i, OStmtIn i) → pSpec.FullTranscript → StmtOut)
    (hcollapse : ∀ (stmt : StmtIn) (oStmt : ∀ i, OStmtIn i) (tr : pSpec.FullTranscript),
      simulateQ (OracleInterface.simOracle2 oSpec oStmt tr.messages)
          (V.verify stmt tr.challenges)
        = (pure (v (stmt, oStmt) tr) : OptionT (OracleComp oSpec) StmtOut)) :
    V.toVerifier = ⟨fun p tr => pure (v p tr,
      fun i => match h : V.embed i with
        | Sum.inl j => (V.hEq i ▸ h ▸ p.2 j : OStmtOut i)
        | Sum.inr j => (V.hEq i ▸ h ▸ tr.messages j : OStmtOut i))⟩ := by
  unfold OracleVerifier.toVerifier
  congr 1
  funext p tr
  obtain ⟨stmt, oStmt⟩ := p
  simp only [hcollapse stmt oStmt tr, pure_bind]
  rfl

end OracleVerifier

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Stmt₂ Stmt₃ : Type}
    {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

/-- **Pure verifiers compose to a pure verifier.** The `Verifier.append` of two deterministic-total
(`pure`) verifiers is itself deterministic-total, with the composed `verify` function feeding `v₁`'s
output on the transcript's first half into `v₂` on the second half. This is the determinism-witness
combinator: it builds the `hVerify` input of the rbr (knowledge) soundness append keystones for
*composite* left verifiers (e.g. RingSwitching's `batchingCore = batching ++ coreInteraction`) from
the components' witnesses. -/
theorem append_pure_pure
    (v₁ : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (v₂ : Stmt₂ → pSpec₂.FullTranscript → Stmt₃) :
    Verifier.append (oSpec := oSpec) ⟨fun stmt tr => pure (v₁ stmt tr)⟩
        ⟨fun stmt tr => pure (v₂ stmt tr)⟩
      = ⟨fun stmt tr => pure (v₂ (v₁ stmt tr.fst) tr.snd)⟩ := by
  unfold Verifier.append
  congr 1

end Verifier

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms OracleVerifier.append_rbrKnowledgeSoundness_subsingleton
#print axioms OracleVerifier.appendRbrKnowledgeSoundnessResidual_msg_subsingleton
#print axioms Verifier.append_pure_pure
#print axioms OracleVerifier.toVerifier_eq_pure_of_collapse
