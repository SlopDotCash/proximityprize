/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.AppendRbrKnowledgePhase2ReconcileProof
import ArkLib.OracleReduction.Composition.Sequential.AppendRbrSoundnessPhase2Proof
import ArkLib.OracleReduction.StateCollapse

/-!
# Append rbr knowledge soundness for arbitrary state, via the state collapse

`append_rbrKnowledgeSoundness_keystone_subsingleton_unconditional` proves the
round-by-round knowledge-soundness append keystone under `[Subsingleton σ]`. This file removes
that hypothesis at **point-mass initial state**: for any state type `σ`, any state-preserving
implementation, and any pinned initial state `s₀`, the keystone holds verbatim
(`append_rbrKnowledgeSoundness_keystone_collapse`).

The proof is pure transfer: `rbrKnowledgeSoundness_collapseState_iff` moves both component
hypotheses and the appended conclusion to the `Unit`-state collapsed implementation
(distribution-faithful by `evalDist_simulateQ_run'_collapseState`), where `Unit` is a
subsingleton and the landed keystone applies.

Axiom-clean: `[propext, Classical.choice, Quot.sound]` (see `#print axioms` at EOF).
-/

open OracleComp OracleSpec ProtocolSpec StateCollapse
open scoped NNReal ENNReal

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type}

/-- **Round-by-round knowledge soundness append keystone, arbitrary state, point-mass
initialization.** The `[Subsingleton σ]` hypothesis of the landed keystone is removed by
collapsing the state: both component soundness hypotheses transfer to the `Unit`-state
implementation `collapseState impl s₀`, the subsingleton keystone applies there, and the
appended conclusion transfers back. The only new hypothesis is state preservation of the
implementation (`hso`), which already underlies the seam toolkit. -/
theorem append_rbrKnowledgeSoundness_keystone_collapse
    {impl : QueryImpl oSpec (StateT σ ProbComp)} {s₀ : σ}
    (hso : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}
    {rbrKnowledgeError₁ : pSpec₁.ChallengeIdx → ℝ≥0}
    {rbrKnowledgeError₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩)
    (hNE₂ : Nonempty Stmt₂) (hNEW₂ : Nonempty Wit₂)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    (h₁ : V₁.rbrKnowledgeSoundness (pure s₀) impl rel₁ rel₂ rbrKnowledgeError₁)
    (h₂ : V₂.rbrKnowledgeSoundness (pure s₀) impl rel₂ rel₃ rbrKnowledgeError₂) :
      (V₁.append V₂).rbrKnowledgeSoundness (pure s₀) impl rel₁ rel₃
        (Sum.elim rbrKnowledgeError₁ rbrKnowledgeError₂ ∘ ChallengeIdx.sumEquiv.symm) := by
  rw [rbrKnowledgeSoundness_collapseState_iff _ _ _ _ _ _ hso] at h₁ h₂ ⊢
  exact append_rbrKnowledgeSoundness_keystone_subsingleton_unconditional
    (init := pure ()) (impl := collapseState impl s₀)
    V₁ V₂ verify hVerify ⟨(), by simp⟩ (by simp) hNE₂ hNEW₂ hn hDir hDir₂ h₁ h₂

/-- **The named append rbr-knowledge-soundness residual is a theorem** (message seam,
deterministic first verifier, point-mass initialization, **arbitrary state type**): the exact
`Prop` `Verifier.appendRbrKnowledgeSoundnessResidual V₁ V₂ h₁ h₂` from `Append.lean`,
discharged by the collapse keystone. Strictly more general than a `[Subsingleton σ]`
instantiation. -/
theorem appendRbrKnowledgeSoundnessResidual_of_message_collapse
    {impl : QueryImpl oSpec (StateT σ ProbComp)} {s₀ : σ}
    (hso : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}
    {rbrKnowledgeError₁ : pSpec₁.ChallengeIdx → ℝ≥0}
    {rbrKnowledgeError₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩)
    (hNE₂ : Nonempty Stmt₂) (hNEW₂ : Nonempty Wit₂)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    (h₁ : V₁.rbrKnowledgeSoundness (pure s₀) impl rel₁ rel₂ rbrKnowledgeError₁)
    (h₂ : V₂.rbrKnowledgeSoundness (pure s₀) impl rel₂ rel₃ rbrKnowledgeError₂) :
    appendRbrKnowledgeSoundnessResidual V₁ V₂ h₁ h₂ :=
  append_rbrKnowledgeSoundness_keystone_collapse hso V₁ V₂ verify hVerify hNE₂ hNEW₂
    hn hDir hDir₂ h₁ h₂

/-- **Round-by-round (plain) soundness append keystone, arbitrary state, point-mass
initialization.** The `[Subsingleton σ]` hypothesis of
`append_rbrSoundness_keystone_subsingleton_unconditional` is removed by the state collapse. -/
theorem append_rbrSoundness_keystone_collapse
    {impl : QueryImpl oSpec (StateT σ ProbComp)} {s₀ : σ}
    (hso : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {lang₁ : Set Stmt₁} {lang₂ : Set Stmt₂} {lang₃ : Set Stmt₃}
    {rbrSoundnessError₁ : pSpec₁.ChallengeIdx → ℝ≥0}
    {rbrSoundnessError₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩)
    (hNE : Nonempty Stmt₂)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    (h₁ : V₁.rbrSoundness (pure s₀) impl lang₁ lang₂ rbrSoundnessError₁)
    (h₂ : V₂.rbrSoundness (pure s₀) impl lang₂ lang₃ rbrSoundnessError₂) :
      (V₁.append V₂).rbrSoundness (pure s₀) impl lang₁ lang₃
        (Sum.elim rbrSoundnessError₁ rbrSoundnessError₂ ∘ ChallengeIdx.sumEquiv.symm) := by
  rw [rbrSoundness_collapseState_iff _ _ _ _ _ _ hso] at h₁ h₂ ⊢
  exact append_rbrSoundness_keystone_subsingleton_unconditional
    (init := pure ()) (impl := collapseState impl s₀)
    V₁ V₂ verify hVerify ⟨(), by simp⟩ (by simp) hNE hn hDir hDir₂ h₁ h₂

/-- **The named append rbr-soundness residual is a theorem** (message seam, deterministic first
verifier, point-mass initialization, **arbitrary state type**). -/
theorem appendRbrSoundnessResidual_of_message_collapse
    {impl : QueryImpl oSpec (StateT σ ProbComp)} {s₀ : σ}
    (hso : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {lang₁ : Set Stmt₁} {lang₂ : Set Stmt₂} {lang₃ : Set Stmt₃}
    {rbrSoundnessError₁ : pSpec₁.ChallengeIdx → ℝ≥0}
    {rbrSoundnessError₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩)
    (hNE : Nonempty Stmt₂)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    (h₁ : V₁.rbrSoundness (pure s₀) impl lang₁ lang₂ rbrSoundnessError₁)
    (h₂ : V₂.rbrSoundness (pure s₀) impl lang₂ lang₃ rbrSoundnessError₂) :
    appendRbrSoundnessResidual (init := pure s₀) (impl := impl) V₁ V₂ h₁ h₂ :=
  append_rbrSoundness_keystone_collapse hso V₁ V₂ verify hVerify hNE hn hDir hDir₂ h₁ h₂

end Verifier

/-! ## Axiom audit — kernel-clean. -/
#print axioms Verifier.append_rbrKnowledgeSoundness_keystone_collapse
#print axioms Verifier.appendRbrKnowledgeSoundnessResidual_of_message_collapse
#print axioms Verifier.append_rbrSoundness_keystone_collapse
#print axioms Verifier.appendRbrSoundnessResidual_of_message_collapse
