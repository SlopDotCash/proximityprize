/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.AppendRbrSoundnessPhase2Proof
import ArkLib.OracleReduction.Composition.Sequential.AppendToVerifierKeystone

/-!
# OracleVerifier-level round-by-round soundness append keystone (issues #29 / #13 / #114 / #62)

Lifts the unconditional Protocol-level rbr-soundness keystone
`Verifier.append_rbrSoundness_keystone_subsingleton_unconditional`
(`AppendRbrSoundnessPhase2Proof.lean`) to the `OracleVerifier` level — the exact shape of the
named residual `OracleVerifier.appendRbrSoundnessResidual` (`Append.lean`) consumed by the FRI
top-seam assembly (`Fri/Spec/Soundness.lean`) and the STIR multi-round chain.

This is the plain-soundness analogue of `AppendRbrKnowledgeOracleLift.lean`: the lift is
definitional plumbing, not new probability. `OracleVerifier.rbrSoundness` *is* `toVerifier`-level
(`Security/RoundByRound.lean`), and the proven
`OracleReduction.oracleVerifier_append_toVerifier` identifies the appended oracle verifier's
`toVerifier` with the `Verifier.append` of the components' `toVerifier`s. Composing the two
discharges `OracleVerifier.appendRbrSoundnessResidual` in the deterministic-`V₁`, message-seam,
`Subsingleton σ` (stateless) regime — the regime of the in-tree `oSpec = []ₒ` consumers
(FRI / transparent-BCS / RingSwitching instantiations).
-/

open OracleComp OracleSpec ProtocolSpec
open scoped ENNReal NNReal

universe u

namespace OracleVerifier

variable {ι : Type} {oSpec : OracleSpec ι}
    {Stmt₁ : Type} {ιₛ₁ : Type} {OStmt₁ : ιₛ₁ → Type}
    [Oₛ₁ : ∀ i, OracleInterface (OStmt₁ i)]
    {Stmt₂ : Type} {ιₛ₂ : Type} {OStmt₂ : ιₛ₂ → Type}
    [Oₛ₂ : ∀ i, OracleInterface (OStmt₂ i)]
    {Stmt₃ : Type} {ιₛ₃ : Type} {OStmt₃ : ιₛ₃ → Type}
    [Oₛ₃ : ∀ i, OracleInterface (OStmt₃ i)]
    {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    [Oₘ₁ : ∀ i, OracleInterface (pSpec₁.Message i)]
    [Oₘ₂ : ∀ i, OracleInterface (pSpec₂.Message i)]
    [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {lang₁ : Set (Stmt₁ × (∀ i, OStmt₁ i))}
    {lang₂ : Set (Stmt₂ × (∀ i, OStmt₂ i))}
    {lang₃ : Set (Stmt₃ × (∀ i, OStmt₃ i))}

/-- **OracleVerifier-level rbr soundness append keystone (unconditional, deterministic-`V₁`
message-seam `Subsingleton σ` regime).** The appended oracle verifier is round-by-round sound with
the `Sum.elim`-routed per-round error, from the two components' `rbrSoundness` alone, given:
* the determinism witness for `V₁`'s compiled (`toVerifier`) form (`verify`/`hVerify`; available
  from a `simulateQ` collapse via `OracleVerifier.toVerifier_eq_pure_of_collapse`),
* a reachable, lossless `init` over a `Subsingleton` simulation state (the stateless regime; e.g.
  `σ = Unit`, `init = pure ()`, which is how the `oSpec = []ₒ` consumers run), and
* the message-seam direction facts.

Proof: `OracleVerifier.rbrSoundness` is definitionally `toVerifier`-level; rewrite the appended
`toVerifier` via the proven `oracleVerifier_append_toVerifier` and apply the unconditional
Protocol-level keystone. -/
theorem append_rbrSoundness_subsingleton [Subsingleton σ]
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    [OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁]
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂)
    {rbrSoundnessError₁ : pSpec₁.ChallengeIdx → ℝ≥0}
    {rbrSoundnessError₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (verify : (Stmt₁ × ∀ i, OStmt₁ i) → pSpec₁.FullTranscript → (Stmt₂ × ∀ i, OStmt₂ i))
    (hVerify : V₁.toVerifier = ⟨fun stmt tr => pure (verify stmt tr)⟩)
    (hInit : ∃ s, s ∈ support init) (hInitNF : Pr[⊥ | init] = 0)
    (hNE₂ : Nonempty (Stmt₂ × ∀ i, OStmt₂ i))
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    (h₁ : V₁.rbrSoundness init impl lang₁ lang₂ rbrSoundnessError₁)
    (h₂ : V₂.rbrSoundness init impl lang₂ lang₃ rbrSoundnessError₂) :
      (OracleVerifier.append (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁ V₂).rbrSoundness
        init impl lang₁ lang₃
        (Sum.elim rbrSoundnessError₁ rbrSoundnessError₂ ∘ ChallengeIdx.sumEquiv.symm) := by
  unfold OracleVerifier.rbrSoundness at h₁ h₂ ⊢
  rw [OracleReduction.oracleVerifier_append_toVerifier]
  exact Verifier.append_rbrSoundness_keystone_subsingleton_unconditional
    V₁.toVerifier V₂.toVerifier verify hVerify hInit hInitNF hNE₂ hn hDir hDir₂ h₁ h₂

/-- **Discharge of the named residual `OracleVerifier.appendRbrSoundnessResidual`**
(`Append.lean`) in the deterministic-`V₁` / `Subsingleton σ` / prover-message-seam regime. The
residual's conclusion is precisely the keystone's, so this is definitional from
`append_rbrSoundness_subsingleton`. With this, `OracleVerifier.append_rbrSoundness` no longer
needs an unproved hypothesis in the stateless regime. -/
theorem appendRbrSoundnessResidual_msg_subsingleton [Subsingleton σ]
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    [OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁]
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂)
    {rbrSoundnessError₁ : pSpec₁.ChallengeIdx → ℝ≥0}
    {rbrSoundnessError₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (verify : (Stmt₁ × ∀ i, OStmt₁ i) → pSpec₁.FullTranscript → (Stmt₂ × ∀ i, OStmt₂ i))
    (hVerify : V₁.toVerifier = ⟨fun stmt tr => pure (verify stmt tr)⟩)
    (hInit : ∃ s, s ∈ support init) (hInitNF : Pr[⊥ | init] = 0)
    (hNE₂ : Nonempty (Stmt₂ × ∀ i, OStmt₂ i))
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    (h₁ : V₁.rbrSoundness init impl lang₁ lang₂ rbrSoundnessError₁)
    (h₂ : V₂.rbrSoundness init impl lang₂ lang₃ rbrSoundnessError₂) :
    appendRbrSoundnessResidual (init := init) (impl := impl) V₁ V₂ h₁ h₂ :=
  append_rbrSoundness_subsingleton V₁ V₂ verify hVerify hInit hInitNF hNE₂ hn hDir hDir₂ h₁ h₂

end OracleVerifier

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms OracleVerifier.append_rbrSoundness_subsingleton
#print axioms OracleVerifier.appendRbrSoundnessResidual_msg_subsingleton
