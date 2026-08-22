/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.AppendSoundnessMsgProof
import ArkLib.OracleReduction.Composition.Sequential.AppendToVerifierKeystone

/-!
# OracleVerifier-level plain-soundness append keystone, message seam (issues #62 / #13 / #114)

The generic `OracleVerifier` lift of the unconditional message-seam append-soundness keystone
`Verifier.append_soundness_msg` (`AppendSoundnessMsgProof.lean`), discharging the named residual
`OracleVerifier.appendSoundnessResidual` (`Append.lean`) with no oracle routing left.

LogUp already performs this exact combination ad-hoc
(`Logup.Security/LogupSoundnessUncond.lean`: `oracleAppendSoundnessResidual_of_plain` applied to
`Verifier.append_soundness_msg`); this file records the *generic* combinator so other consumers —
notably the eight `h_residual` call sites in `BatchedFri/Security.lean` /
`BatchedFri/QueryRoundSoundness.lean` and the FRI top seam (`Fri/Spec/Soundness.lean`) — can
discharge their append-soundness hypotheses without re-deriving the fusion plumbing.

The lift is definitional: `OracleVerifier.soundness` *is* `toVerifier`-level
(`Security/Basic.lean`), and the proven binary fusion
`OracleReduction.oracleVerifier_append_toVerifier` identifies the appended oracle verifier's
`toVerifier` with `Verifier.append V₁.toVerifier V₂.toVerifier`, to which the plain message-seam
keystone applies directly.
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

/-- **OracleVerifier-level plain-soundness append keystone, message seam (unconditional).** The
appended oracle verifier is sound with the additive error `ε₁ + ε₂`, from the two components'
soundness alone, given the message-seam direction facts (`hn`/`hDir`/`hDir₂`) and the standard
honest-implementation side conditions (`himplSP`/`himplNF`/`himplVB` — state-preserving,
never-failing, value-blind; all vacuous for `oSpec = []ₒ`).

Proof: `OracleVerifier.soundness` is definitionally `toVerifier`-level; rewrite the appended
`toVerifier` via the proven binary fusion `oracleVerifier_append_toVerifier`, then apply the
unconditional plain message-seam keystone `Verifier.append_soundness_msg`. -/
theorem append_soundness_msg
    [Inhabited (Stmt₂ × ∀ i, OStmt₂ i)]
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    [OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁]
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂)
    {soundnessError₁ soundnessError₂ : ℝ≥0}
    (h₁ : V₁.soundness (init := init) (impl := impl) lang₁ lang₂ soundnessError₁)
    (h₂ : V₂.soundness (init := init) (impl := impl) lang₂ lang₃ soundnessError₂)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
      (OracleVerifier.append (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁ V₂).soundness
        init impl lang₁ lang₃ (soundnessError₁ + soundnessError₂) := by
  unfold OracleVerifier.soundness at h₁ h₂ ⊢
  rw [OracleReduction.oracleVerifier_append_toVerifier]
  exact Verifier.append_soundness_msg V₁.toVerifier V₂.toVerifier h₁ h₂ hn hDir hDir₂
    himplSP himplNF himplVB

/-- **Discharge of the named residual `OracleVerifier.appendSoundnessResidual`** (`Append.lean`)
for the message-first seam under the standard honest-implementation side conditions. The
residual's conclusion is precisely the keystone's, so this is definitional from
`append_soundness_msg`. With this, `OracleVerifier.append_soundness` no longer needs an unproved
hypothesis at a message seam — the regime of the BCS opening phase, LogUp Protocol 2, and the
Batched-FRI batching/fold seams. -/
theorem appendSoundnessResidual_msg
    [Inhabited (Stmt₂ × ∀ i, OStmt₂ i)]
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    [OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁]
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂)
    {soundnessError₁ soundnessError₂ : ℝ≥0}
    (h₁ : V₁.soundness (init := init) (impl := impl) lang₁ lang₂ soundnessError₁)
    (h₂ : V₂.soundness (init := init) (impl := impl) lang₂ lang₃ soundnessError₂)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    appendSoundnessResidual (init := init) (impl := impl) V₁ V₂ h₁ h₂ :=
  append_soundness_msg V₁ V₂ h₁ h₂ hn hDir hDir₂ himplSP himplNF himplVB

end OracleVerifier

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms OracleVerifier.append_soundness_msg
#print axioms OracleVerifier.appendSoundnessResidual_msg
