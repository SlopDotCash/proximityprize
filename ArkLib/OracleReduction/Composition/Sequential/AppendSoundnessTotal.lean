/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.AppendSoundnessChallengeProof
import ArkLib.OracleReduction.Composition.Sequential.AppendSoundnessOracleMsg

/-!
# Seam-agnostic append soundness (issues #62 / #13 / #114 / #362)

This file closes the seam split for plain append *soundness*, mirroring what
`AppendPerfectCompletenessTotal.lean` already does for completeness:

* `Verifier.append_soundness_total_pos` — the seam-agnostic Verifier-level keystone for any
  *nonempty* trailing protocol: case on the direction of `pSpec₂`'s opening round and defer to
  the proven message-seam (`append_soundness_msg`) or challenge-seam
  (`append_soundness_challenge`) keystones.  The `n = 0` case is NOT covered (neither seam
  keystone applies to an empty right protocol; every concrete ArkLib consumer to date has a
  nonempty trailing protocol).
* `Verifier.appendSoundnessResidual_total_pos` — the named residual
  `Verifier.appendSoundnessResidual` (`Append.lean`) discharged seam-agnostically.
* `OracleVerifier.append_soundness_challenge` / `appendSoundnessResidual_challenge` — the
  `OracleVerifier` lift of the challenge-seam keystone (the challenge companion of
  `AppendSoundnessOracleMsg.lean`), via the proven binary fusion
  `OracleReduction.oracleVerifier_append_toVerifier`.
* `OracleVerifier.append_soundness_total_pos` / `appendSoundnessResidual_total_pos` — the
  oracle-level seam-agnostic total, discharging the named residual
  `OracleVerifier.appendSoundnessResidual` for every nonempty trailing protocol.  This is the
  form the `h_residual` call sites in `BatchedFri/Security.lean` /
  `BatchedFri/QueryRoundSoundness.lean` and the FRI top seam can consume without first
  inspecting their seam direction.

All side conditions are the standard honest-implementation facts already required by the two
seam keystones (`himplSP`/`himplNF`/`himplVB`; vacuous for `oSpec = []ₒ`), plus the
`[oSpec.Fintype] [oSpec.Inhabited]` instances inherited from the challenge-seam toolkit.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped ENNReal NNReal

universe u

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Stmt₂ Stmt₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- **Seam-agnostic binary append soundness, nonempty trailing protocol.**  The appended
verifier is sound with additive error `ε₁ + ε₂` from the two components' soundness alone,
regardless of the direction of the seam round: the seam direction is read off
(`Prover.append_dir_natAdd`) and the proof defers to the message-seam
(`append_soundness_msg`) or challenge-seam (`append_soundness_challenge`) keystone. -/
theorem append_soundness_total_pos
    [oSpec.Fintype] [oSpec.Inhabited] [Inhabited Stmt₂]
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {lang₁ : Set Stmt₁} {lang₂ : Set Stmt₂} {lang₃ : Set Stmt₃} {ε₁ ε₂ : ℝ≥0}
    (h₁ : V₁.soundness init impl lang₁ lang₂ ε₁)
    (h₂ : V₂.soundness init impl lang₂ lang₃ ε₂)
    (hn : 0 < n)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    (V₁.append V₂).soundness init impl lang₁ lang₃ (ε₁ + ε₂) := by
  have hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n))
      = pSpec₂.dir (⟨0, hn⟩ : Fin n) := by
    rw [show (⟨m, by omega⟩ : Fin (m + n)) = Fin.natAdd m ⟨0, hn⟩ from by ext; simp,
      Prover.append_dir_natAdd]
  cases hd : pSpec₂.dir (⟨0, hn⟩ : Fin n) with
  | V_to_P =>
    exact append_soundness_challenge V₁ V₂ h₁ h₂ hn (hDir.trans hd) hd
      himplSP himplNF himplVB
  | P_to_V =>
    exact append_soundness_msg V₁ V₂ h₁ h₂ hn (hDir.trans hd) hd
      himplSP himplNF himplVB

/-- **Seam-agnostic discharge of the named residual `Verifier.appendSoundnessResidual`**
(`Append.lean`) for every nonempty trailing protocol, under the standard
honest-implementation side conditions. -/
theorem appendSoundnessResidual_total_pos
    [oSpec.Fintype] [oSpec.Inhabited] [Inhabited Stmt₂]
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {lang₁ : Set Stmt₁} {lang₂ : Set Stmt₂} {lang₃ : Set Stmt₃} {ε₁ ε₂ : ℝ≥0}
    (h₁ : V₁.soundness init impl lang₁ lang₂ ε₁)
    (h₂ : V₂.soundness init impl lang₂ lang₃ ε₂)
    (hn : 0 < n)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    Verifier.appendSoundnessResidual (init := init) (impl := impl)
      (lang₁ := lang₁) (lang₂ := lang₂) (lang₃ := lang₃) V₁ V₂ h₁ h₂ :=
  append_soundness_total_pos V₁ V₂ h₁ h₂ hn himplSP himplNF himplVB

end Verifier

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

/-- **OracleVerifier-level plain-soundness append keystone, challenge seam (unconditional).**
The challenge-seam companion of `OracleVerifier.append_soundness_msg`
(`AppendSoundnessOracleMsg.lean`): the appended oracle verifier is sound with additive error
`ε₁ + ε₂` when `pSpec₂` opens with a *verifier challenge* (`V_to_P` seam).

Proof: `OracleVerifier.soundness` is definitionally `toVerifier`-level; rewrite the appended
`toVerifier` via the proven binary fusion `oracleVerifier_append_toVerifier`, then apply the
unconditional plain challenge-seam keystone `Verifier.append_soundness_challenge`. -/
theorem append_soundness_challenge
    [oSpec.Fintype] [oSpec.Inhabited] [Inhabited (Stmt₂ × ∀ i, OStmt₂ i)]
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    [OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁]
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂)
    {soundnessError₁ soundnessError₂ : ℝ≥0}
    (h₁ : V₁.soundness (init := init) (impl := impl) lang₁ lang₂ soundnessError₁)
    (h₂ : V₂.soundness (init := init) (impl := impl) lang₂ lang₃ soundnessError₂)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .V_to_P)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .V_to_P)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
      (OracleVerifier.append (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁ V₂).soundness
        init impl lang₁ lang₃ (soundnessError₁ + soundnessError₂) := by
  unfold OracleVerifier.soundness at h₁ h₂ ⊢
  rw [OracleReduction.oracleVerifier_append_toVerifier]
  exact Verifier.append_soundness_challenge V₁.toVerifier V₂.toVerifier h₁ h₂ hn hDir hDir₂
    himplSP himplNF himplVB

/-- **Challenge-seam discharge of the named residual `OracleVerifier.appendSoundnessResidual`**
(`Append.lean`), the companion of `appendSoundnessResidual_msg`.  With both seam discharges,
`OracleVerifier.append_soundness` no longer needs an unproved hypothesis at either seam
direction. -/
theorem appendSoundnessResidual_challenge
    [oSpec.Fintype] [oSpec.Inhabited] [Inhabited (Stmt₂ × ∀ i, OStmt₂ i)]
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    [OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁]
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂)
    {soundnessError₁ soundnessError₂ : ℝ≥0}
    (h₁ : V₁.soundness (init := init) (impl := impl) lang₁ lang₂ soundnessError₁)
    (h₂ : V₂.soundness (init := init) (impl := impl) lang₂ lang₃ soundnessError₂)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .V_to_P)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .V_to_P)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    appendSoundnessResidual (init := init) (impl := impl) V₁ V₂ h₁ h₂ :=
  append_soundness_challenge V₁ V₂ h₁ h₂ hn hDir hDir₂ himplSP himplNF himplVB

/-- **Seam-agnostic OracleVerifier append soundness, nonempty trailing protocol.**  The
oracle-level analogue of `Verifier.append_soundness_total_pos`: case on the seam direction
and defer to the message-seam or challenge-seam oracle keystone. -/
theorem append_soundness_total_pos
    [oSpec.Fintype] [oSpec.Inhabited] [Inhabited (Stmt₂ × ∀ i, OStmt₂ i)]
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    [OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁]
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂)
    {soundnessError₁ soundnessError₂ : ℝ≥0}
    (h₁ : V₁.soundness (init := init) (impl := impl) lang₁ lang₂ soundnessError₁)
    (h₂ : V₂.soundness (init := init) (impl := impl) lang₂ lang₃ soundnessError₂)
    (hn : 0 < n)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
      (OracleVerifier.append (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁ V₂).soundness
        init impl lang₁ lang₃ (soundnessError₁ + soundnessError₂) := by
  have hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n))
      = pSpec₂.dir (⟨0, hn⟩ : Fin n) := by
    rw [show (⟨m, by omega⟩ : Fin (m + n)) = Fin.natAdd m ⟨0, hn⟩ from by ext; simp,
      Prover.append_dir_natAdd]
  cases hd : pSpec₂.dir (⟨0, hn⟩ : Fin n) with
  | V_to_P =>
    exact append_soundness_challenge V₁ V₂ h₁ h₂ hn (hDir.trans hd) hd
      himplSP himplNF himplVB
  | P_to_V =>
    exact append_soundness_msg V₁ V₂ h₁ h₂ hn (hDir.trans hd) hd
      himplSP himplNF himplVB

/-- **Seam-agnostic discharge of the named residual `OracleVerifier.appendSoundnessResidual`**
for every nonempty trailing protocol.  This is the drop-in provider for the `h_residual`
hypotheses of the Batched-FRI security tower and the FRI top seam: no seam-direction
inspection needed at the call site. -/
theorem appendSoundnessResidual_total_pos
    [oSpec.Fintype] [oSpec.Inhabited] [Inhabited (Stmt₂ × ∀ i, OStmt₂ i)]
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    [OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁]
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂)
    {soundnessError₁ soundnessError₂ : ℝ≥0}
    (h₁ : V₁.soundness (init := init) (impl := impl) lang₁ lang₂ soundnessError₁)
    (h₂ : V₂.soundness (init := init) (impl := impl) lang₂ lang₃ soundnessError₂)
    (hn : 0 < n)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    appendSoundnessResidual (init := init) (impl := impl) V₁ V₂ h₁ h₂ :=
  append_soundness_total_pos V₁ V₂ h₁ h₂ hn himplSP himplNF himplVB

end OracleVerifier

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms Verifier.append_soundness_total_pos
#print axioms Verifier.appendSoundnessResidual_total_pos
#print axioms OracleVerifier.append_soundness_challenge
#print axioms OracleVerifier.appendSoundnessResidual_challenge
#print axioms OracleVerifier.append_soundness_total_pos
#print axioms OracleVerifier.appendSoundnessResidual_total_pos
