/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.AppendSoundnessMsgProof
import ArkLib.OracleReduction.Composition.Sequential.AppendChallengeSeamChallenge

/-!
# Binary sequential-composition soundness (challenge seam) — `appendSoundnessResidual` discharge

The challenge-seam (`V_to_P` seam) analogue of `AppendSoundnessMsgProof.lean`: discharges
`Verifier.appendSoundnessResidual` when the second protocol opens with a *verifier challenge*.

The proof replays `append_soundness_msg'`'s canonical chain verbatim — the union-bound machinery
(`probComp_seam_swap_union_le`) and both per-phase bounds (the `fstSound`/`sndSound` provers, the
left/right challenge-oracle-seam transfers, and the state-independence collapse) are seam-type
agnostic — with a single substitution at the head: the *syntactic* prover run factoring
`Prover.run_seam_factor` (false at a challenge seam, where the appended prover samples the seam
`getChallenge` before replaying `fst`'s output) is replaced by the *distributional* factoring
`Reduction.soundness_game_factor_challenge` (built on the proven simulated seam-challenge commute
of `AppendChallengeSeamChallenge.lean`), spliced in at the `evalDist` level via
`EvalDistEq.prEvent_eq`.

The extra `[∀ q, Fintype (oSpec.Range q)] [∀ q, Inhabited (oSpec.Range q)]` instances (inherited from the challenge-seam
factoring toolkit) are the only added side conditions relative to the message-seam case.
-/

open OracleComp OracleSpec ProtocolSpec OptionTStateT
open scoped ENNReal NNReal

universe u

-- Historical all-subsets observations include the complete product and Option outputs.
private local instance (A : Type) : MeasurableSpace A := ⊤
private local instance (A B : Type) : MeasurableSpace (A × B) := ⊤
private local instance (A : Type) : MeasurableSpace (Option A) := ⊤
private local instance (A : Type) : @DiscreteMeasurableSpace A ⊤ := ⟨fun _ => True.intro⟩

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Stmt₂ Stmt₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- **Binary append-soundness, challenge seam (`V_to_P`), canonical-chain proof.** The verbatim
shared stage-bound proof with the syntactic prover run factoring replaced by the
distributional challenge-seam factoring `Reduction.soundness_game_factor_challenge` (spliced in at
the `evalDist` level via `probEvent_congr'`); the union bound and both per-phase
(`fstSound`/`sndSound`) bounds are seam-type agnostic. -/
theorem append_soundness_challenge'
    [∀ q, Fintype (oSpec.Range q)] [∀ q, Inhabited (oSpec.Range q)] [Inhabited Stmt₂]
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {lang₁ : Set Stmt₁} {lang₂ : Set Stmt₂} {lang₃ : Set Stmt₃} {ε₁ ε₂ : ℝ≥0}
    (h₁ : V₁.soundness init impl lang₁ lang₂ ε₁)
    (h₂ : V₂.soundness init impl lang₂ lang₃ ε₂)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .V_to_P)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .V_to_P)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), prFail ((impl t).run s) = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    (V₁.append V₂).soundness init impl lang₁ lang₃ (ε₁ + ε₂) := by
  apply append_soundness_of_game_factorization V₁ V₂ h₁ h₂ himplSP himplNF himplVB
  intro WitIn WitOut prover stmtIn witIn
  rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete]
  congr 1
  funext s
  exact Reduction.soundness_game_factor_challenge V₁ V₂ prover stmtIn witIn hn hDir hDir₂
    himplSP s


/-- **Unconditional discharge of the named append-soundness residual, challenge-seam case.** The
challenge-seam companion of `append_soundness_msg_residual`: for a `V_to_P` seam (the second
protocol opens with a verifier challenge), `Verifier.appendSoundnessResidual V₁ V₂ h₁ h₂` — which is
definitionally `(V₁.append V₂).soundness init impl lang₁ lang₃ (ε₁ + ε₂)` — follows from
`append_soundness_challenge'` under the challenge-seam side conditions. Together with the
message-seam discharge this covers both possible directions of a non-empty second protocol's
opening round. -/
theorem append_soundness_challenge_residual
    [∀ q, Fintype (oSpec.Range q)] [∀ q, Inhabited (oSpec.Range q)] [Inhabited Stmt₂]
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {lang₁ : Set Stmt₁} {lang₂ : Set Stmt₂} {lang₃ : Set Stmt₃} {ε₁ ε₂ : ℝ≥0}
    (h₁ : V₁.soundness init impl lang₁ lang₂ ε₁)
    (h₂ : V₂.soundness init impl lang₂ lang₃ ε₂)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .V_to_P)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .V_to_P)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), prFail ((impl t).run s) = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    Verifier.appendSoundnessResidual (init := init) (impl := impl)
      (lang₁ := lang₁) (lang₂ := lang₂) (lang₃ := lang₃) V₁ V₂ h₁ h₂ :=
  append_soundness_challenge' V₁ V₂ h₁ h₂ hn hDir hDir₂ himplSP himplNF himplVB

/-- **Unconditional binary append-soundness, challenge-seam case** (the conclusion of
`Verifier.append_soundness` with the residual hypothesis *eliminated*), for a `V_to_P` seam. -/
theorem append_soundness_challenge
    [∀ q, Fintype (oSpec.Range q)] [∀ q, Inhabited (oSpec.Range q)] [Inhabited Stmt₂]
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {lang₁ : Set Stmt₁} {lang₂ : Set Stmt₂} {lang₃ : Set Stmt₃} {ε₁ ε₂ : ℝ≥0}
    (h₁ : V₁.soundness init impl lang₁ lang₂ ε₁)
    (h₂ : V₂.soundness init impl lang₂ lang₃ ε₂)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .V_to_P)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .V_to_P)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), prFail ((impl t).run s) = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    (V₁.append V₂).soundness init impl lang₁ lang₃ (ε₁ + ε₂) :=
  append_soundness_challenge' V₁ V₂ h₁ h₂ hn hDir hDir₂ himplSP himplNF himplVB

end Verifier

-- Axiom audit: the unconditional challenge-seam composition lemmas must not introduce `sorryAx`.
#print axioms Verifier.append_soundness_challenge'
#print axioms Verifier.append_soundness_challenge_residual
#print axioms Verifier.append_soundness_challenge
