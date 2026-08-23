/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.AppendRbrKnowledgeFailingDet
import ArkLib.OracleReduction.Composition.Sequential.AppendRbrKnowledgeChallenge

/-!
# Failing-deterministic rbr knowledge-soundness append keystone — CHALLENGE seam

The `V_to_P`-seam companion of `AppendRbrKnowledgeFailingDet.lean` (issue #313, BinaryBasefold
closeout): round-by-round knowledge soundness of `append` when the first round of `pSpec₂` is a
**challenge** round and the left verifier is only **failing**-deterministic
(`verify? : Stmt₁ → FullTranscript → Option Stmt₂`, i.e. `⟨fun s tr => OptionT.mk (pure
(verify? s tr))⟩`).

The proof replays the **optionization reduction** verbatim against the challenge-seam total-det
keystone: rewrite the seam by `Verifier.append_failingDet_eq_optionized` into the
total-deterministic seam over `Option Stmt₂` (determinism witness `rfl`, `Nonempty (Option Stmt₂)`
free via `none`), transport the per-phase hypotheses by
`Verifier.failingDet_optionized_rbrKnowledgeSoundness` / `Verifier.optionLift_rbrKnowledgeSoundness`
(both seam-direction-agnostic), and close with the residual-free challenge-seam keystone
`Verifier.append_rbrKnowledgeSoundness_keystone_subsingleton_challenge`
(`AppendRbrKnowledgeChallenge.lean`).

**Consumer shape (BinaryBasefold).** The full protocol is
`append(coreInteraction, queryPhase)` with `pSpecQuery = ⟨![.V_to_P], …⟩` (the seam round is the
verifier's batch of query challenges) and a failing-deterministic core verifier. The keystone's
error output `Sum.elim err₁ err₂ ∘ ChallengeIdx.sumEquiv.symm` matches the front door's
`fullRbrKnowledgeError = fun i => Sum.elim err₁ err₂ (ChallengeIdx.sumEquiv.symm i)`
definitionally; the flattening is recorded as `Verifier.sumElim_comp_sumEquiv_symm`.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped ENNReal NNReal

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Stmt₂ Stmt₃ : Type}
    {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

/-- **Error-form flattening.** The keystone's composed error `Sum.elim err₁ err₂ ∘
ChallengeIdx.sumEquiv.symm` is definitionally the pointwise `Sum.elim`-of-`sumEquiv.symm` form
used by consumer-side error definitions (e.g. BinaryBasefold's `fullRbrKnowledgeError`). -/
theorem sumElim_comp_sumEquiv_symm
    (err₁ : pSpec₁.ChallengeIdx → ℝ≥0) (err₂ : pSpec₂.ChallengeIdx → ℝ≥0) :
    (Sum.elim err₁ err₂ ∘ ChallengeIdx.sumEquiv.symm
        : (pSpec₁ ++ₚ pSpec₂).ChallengeIdx → ℝ≥0)
      = fun i => Sum.elim err₁ err₂ (ChallengeIdx.sumEquiv.symm i) := rfl

variable {Wit₂ : Type} {σ : Type} {init : ProbComp σ}
    {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- **The failing-deterministic rbr knowledge-soundness append keystone (`Subsingleton σ`,
CHALLENGE seam).** The `V_to_P`-seam capstone of the optionization reduction: appending a
*failing*-deterministic left verifier (the BinaryBasefold `coreInteraction` shape, `else failure`)
to `V₂` across a challenge seam (first round of `pSpec₂` is `.V_to_P`) is round-by-round knowledge
sound with the additive `Sum.elim` error — **no residual hypotheses** beyond the per-phase bounds,
the failing-determinism shape itself, and the stateless regime's side conditions.

Proof: rewrite the seam by `append_failingDet_eq_optionized` into the total-deterministic seam over
`Option Stmt₂` (where the determinism witness is `rfl` and `Nonempty (Option Stmt₂)` is free via
`none`), transport `h₁`/`h₂` by `failingDet_optionized_rbrKnowledgeSoundness` /
`optionLift_rbrKnowledgeSoundness`, and apply the residual-free total-deterministic challenge-seam
keystone `append_rbrKnowledgeSoundness_keystone_subsingleton_challenge`. -/
theorem append_rbrKnowledgeSoundness_failingDet_subsingleton_challenge
    [Subsingleton σ] [Inhabited Stmt₂]
    {Stmt₃ Wit₁ Wit₃ : Type} {n : ℕ} {pSpec₂ : ProtocolSpec n}
    [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
    (verify? : Stmt₁ → pSpec₁.FullTranscript → Option Stmt₂)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}
    {err₁ : pSpec₁.ChallengeIdx → ℝ≥0} {err₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (hInit : ∃ s, s ∈ support init) (hInitNF : Pr[⊥ | init] = 0)
    (hNEW₂ : Nonempty Wit₂)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .V_to_P)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .V_to_P)
    (h₁ : Verifier.rbrKnowledgeSoundness init impl rel₁ rel₂
      (⟨fun s tr => OptionT.mk (pure (verify? s tr))⟩ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) err₁)
    (h₂ : V₂.rbrKnowledgeSoundness init impl rel₂ rel₃ err₂) :
    (Verifier.append
        (⟨fun s tr => OptionT.mk (pure (verify? s tr))⟩ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
        V₂).rbrKnowledgeSoundness init impl rel₁ rel₃
      (Sum.elim err₁ err₂ ∘ ChallengeIdx.sumEquiv.symm) := by
  rw [append_failingDet_eq_optionized]
  exact append_rbrKnowledgeSoundness_keystone_subsingleton_challenge
    (⟨fun s tr => pure (verify? s tr)⟩ : Verifier oSpec Stmt₁ (Option Stmt₂) pSpec₁)
    V₂.optionLift verify? rfl hInit hInitNF ⟨none⟩ hNEW₂ hn hDir hDir₂
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
    {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    [Oₘ₁ : ∀ i, OracleInterface (pSpec₁.Message i)]
    [Oₘ₂ : ∀ i, OracleInterface (pSpec₂.Message i)]
    [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel₁ : Set ((Stmt₁ × ∀ i, OStmt₁ i) × Wit₁)}
    {rel₂ : Set ((Stmt₂ × ∀ i, OStmt₂ i) × Wit₂)}
    {rel₃ : Set ((Stmt₃ × ∀ i, OStmt₃ i) × Wit₃)}

/-- **OracleVerifier-level failing-deterministic rbr knowledge-soundness append keystone
(`Subsingleton σ`, CHALLENGE seam).** The OracleVerifier companion of
`Verifier.append_rbrKnowledgeSoundness_failingDet_subsingleton_challenge` and the `V_to_P`-seam
companion of `OracleVerifier.append_rbrKnowledgeSoundness_failingDet_subsingleton`: discharges the
rbr knowledge soundness of `OracleVerifier.append` for seams whose left verifier compiles to a
*failing*-deterministic `toVerifier` (witnesses supplied by `toVerifier_eq_failingDet_of_collapse`
+ the composition combinators) and whose right phase opens with a challenge round — the
BinaryBasefold `append(coreInteraction, queryPhase)` shape. One-shot from
`oracleVerifier_append_toVerifier` + the Protocol-level challenge-seam failing-det capstone. -/
theorem append_rbrKnowledgeSoundness_failingDet_subsingleton_challenge
    [Subsingleton σ] [Inhabited (Stmt₂ × ∀ i, OStmt₂ i)]
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    [OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁]
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂)
    {rbrKnowledgeError₁ : pSpec₁.ChallengeIdx → ℝ≥0}
    {rbrKnowledgeError₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (verify? : (Stmt₁ × ∀ i, OStmt₁ i) → pSpec₁.FullTranscript →
      Option (Stmt₂ × ∀ i, OStmt₂ i))
    (hVerify : V₁.toVerifier = ⟨fun p tr => OptionT.mk (pure (verify? p tr))⟩)
    (hInit : ∃ s, s ∈ support init) (hInitNF : Pr[⊥ | init] = 0)
    (hNEW₂ : Nonempty Wit₂)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .V_to_P)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .V_to_P)
    (h₁ : V₁.rbrKnowledgeSoundness init impl rel₁ rel₂ rbrKnowledgeError₁)
    (h₂ : V₂.rbrKnowledgeSoundness init impl rel₂ rel₃ rbrKnowledgeError₂) :
      (OracleVerifier.append (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁ V₂).rbrKnowledgeSoundness
        init impl rel₁ rel₃
        (Sum.elim rbrKnowledgeError₁ rbrKnowledgeError₂ ∘ ChallengeIdx.sumEquiv.symm) := by
  unfold OracleVerifier.rbrKnowledgeSoundness at h₁ h₂ ⊢
  rw [OracleReduction.oracleVerifier_append_toVerifier, hVerify]
  rw [hVerify] at h₁
  exact Verifier.append_rbrKnowledgeSoundness_failingDet_subsingleton_challenge verify?
    V₂.toVerifier hInit hInitNF hNEW₂ hn hDir hDir₂ h₁ h₂

end OracleVerifier

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms Verifier.sumElim_comp_sumEquiv_symm
#print axioms Verifier.append_rbrKnowledgeSoundness_failingDet_subsingleton_challenge
#print axioms OracleVerifier.append_rbrKnowledgeSoundness_failingDet_subsingleton_challenge
