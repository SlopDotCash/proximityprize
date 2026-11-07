/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Stir.InitRbrSoundness
import ProximityPrize.Extensions.ProofSystem.Component.SendWitness
import ArkLib.OracleReduction.Composition.Sequential.AppendRbrKnowledgeSoundness

/-!
# STIR chain first seam: init-block RBR through the append keystone (#301)

Composes the zero-error round-by-round knowledge soundness of the initial `[C_fold]` STIR
block through the unconditional append RBR knowledge keystone
(`Verifier.append_rbrKnowledgeSoundness_keystone_unconditional`,
`AppendRbrKnowledgeStateFunction.lean`), for an **arbitrary** tail verifier over an
**arbitrary** (generic, opaque) tail protocol spec `pSpec₂`.

The initial-block factoring and security theorems come from their shared
`InitRbrSoundness` implementation owner.
-/

namespace StirIOP

namespace Round3

open OracleSpec OracleComp ProtocolSpec STIR ReedSolomon NNReal StirIOP.Round Verifier

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

/-! ## The composition theorem (#301): init block ∘ arbitrary tail, through the keystone -/

variable {n : ℕ} {pSpec₂ : ProtocolSpec n} [∀ i, SampleableType (pSpec₂.Challenge i)]
variable {Stmt₃ Wit₃ : Type}

/-- **RBR knowledge soundness of the STIR chain's first seam (init block ∘ arbitrary tail).**

For an arbitrary tail verifier `V₂` over an arbitrary `pSpec₂`, given `V₂`'s RBR knowledge
soundness (`h₂`) and the keystone's phase-2 seam residual (`hPhase2`), the appended verifier
`stirInitVerifier.toVerifier.append V₂` is RBR knowledge sound from `stirOStmtRel Unit` to
`rel₃`, with the tail's error reindexed (the init block's per-round error is `0`).

This is the keystone instantiation that turns the per-block init RBR fact into a chain RBR
fact: `V₁ := stirInitVerifier.toVerifier` with its proven pure-verifier factoring
(`stirInitVerifier_toVerifier_eq`) and zero-error RBR knowledge soundness
(`stirInitVerifier_rbrKnowledgeSoundness`). -/
theorem stirInit_append_rbrKnowledgeSoundness
    (V₂ : Verifier []ₒ (F × ∀ i, OStmt ι F i) Stmt₃ pSpec₂)
    {rel₃ : Set (Stmt₃ × Wit₃)}
    {rbrKnowledgeError₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (φ : ι ↪ F) (deg : ℕ) (δ : ℝ≥0)
    (hInit : ∃ s, s ∈ support init)
    (h₂ : V₂.rbrKnowledgeSoundness init impl (stirOStmtRel F φ deg δ) rel₃ rbrKnowledgeError₂)
    (hPhase2 : ∀ {WitMid₁ : Fin (1 + 1) → Type} {WitMid₂ : Fin (n + 1) → Type}
      {E₁ : Extractor.RoundByRound []ₒ (Unit × ∀ i, OStmt ι F i) Unit Unit
        (pSpecInit F) WitMid₁}
      {E₂ : Extractor.RoundByRound []ₒ (F × ∀ i, OStmt ι F i) Unit Wit₃ pSpec₂ WitMid₂}
      (kSF₁ : (stirInitVerifier (ι := ι) (F := F)).toVerifier.KnowledgeStateFunction init impl
        (stirOStmtRel Unit φ deg δ) (stirOStmtRel F φ deg δ) E₁)
      (kSF₂ : V₂.KnowledgeStateFunction init impl (stirOStmtRel F φ deg δ) rel₃ E₂),
      Verifier.appendRbrKnowledgeSoundnessPhase2Residual (init := init) (impl := impl)
        (stirInitVerifier (ι := ι) (F := F)).toVerifier V₂ kSF₁ kSF₂
        stirInitVerify stirInitVerifier_toVerifier_eq hInit
        (rbrKnowledgeError₂ := rbrKnowledgeError₂)) :
    @Verifier.rbrKnowledgeSoundness PEmpty.{1} []ₒ (Unit × ((i : Unit) → OStmt ι F i)) Unit
      Stmt₃ Wit₃ (1 + n) (pSpecInit F ++ₚ pSpec₂)
      (fun i => instSampleableTypeChallengeAppend i) σ init impl
      (stirOStmtRel Unit φ deg δ) rel₃
      ((stirInitVerifier (ι := ι) (F := F)).toVerifier.append V₂)
      (Sum.elim 0 rbrKnowledgeError₂ ∘ ChallengeIdx.sumEquiv.symm) :=
  Verifier.append_rbrKnowledgeSoundness_keystone_unconditional
    (stirInitVerifier (ι := ι) (F := F)).toVerifier V₂
    stirInitVerify stirInitVerifier_toVerifier_eq hInit
    ⟨(0, fun _ _ => (0 : F))⟩ ⟨()⟩
    (stirInitVerifier_rbrKnowledgeSoundness init impl φ deg δ)
    h₂ hPhase2

end Round3

end StirIOP

#print axioms StirIOP.Round3.stirInitVerifier_toVerifier_eq
#print axioms StirIOP.Round3.stirInitVerifier_rbrKnowledgeSoundness
#print axioms StirIOP.Round3.stirInit_append_rbrKnowledgeSoundness
