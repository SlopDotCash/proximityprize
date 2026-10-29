/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Composition

/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Basic
import ProximityPrize.Extensions.OracleReduction.Composition.Sequential.Append
import ArkLib.OracleReduction.Composition.Sequential.AppendOracleAdapters

/-!
  # Composition for Coordinate-Wise Special Soundness

  This file contains the sequential-composition API for coordinate-wise special soundness (CWSS).
  CWSS composition is factored through the generic `ChallengeTreeShape` API:

  * `CWSSStructure.append` and `CWSSStructure.seqCompose` transport intrinsic CWSS data across
    protocol composition.
  * `CWSSStructure.toShape_append` identifies the CWSS shape of an appended structure with the
    generic appended tree shape.
  * `Verifier.append_treeSpecialSound` is the generic structured-tree preservation statement.
  * `Verifier.append_coordinateWiseSpecialSound` is the CWSS-specific wrapper.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

universe u v

/-- Applying a `cast` of an `Equiv` (transported along equalities of its domain and codomain) agrees
with casting the argument into the original domain and the result out of the original codomain. This
is the single cast-commutation fact underlying the CWSS shape-composition theorems. -/
theorem cast_equiv_apply {A B : Type u} {C D : Type v} (hAB : A = B) (hCD : C = D) (e : A ≃ C)
    (b : B) :
    cast (show (A ≃ C) = (B ≃ D) by rw [hAB, hCD]) e b = cast hCD (e (cast hAB.symm b)) := by
  subst hAB; subst hCD; rfl

namespace ChallengeTreeShape

variable {r : ℕ} {len : Fin r → ℕ} {pSpec : ∀ i, ProtocolSpec (len i)}

/-- Sequential composition of a finite family of generic challenge-tree shapes. -/
def seqCompose (S : ∀ i, ChallengeTreeShape (pSpec i)) :
    ChallengeTreeShape (ProtocolSpec.seqCompose pSpec) where
  arity := fun combinedIdx =>
    let ij := seqComposeChallengeIdxToSigma combinedIdx
    (S ij.1).arity ij.2
  nodeOk := fun combinedIdx challenges =>
    let ij := seqComposeChallengeIdxToSigma combinedIdx
    (S ij.1).nodeOk ij.2 fun j =>
      cast (seqCompose_challenge_eq combinedIdx) (challenges j)

end ChallengeTreeShape

namespace CWSSStructure

variable {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

section AppendChar

variable (D₁ : CWSSStructure pSpec₁) (D₂ : CWSSStructure pSpec₂)

end AppendChar

variable {r : ℕ} {len : Fin r → ℕ} {pSpec : ∀ i, ProtocolSpec (len i)}

/-- Sequential composition of a finite family of CWSS structures. -/
def seqCompose (D : ∀ i, CWSSStructure (pSpec i)) :
    CWSSStructure (ProtocolSpec.seqCompose pSpec) where
  coordIndex := fun i =>
    let ij := seqComposeChallengeIdxToSigma i
    (D ij.1).coordIndex ij.2
  alphabet := fun i =>
    let ij := seqComposeChallengeIdxToSigma i
    (D ij.1).alphabet ij.2
  decompose := fun i =>
    cast (by rw [seqCompose_challenge_eq i])
      ((D (seqComposeChallengeIdxToSigma i).1).decompose (seqComposeChallengeIdxToSigma i).2)
  soundnessParam := fun i =>
    let ij := seqComposeChallengeIdxToSigma i
    (D ij.1).soundnessParam ij.2
  arity := fun i =>
    let ij := seqComposeChallengeIdxToSigma i
    (D ij.1).arity ij.2
  arity_eq := by
    funext i
    exact congrFun ((D (seqComposeChallengeIdxToSigma i).1).arity_eq)
      (seqComposeChallengeIdxToSigma i).2

/-- The arity of a sequentially composed CWSS structure is the component arity at the decoded
component challenge index. -/
theorem seqCompose_arity (D : ∀ i, CWSSStructure (pSpec i)) :
    (seqCompose D).arity =
      fun combinedIdx =>
        let ij := seqComposeChallengeIdxToSigma combinedIdx
        (D ij.1).arity ij.2 := rfl

/-- The sequentially-composed `decompose`, applied, equals the decoded component's `decompose`
applied to the cast-in challenge. The cast-commutation `cast_equiv_apply` applies directly here
because `seqCompose.decompose` is a single cast (no case split). -/
theorem seqCompose_decompose_apply (D : ∀ i, CWSSStructure (pSpec i))
    (ci : (ProtocolSpec.seqCompose pSpec).ChallengeIdx)
    (x : (ProtocolSpec.seqCompose pSpec).Challenge ci) :
    (seqCompose D).decompose ci x =
      (D (seqComposeChallengeIdxToSigma ci).1).decompose (seqComposeChallengeIdxToSigma ci).2
        (cast (seqCompose_challenge_eq ci) x) :=
  cast_equiv_apply (seqCompose_challenge_eq ci).symm rfl
    ((D (seqComposeChallengeIdxToSigma ci).1).decompose (seqComposeChallengeIdxToSigma ci).2) x

/-- The shape induced by finite sequential CWSS data is the generic sequential composition of the
component shapes. -/
theorem toShape_seqCompose (D : ∀ i, CWSSStructure (pSpec i)) :
    CWSSStructure.toShape (seqCompose D) =
      ChallengeTreeShape.seqCompose (fun i => CWSSStructure.toShape (D i)) := by
  refine ChallengeTreeShape.ext rfl (heq_of_eq ?_)
  funext ci challenges
  change CWSSStructure.nodeOk (seqCompose D) ci challenges =
    (D (seqComposeChallengeIdxToSigma ci).1).nodeOk (seqComposeChallengeIdxToSigma ci).2
      (fun j => cast (seqCompose_challenge_eq ci) (challenges j))
  unfold CWSSStructure.nodeOk
  congr 1
  funext j
  rw [seqCompose_decompose_apply]
  rfl

end CWSSStructure

namespace Verifier

open ProtocolSpec ProtocolSpec.ChallengeTree

variable {ι : Type} {oSpec : OracleSpec ι}
  {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
  {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)}
  {rel₃ : Set (Stmt₃ × Wit₃)}

variable [∀ i, SampleableType (pSpec₁.Challenge i)]
  [∀ i, SampleableType (pSpec₂.Challenge i)]

omit [∀ i, SampleableType (pSpec₂.Challenge i)] in
/-- Generic preservation of tree-special soundness under binary verifier append. -/
theorem append_treeSpecialSound
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (S₁ : ChallengeTreeShape pSpec₁) (S₂ : ChallengeTreeShape pSpec₂)
    (verify₁ : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hV₁ : ∀ stmt tr, V₁.verify stmt tr = pure (verify₁ stmt tr))
    (h₁ : V₁.treeSpecialSound init impl S₁ rel₁ rel₂)
    (h₂ : V₂.treeSpecialSound init impl S₂ rel₂ rel₃) :
      (V₁.append V₂).treeSpecialSound init impl
        (S₁.append S₂) rel₁ rel₃ := by
  rcases h₁ with ⟨E₁, hE₁⟩
  rcases h₂ with ⟨E₂, hE₂⟩
  exact ⟨Extractor.TreeBased.append verify₁ E₁ E₂,
    append_treeSpecialSoundWith init impl V₁ V₂ S₁ S₂ verify₁ hV₁ E₁ E₂ hE₁ hE₂⟩

omit [∀ i, SampleableType (pSpec₂.Challenge i)] in
/-- Coordinate-wise special soundness is preserved by binary verifier append.

The deterministic first-verifier output identifies the input statement of each suffix tree consumed
by the second verifier's extractor. -/
theorem append_coordinateWiseSpecialSound
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (D₁ : CWSSStructure pSpec₁) (D₂ : CWSSStructure pSpec₂)
    (verify₁ : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hV₁ : ∀ stmt tr, V₁.verify stmt tr = pure (verify₁ stmt tr))
    (h₁ : V₁.coordinateWiseSpecialSound init impl D₁ rel₁ rel₂)
    (h₂ : V₂.coordinateWiseSpecialSound init impl D₂ rel₂ rel₃) :
      (V₁.append V₂).coordinateWiseSpecialSound init impl
        (CWSSStructure.append D₁ D₂) rel₁ rel₃ := by
  change (V₁.append V₂).treeSpecialSound init impl
    (CWSSStructure.toShape (CWSSStructure.append D₁ D₂)) rel₁ rel₃
  rw [CWSSStructure.toShape_append]
  exact append_treeSpecialSound init impl V₁ V₂
    (CWSSStructure.toShape D₁) (CWSSStructure.toShape D₂) verify₁ hV₁ h₁ h₂

end Verifier

namespace OracleVerifier

open ProtocolSpec

variable {ι : Type} {oSpec : OracleSpec ι}
  {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {ιₛ₁ : Type} {OStmt₁ : ιₛ₁ → Type} [Oₛ₁ : ∀ i, OracleInterface (OStmt₁ i)]
  {ιₛ₂ : Type} {OStmt₂ : ιₛ₂ → Type} [Oₛ₂ : ∀ i, OracleInterface (OStmt₂ i)]
  {ιₛ₃ : Type} {OStmt₃ : ιₛ₃ → Type} [Oₛ₃ : ∀ i, OracleInterface (OStmt₃ i)]
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, OracleInterface (pSpec₁.Message i)] [∀ i, OracleInterface (pSpec₂.Message i)]
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
  {rel₁ : Set ((Stmt₁ × ∀ i, OStmt₁ i) × Wit₁)}
  {rel₂ : Set ((Stmt₂ × ∀ i, OStmt₂ i) × Wit₂)}
  {rel₃ : Set ((Stmt₃ × ∀ i, OStmt₃ i) × Wit₃)}

omit [∀ i, SampleableType (pSpec₂.Challenge i)] in
/-- Oracle-verifier wrapper for binary CWSS append. -/
theorem append_coordinateWiseSpecialSound
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)

    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂)
    (D₁ : CWSSStructure pSpec₁) (D₂ : CWSSStructure pSpec₂)
    (verify₁ :
      (Stmt₁ × ∀ i, OStmt₁ i) → pSpec₁.FullTranscript → (Stmt₂ × ∀ i, OStmt₂ i))
    (hV₁ : ∀ stmt tr, V₁.toVerifier.verify stmt tr = pure (verify₁ stmt tr))
    (h₁ : V₁.coordinateWiseSpecialSound init impl D₁ rel₁ rel₂)
    (h₂ : V₂.coordinateWiseSpecialSound init impl D₂ rel₂ rel₃) :
      (V₁.append V₂).coordinateWiseSpecialSound init impl
        (CWSSStructure.append D₁ D₂) rel₁ rel₃ := by
  unfold OracleVerifier.coordinateWiseSpecialSound at h₁ h₂ ⊢
  rw [OracleReduction.oracleVerifier_append_toVerifier]
  exact Verifier.append_coordinateWiseSpecialSound init impl V₁.toVerifier V₂.toVerifier
    D₁ D₂ verify₁ hV₁ h₁ h₂

end OracleVerifier

end
