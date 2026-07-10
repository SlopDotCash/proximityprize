/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G81DMultisetRelativePermutation
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G85EndpointAssemblyMultiset
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G86MaximalSplitEmbeddingExtraction

/-!
# G87: ordered assembly representation after maximal cancellation

G86 extracts core-slot embeddings whose canonical complementary padding words have equal value
multisets.  This file adapts G81D to `Fin`-indexed words, obtaining one relative permutation of
the padding positions, and then gives an exact ordered assembly representation of both endpoints.

This is the existential inverse representation needed by the factorial-corrected decoder.  It
does not yet package a counted core type or define the decoder itself.  Issue #466/#505.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G87MaximalCancellationAssemblyRepresentation

open ArkLib.ProximityGap.Frontier.G81DMultisetRelativePermutation
open ArkLib.ProximityGap.Frontier.G83MMaximalCommonCancellation
open ArkLib.ProximityGap.Frontier.G84AEndpointAssembly
open ArkLib.ProximityGap.Frontier.G85EndpointAssemblyMultiset
open ArkLib.ProximityGap.Frontier.G86MaximalSplitEmbeddingExtraction

variable {A : Type*} [DecidableEq A]

/-- **`Fin`-word adapter for G81D.**  Two equally long words with the same value multiset differ
by one permutation of their positions.  The orientation matches the corrected decoder: the right
padding word is the left padding word precomposed with `σ`. -/
theorem exists_perm_of_valueMultiset_eq {n : ℕ} (left right : Fin n → A)
    (hbag : valueMultiset left = valueMultiset right) :
    ∃ σ : Equiv.Perm (Fin n), right = left ∘ σ := by
  let leftList := List.ofFn left
  let rightList := List.ofFn right
  have hl : leftList.length = n := by simp [leftList]
  have hr : rightList.length = n := by simp [rightList]
  have hlistBag : (leftList : Multiset A) = rightList := by
    simpa [leftList, rightList, valueMultiset_eq_coe_ofFn] using hbag
  obtain ⟨e, he⟩ := exists_indexEquiv_of_multiset_eq leftList rightList hlistBag
  let σ : Equiv.Perm (Fin n) :=
    (finCongr hr.symm).trans (e.trans (finCongr hl))
  refine ⟨σ, ?_⟩
  funext i
  let ir : Fin rightList.length := (finCongr hr.symm) i
  have hvalue := he ir
  simpa [leftList, rightList, σ, ir] using hvalue.symm

/-- **Exact maximal-cancellation assembly representation.**  If the left maximal residual has
depth `s`, both endpoints are assembled from ordered depth-`s` core words and one common ordered
padding word.  The right endpoint uses only one additional relative padding permutation.

The core words enumerate exactly G83M's left and right residual multisets. -/
theorem exists_maximalCancellation_assembly {r s : ℕ} (hsr : s ≤ r)
    (left right : Fin r → A)
    (hleftCoreCard : (leftCore (valueMultiset left) (valueMultiset right)).card = s) :
    ∃ (leftCoreWord rightCoreWord : Fin s → A)
      (eLeft eRight : Fin s ↪ Fin r)
      (padding : Fin (r - s) → A) (σ : Equiv.Perm (Fin (r - s))),
      valueMultiset leftCoreWord =
          leftCore (valueMultiset left) (valueMultiset right) ∧
      valueMultiset rightCoreWord =
          rightCore (valueMultiset left) (valueMultiset right) ∧
      valueMultiset padding =
          commonPart (valueMultiset left) (valueMultiset right) ∧
      assemble hsr eLeft leftCoreWord padding = left ∧
      assemble hsr eRight rightCoreWord (padding ∘ σ) = right := by
  obtain ⟨eLeft, eRight, hLeftCore, hRightCore, hLeftPad, hRightPad⟩ :=
    exists_embeddings_equal_padding_of_maximal_split hsr left right hleftCoreCard
  let leftCoreWord := coreAt eLeft left
  let rightCoreWord := coreAt eRight right
  let leftPadding := padAt hsr eLeft left
  let rightPadding := padAt hsr eRight right
  have hPaddingBag : valueMultiset leftPadding = valueMultiset rightPadding := by
    rw [hLeftPad, hRightPad]
  obtain ⟨σ, hσ⟩ := exists_perm_of_valueMultiset_eq leftPadding rightPadding hPaddingBag
  refine ⟨leftCoreWord, rightCoreWord, eLeft, eRight, leftPadding, σ,
    hLeftCore, hRightCore, hLeftPad, ?_, ?_⟩
  · exact assemble_coreAt_padAt hsr eLeft left
  · rw [← hσ]
    exact assemble_coreAt_padAt hsr eRight right

end ArkLib.ProximityGap.Frontier.G87MaximalCancellationAssemblyRepresentation

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G87MaximalCancellationAssemblyRepresentation.exists_perm_of_valueMultiset_eq
#print axioms
  ArkLib.ProximityGap.Frontier.G87MaximalCancellationAssemblyRepresentation.exists_maximalCancellation_assembly
