/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G83MMaximalCommonCancellation
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G85EOccurrenceEmbedding
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G85EndpointAssemblyMultiset

/-!
# G86: extract endpoint embeddings from a maximal multiset split

This file turns a multiset reconstruction `core + padding = values endpoint`, with a prescribed
core cardinality, into an actual embedding of the core occurrences in the endpoint.  Restricting
to the canonical complementary slots then has exactly the prescribed padding multiset.  Applying
the result to the two G83M reconstructions gives equal canonical-complement padding bags.

Repeated values are handled by G85E's occurrence-index bijection, rather than by support sets.
Issue #466/#505.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G86MaximalSplitEmbeddingExtraction

open ArkLib.ProximityGap.Frontier.G83MMaximalCommonCancellation
open ArkLib.ProximityGap.Frontier.G85EOccurrenceEmbedding
open ArkLib.ProximityGap.Frontier.G85EndpointAssemblyMultiset

variable {A : Type*} [DecidableEq A]

/-- Enumerating a `Fin`-indexed word as a value multiset agrees with `List.ofFn`. -/
theorem valueMultiset_eq_coe_ofFn {n : ℕ} (word : Fin n → A) :
    valueMultiset word = (List.ofFn word : Multiset A) := by
  exact Fin.univ_val_map word

/-- A multiset split with a core of size `s` selects `s` occurrence positions in the endpoint.
The selected word has exactly the core bag, including all multiplicities. -/
theorem exists_coreEmbedding_of_split {r s : ℕ}
    (word : Fin r → A) (coreBag padBag : Multiset A)
    (hcoreCard : coreBag.card = s)
    (hsplit : coreBag + padBag = valueMultiset word) :
    ∃ e : Fin s ↪ Fin r, valueMultiset (coreAt e word) = coreBag := by
  let core := coreBag.toList
  let pad := padBag.toList
  let endpoint := List.ofFn word
  have hperm : (core ++ pad).Perm endpoint := by
    have heq : ((core ++ pad : List A) : Multiset A) = (endpoint : Multiset A) := by
      change (coreBag.toList : Multiset A) + padBag.toList =
        (List.ofFn word : Multiset A)
      rw [Multiset.coe_toList, Multiset.coe_toList, ← valueMultiset_eq_coe_ofFn]
      exact hsplit
    exact Multiset.coe_eq_coe.mp heq
  have hcoreLen : core.length = s := by simp [core, hcoreCard]
  have hendpointLen : endpoint.length = r := by simp [endpoint]
  let e : Fin s ↪ Fin r :=
    (finCongr hcoreLen.symm).toEmbedding |>.trans
      ((coreEmbedding hperm).trans (finCongr hendpointLen).toEmbedding)
  refine ⟨e, ?_⟩
  rw [valueMultiset_eq_coe_ofFn]
  have hwords : List.ofFn (coreAt e word) = core := by
    apply List.ext_get
    · simp [core, hcoreLen]
    · intro i hi hi'
      simp only [List.length_ofFn] at hi
      let is : Fin s := ⟨i, hi⟩
      let ic : Fin core.length := (finCongr hcoreLen.symm) is
      have hget := get_coreEmbedding hperm ic
      simpa [coreAt, e, endpoint, is, ic] using hget
  rw [hwords]
  exact Multiset.coe_toList coreBag

/-- The canonical complement of an extracted core embedding realizes the other side of the
multiset split. -/
theorem exists_coreEmbedding_and_padding_of_split {r s : ℕ} (hsr : s ≤ r)
    (word : Fin r → A) (coreBag padBag : Multiset A)
    (hcoreCard : coreBag.card = s)
    (hsplit : coreBag + padBag = valueMultiset word) :
    ∃ e : Fin s ↪ Fin r,
      valueMultiset (coreAt e word) = coreBag ∧
      valueMultiset (padAt hsr e word) = padBag := by
  obtain ⟨e, hcore⟩ := exists_coreEmbedding_of_split word coreBag padBag hcoreCard hsplit
  refine ⟨e, hcore, ?_⟩
  exact valueMultiset_padAt_eq_of_split hsr e word coreBag padBag hsplit hcore

/-- **Two-endpoint maximal-cancellation extraction.**  Equal-length endpoints whose G83M
residual cores have depth `s` admit core-slot embeddings for which both canonical complementary
padding words enumerate the same maximal common part. -/
theorem exists_embeddings_equal_padding_of_maximal_split {r s : ℕ} (hsr : s ≤ r)
    (left right : Fin r → A)
    (hleftCoreCard : (leftCore (valueMultiset left) (valueMultiset right)).card = s) :
    ∃ eLeft eRight : Fin s ↪ Fin r,
      valueMultiset (coreAt eLeft left) =
          leftCore (valueMultiset left) (valueMultiset right) ∧
      valueMultiset (coreAt eRight right) =
          rightCore (valueMultiset left) (valueMultiset right) ∧
      valueMultiset (padAt hsr eLeft left) =
          commonPart (valueMultiset left) (valueMultiset right) ∧
      valueMultiset (padAt hsr eRight right) =
          commonPart (valueMultiset left) (valueMultiset right) := by
  let l := valueMultiset left
  let r' := valueMultiset right
  have hcards : l.card = r'.card := by simp [l, r', valueMultiset]
  have hrightCoreCard : (rightCore l r').card = s := by
    rw [← hleftCoreCard]
    exact (core_card_eq hcards).symm
  obtain ⟨eLeft, hLeftCore, hLeftPad⟩ :=
    exists_coreEmbedding_and_padding_of_split hsr left (leftCore l r') (commonPart l r')
      hleftCoreCard (left_reconstruct l r')
  obtain ⟨eRight, hRightCore, hRightPad⟩ :=
    exists_coreEmbedding_and_padding_of_split hsr right (rightCore l r') (commonPart l r')
      hrightCoreCard (right_reconstruct l r')
  exact ⟨eLeft, eRight, hLeftCore, hRightCore, hLeftPad, hRightPad⟩

end ArkLib.ProximityGap.Frontier.G86MaximalSplitEmbeddingExtraction

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G86MaximalSplitEmbeddingExtraction.valueMultiset_eq_coe_ofFn
#print axioms
  ArkLib.ProximityGap.Frontier.G86MaximalSplitEmbeddingExtraction.exists_coreEmbedding_of_split
#print axioms
  ArkLib.ProximityGap.Frontier.G86MaximalSplitEmbeddingExtraction.exists_coreEmbedding_and_padding_of_split
#print axioms
  ArkLib.ProximityGap.Frontier.G86MaximalSplitEmbeddingExtraction.exists_embeddings_equal_padding_of_maximal_split
