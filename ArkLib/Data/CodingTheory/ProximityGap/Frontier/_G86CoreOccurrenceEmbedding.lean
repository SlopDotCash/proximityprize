/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G84AEndpointAssembly

/-!
# G86: extract core-slot embeddings from occurrence permutations

The maximal-cancellation decoder starts with a multiset decomposition of an endpoint into a core
and common padding.  After choosing ordered representatives, this is a permutation
`core.toList ++ padding.toList ~ endpoint.toList`.  `List.Perm.idxBij` matches repeated occurrences
correctly.  Restricting that bijection to the initial core block gives the required core-slot
embedding.

The complementary padding order need not be chosen in advance: G85 reads it from the remaining
endpoint slots and proves that assembling the extracted core with this padding recovers the entire
endpoint.  This is the occurrence-sensitive extraction step of the G81C decoder. Issue #466/#505.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G86CoreOccurrenceEmbedding

open G84AEndpointAssembly
open G84SCorePaddingSlotPartition

def coreAt {A : Type*} {r s : ℕ} (e : Fin s ↪ Fin r) (word : Fin r → A) : Fin s → A :=
  word ∘ e

noncomputable def paddingAt {A : Type*} {r s : ℕ} (hsr : s ≤ r)
    (e : Fin s ↪ Fin r) (word : Fin r → A) : Fin (r - s) → A :=
  word ∘ padSlots hsr e

private theorem assemble_extracted {A : Type*} {r s : ℕ} (hsr : s ≤ r)
    (e : Fin s ↪ Fin r) (word : Fin r → A) :
    assemble hsr e (coreAt e word) (paddingAt hsr e word) = word := by
  funext k
  cases h : (slotEquiv hsr e).symm k with
  | inl i =>
      have hk : k = e i := by
        have := congrArg (slotEquiv hsr e) h
        simpa using this
      subst k
      exact G84AEndpointAssembly.assemble_core
        hsr e (coreAt e word) (paddingAt hsr e word) i
  | inr j =>
      have hk : k = padSlots hsr e j := by
        have := congrArg (slotEquiv hsr e) h
        simpa using this
      subst k
      exact G84AEndpointAssembly.assemble_pad
        hsr e (coreAt e word) (paddingAt hsr e word) j

/-- A permutation from `core ++ padding` to an endpoint supplies an occurrence-preserving
embedding of the core positions into the endpoint positions. Repetitions are handled by
`List.Perm.idxBij`, not by value-level choice. -/
theorem exists_coreEmbedding_of_perm_append
    {A : Type*} [DecidableEq A] {r s : ℕ} (hsr : s ≤ r)
    (core : Fin s → A) (padding : Fin (r - s) → A) (word : Fin r → A)
    (hp : (List.ofFn core ++ List.ofFn padding).Perm (List.ofFn word)) :
    ∃ e : Fin s ↪ Fin r,
      coreAt e word = core ∧
      assemble hsr e core (paddingAt hsr e word) = word := by
  let toConcat : Fin s ↪ Fin (List.ofFn core ++ List.ofFn padding).length :=
    { toFun := fun i => ⟨i.val, by simp; omega⟩
      inj' := by
        intro i j hij
        apply Fin.ext
        simpa using congrArg (fun x => x.val) hij }
  let toWord : Fin (List.ofFn core ++ List.ofFn padding).length ≃
      Fin (List.ofFn word).length :=
    { toFun := hp.idxBij
      invFun := hp.symm.idxBij
      left_inv := hp.idxBij_rightInverse_idxBij_symm
      right_inv := hp.idxBij_leftInverse_idxBij_symm }
  let e : Fin s ↪ Fin r :=
    { toFun := fun i => ⟨(toWord (toConcat i)).val, by simpa using (toWord (toConcat i)).isLt⟩
      inj' := by
        intro i j hij
        apply toConcat.injective
        apply toWord.injective
        apply Fin.ext
        simpa using congrArg (fun x => x.val) hij }
  have hcore : coreAt e word = core := by
    funext i
    have hget := hp.getElem_idxBij_eq_getElem (toConcat i)
    have hv : word ⟨(hp.idxBij (toConcat i)).val,
        by simpa using (hp.idxBij (toConcat i)).isLt⟩ = core i := by
      calc
        word ⟨(hp.idxBij (toConcat i)).val,
            by simpa using (hp.idxBij (toConcat i)).isLt⟩ =
            (List.ofFn core ++ List.ofFn padding)[(toConcat i).val] := by
              simpa only [List.getElem_ofFn] using hget
        _ = core i := by
          change (List.ofFn core ++ List.ofFn padding)[i.val] = core i
          simp
    exact hv
  refine ⟨e, hcore, ?_⟩
  rw [← hcore]
  exact assemble_extracted hsr e word

/-- Multiset reconstruction is enough: equality of quotient multisets produces the occurrence
permutation required by `exists_coreEmbedding_of_perm_append`. -/
theorem exists_coreEmbedding_of_multiset_add
    {A : Type*} [DecidableEq A] {r s : ℕ} (hsr : s ≤ r)
    (core : Fin s → A) (padding : Fin (r - s) → A) (word : Fin r → A)
    (hm : (List.ofFn core : Multiset A) + (List.ofFn padding : Multiset A) =
      (List.ofFn word : Multiset A)) :
    ∃ e : Fin s ↪ Fin r,
      coreAt e word = core ∧
      assemble hsr e core (paddingAt hsr e word) = word := by
  apply exists_coreEmbedding_of_perm_append hsr core padding word
  apply Multiset.coe_eq_coe.mp
  simpa using hm

/-- Two ordered words representing the same multiset differ by one permutation of their position
type, including in the presence of repeated values. This is the function-level coordinate used by
G81C's corrected padding code. -/
theorem exists_perm_comp_of_multiset_eq
    {A : Type*} [DecidableEq A] {t : ℕ} (left right : Fin t → A)
    (hm : (List.ofFn left : Multiset A) = (List.ofFn right : Multiset A)) :
    ∃ σ : Equiv.Perm (Fin t), right = left ∘ σ := by
  have hp : (List.ofFn right).Perm (List.ofFn left) := Multiset.coe_eq_coe.mp hm.symm
  let σ : Equiv.Perm (Fin t) :=
    { toFun := fun i => ⟨(hp.idxBij ⟨i.val, by simpa using i.isLt⟩).val,
        by simpa using (hp.idxBij ⟨i.val, by simpa using i.isLt⟩).isLt⟩
      invFun := fun i => ⟨(hp.symm.idxBij ⟨i.val, by simpa using i.isLt⟩).val,
        by simpa using (hp.symm.idxBij ⟨i.val, by simpa using i.isLt⟩).isLt⟩
      left_inv := by
        intro i
        apply Fin.ext
        simpa using congrArg Fin.val
          (hp.idxBij_rightInverse_idxBij_symm ⟨i.val, by simpa using i.isLt⟩)
      right_inv := by
        intro i
        apply Fin.ext
        simpa using congrArg Fin.val
          (hp.idxBij_leftInverse_idxBij_symm ⟨i.val, by simpa using i.isLt⟩) }
  refine ⟨σ, ?_⟩
  funext i
  have hget := hp.getElem_idxBij_eq_getElem ⟨i.val, by simpa using i.isLt⟩
  simpa only [Function.comp_apply, List.getElem_ofFn, σ] using hget.symm

end ArkLib.ProximityGap.Frontier.G86CoreOccurrenceEmbedding

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G86CoreOccurrenceEmbedding.exists_coreEmbedding_of_perm_append
#print axioms
  ArkLib.ProximityGap.Frontier.G86CoreOccurrenceEmbedding.exists_coreEmbedding_of_multiset_add
#print axioms
  ArkLib.ProximityGap.Frontier.G86CoreOccurrenceEmbedding.exists_perm_comp_of_multiset_eq
