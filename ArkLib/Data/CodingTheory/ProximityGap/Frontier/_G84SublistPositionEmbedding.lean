/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.List.Perm.Subperm
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.Tuple.Basic

/-!
# G84: sublist witnesses extract value-preserving tuple slots

The corrected padding decoder needs to turn a residual core submultiset into actual slots of an
ordered endpoint tuple.  The structural bridge is list-theoretic:

* a `Sublist` proof induces an embedding of source positions into target positions preserving
  `List.get` values;
* a `Subperm` proof first permutes the target and then supplies such a sublist.

The second permutation can be transported back to the original tuple using G81D's landed
value-preserving index equivalence.  This file proves the previously missing slot-extraction half
without depending on the branch-local G81/G83 modules.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G84SublistPositionEmbedding

variable {α : Type*}

/-- A sublist has a value-preserving injection of its positions into the ambient list positions. -/
theorem exists_positionEmbedding_of_sublist {l₁ l₂ : List α} (h : List.Sublist l₁ l₂) :
    ∃ e : Fin l₁.length ↪ Fin l₂.length, ∀ i, l₂.get (e i) = l₁.get i := by
  induction h with
  | slnil =>
      let e : Fin 0 ↪ Fin 0 := Function.Embedding.ofIsEmpty
      exact ⟨e, fun i => Fin.elim0 i⟩
  | cons a h ih =>
      rename_i l₁' l₂'
      obtain ⟨e, he⟩ := ih
      let e' : Fin l₁'.length ↪ Fin (a :: l₂').length :=
        e.trans (Fin.succEmb l₂'.length)
      refine ⟨e', fun i => ?_⟩
      simp only [e', Function.Embedding.coeFn_mk, List.get_cons_succ]
      exact he i
  | cons_cons a h ih =>
      rename_i l₁' l₂'
      obtain ⟨e, he⟩ := ih
      let f : Fin (a :: l₁').length → Fin (a :: l₂').length :=
        Fin.cons 0 (fun i => (e i).succ)
      have hf : Function.Injective f := by
        apply Fin.cons_injective_of_injective
        · rintro ⟨i, hi⟩
          exact Fin.succ_ne_zero (e i) hi
        · intro i j hij
          exact e.injective (Fin.succ_inj.mp hij)
      let e' : Fin (a :: l₁').length ↪ Fin (a :: l₂').length := ⟨f, hf⟩
      refine ⟨e', fun i => ?_⟩
      refine Fin.cases ?_ (fun i => ?_) i
      · simp [e', f]
      · simp only [e', f, Function.Embedding.coeFn_mk, Fin.cases_succ, List.get_cons_succ]
        exact he i

/-- A subpermutation can be realized after permuting the ambient list, together with an embedding
of residual positions into that permuted endpoint. -/
theorem exists_permuted_positionEmbedding_of_subperm {l₁ l₂ : List α}
    (h : List.Subperm l₁ l₂) :
    ∃ l₂' : List α, List.Perm l₂' l₂ ∧
      ∃ e : Fin l₁.length ↪ Fin l₂'.length, ∀ i, l₂'.get (e i) = l₁.get i := by
  rw [List.subperm_iff] at h
  obtain ⟨l₂', hperm, hsub⟩ := h
  exact ⟨l₂', hperm, exists_positionEmbedding_of_sublist hsub⟩

end ArkLib.ProximityGap.Frontier.G84SublistPositionEmbedding

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G84SublistPositionEmbedding.exists_positionEmbedding_of_sublist
#print axioms
  ArkLib.ProximityGap.Frontier.G84SublistPositionEmbedding.exists_permuted_positionEmbedding_of_subperm
