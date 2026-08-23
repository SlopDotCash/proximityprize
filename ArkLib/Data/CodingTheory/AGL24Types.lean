/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib
import ArkLib.Data.CodingTheory.AGL24WeakPartition

/-!
# [AGL24] §3 opening: types, the type-ordered WLOG, and permutation invariance
# (issue #346, brick 11)

The certificate machinery of [AGL24] §3 fixes a *type-ordered* hypergraph: the **type** of an
index `i` is its edge `eᵢ ⊆ [t]` (at most `2^t` types — the symmetry classes of Remark 2.9
driving the linear alphabet size), and the paper assumes WLOG that equal types appear
consecutively. This brick supplies that foundation:

* `typeKey` — an injective linear-order key on types (via `Fintype.equivFin`);
* `card_types_le` — at most `2^t` distinct types;
* `TypeOrdered` — equal types appear consecutively (the betweenness form);
* `exists_typeOrdered_perm` — **the WLOG**: every edge family is a permutation of a
  type-ordered one (`Tuple.sort` on the key);
* `weaklyPartitionConnected_comp_equiv` — weak partition connectivity is invariant under
  edge reindexing (the sum transports along the equivalence) — the lemma that makes the
  WLOG legitimate for the §3 consumers.
-/

open Finset

namespace AGL24

variable {t : ℕ}

/-- An injective linear-order key on types (edges as subsets of `[t]`). -/
noncomputable def typeKey : Finset (Fin t) → Fin (2 ^ t) :=
  fun s => (Fintype.equivFin (Finset (Fin t))).toFun s |>.cast (by
    rw [Fintype.card_finset, Fintype.card_fin])

theorem typeKey_injective : Function.Injective (typeKey (t := t)) := by
  intro s s' h
  have := Fin.val_eq_of_eq h
  simp only [typeKey, Fin.coe_cast] at this
  exact (Fintype.equivFin (Finset (Fin t))).injective (Fin.val_injective this)

/-- **Remark 2.9's count**: an edge family has at most `2^t` distinct types. -/
theorem card_types_le {n : ℕ} (e : Fin n → Finset (Fin t)) :
    (Finset.univ.image e).card ≤ 2 ^ t := by
  calc (Finset.univ.image e).card
      ≤ Fintype.card (Finset (Fin t)) := Finset.card_le_univ _
  _ = 2 ^ t := by rw [Fintype.card_finset, Fintype.card_fin]

/-- **Type-ordered** ([AGL24] §3): equal types appear consecutively — betweenness form. -/
def TypeOrdered {n : ℕ} (e : Fin n → Finset (Fin t)) : Prop :=
  ∀ i j l : Fin n, i ≤ j → j ≤ l → e i = e l → e i = e j

/-- **The type-ordering WLOG**: every edge family is a permutation of a type-ordered one. -/
theorem exists_typeOrdered_perm {n : ℕ} (e : Fin n → Finset (Fin t)) :
    ∃ σ : Equiv.Perm (Fin n), TypeOrdered (e ∘ σ) := by
  classical
  -- Sort by the injective key.
  set σ := Tuple.sort (fun i => typeKey (e i)) with hσ
  refine ⟨σ, ?_⟩
  intro i j l hij hjl hil
  have hmono : Monotone ((fun i => typeKey (e i)) ∘ σ) := Tuple.monotone_sort _
  -- The keys at the ends agree; monotonicity pinches the middle key.
  have hkey_il : typeKey (e (σ i)) = typeKey (e (σ l)) := congrArg typeKey hil
  have h1 : typeKey (e (σ i)) ≤ typeKey (e (σ j)) := hmono hij
  have h2 : typeKey (e (σ j)) ≤ typeKey (e (σ l)) := hmono hjl
  have hkey_ij : typeKey (e (σ i)) = typeKey (e (σ j)) := by
    refine le_antisymm h1 ?_
    rw [hkey_il]
    exact h2
  exact typeKey_injective hkey_ij

/-- **Permutation invariance of weak partition connectivity**: reindexing the edge family
along an equivalence preserves WPC (the touched-cell sum transports along the equivalence). -/
theorem weaklyPartitionConnected_comp_equiv {V : Type*} [Fintype V] [DecidableEq V]
    {n k : ℕ} (s : Finset V) (e : Fin n → Finset V) (σ : Equiv.Perm (Fin n))
    (h : WeaklyPartitionConnected k s e) :
    WeaklyPartitionConnected k s (e ∘ σ) := by
  intro P
  calc k * (P.parts.card - 1)
      ≤ ∑ i, ((touchedCells P (e i ∩ s)).card - 1) := h P
  _ = ∑ i, ((touchedCells P ((e ∘ σ) i ∩ s)).card - 1) :=
      (Equiv.sum_comp σ fun i => ((touchedCells P (e i ∩ s)).card - 1)).symm

end AGL24

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms AGL24.typeKey_injective
#print axioms AGL24.card_types_le
#print axioms AGL24.exists_typeOrdered_perm
#print axioms AGL24.weaklyPartitionConnected_comp_equiv
