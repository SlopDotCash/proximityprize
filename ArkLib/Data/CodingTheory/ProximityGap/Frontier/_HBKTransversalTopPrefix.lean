/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HBKTransversalRepProfile
import Mathlib.Data.List.Sort

/-!
# Realizing the ordered HBK prefix by transversal representatives

The canonical HBK profile sorts representation-count values and therefore forgets which
transversal representative supplied each occurrence.  This file restores witnesses without
discarding repeated values: sort the representatives lexicographically by decreasing count and
an arbitrary tie-break order, then take an initial segment.  Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.HBKTransversalTopPrefix

open scoped BigOperators
open ArkLib.ProximityGap.AdditiveEnergyRepBound
open HBKOrderedNatProfile HBKTransversalRepProfile

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable section

/-- Representatives sorted by decreasing representation count.  Insertion sort is stable, so
equal counts retain distinct representatives without needing an order on the ambient field. -/
def orderedRepresentatives (G T : Finset F) : List F :=
  T.toList.insertionSort fun x y => repCount G y ≤ repCount G x

/-- The first `k` representatives in HBK order, retaining distinct representatives even when
their representation counts agree. -/
def topPrefix (G T : Finset F) (k : ℕ) : Finset F := by
  classical
  exact ⟨↑((orderedRepresentatives G T).take k),
    ((List.perm_insertionSort (fun x y => repCount G y ≤ repCount G x) T.toList).nodup_iff.mpr
      T.nodup_toList).take⟩

@[simp] theorem orderedRepresentatives_length (G T : Finset F) :
    (orderedRepresentatives G T).length = T.card := by
  classical
  simp [orderedRepresentatives]

theorem orderedRepresentatives_nodup (G T : Finset F) :
    (orderedRepresentatives G T).Nodup := by
  classical
  exact (List.perm_insertionSort _ T.toList).nodup_iff.mpr T.nodup_toList

theorem topPrefix_subset (G T : Finset F) (k : ℕ) : topPrefix G T k ⊆ T := by
  classical
  intro x hx
  have hx' : x ∈ (orderedRepresentatives G T).take k := by
    simpa [topPrefix] using hx
  have hxord : x ∈ orderedRepresentatives G T := List.mem_of_mem_take hx'
  simpa [orderedRepresentatives] using hxord

theorem topPrefix_card (G T : Finset F) (k : ℕ) (hk : k ≤ T.card) :
    (topPrefix G T k).card = k := by
  classical
  rw [topPrefix, Finset.card_mk, Multiset.coe_card]
  simp [orderedRepresentatives_length, hk]

private theorem map_orderedRepresentatives (G T : Finset F) :
    (orderedRepresentatives G T).map (repCount G) =
      descendingList (transversalRepMultiset G T) := by
  classical
  let r : F → F → Prop := fun x y => repCount G y ≤ repCount G x
  letI : Std.Total r := ⟨fun x y => (Nat.le_total (repCount G x) (repCount G y)).symm⟩
  letI : IsTrans F r := ⟨fun _ _ _ hxy hyz => Nat.le_trans hyz hxy⟩
  apply List.Perm.eq_of_pairwise (le := fun a b : ℕ => b ≤ a)
  · omega
  · rw [List.pairwise_map]
    exact List.pairwise_insertionSort r _
  · exact descendingList_pairwise _
  · rw [← Multiset.coe_eq_coe]
    rw [Multiset.coe_eq_coe]
    have h₁ := (List.perm_insertionSort r T.toList).map (repCount G)
    have h₂ : List.Perm (descendingList (transversalRepMultiset G T))
        (T.toList.map (repCount G)) := by
      rw [← Multiset.coe_eq_coe]
      rw [show (↑(descendingList (transversalRepMultiset G T)) : Multiset ℕ) =
          transversalRepMultiset G T by simp [descendingList]]
      change Multiset.map (repCount G) T.val =
        Multiset.map (repCount G) (↑T.toList : Multiset F)
      exact congrArg (Multiset.map (repCount G)) (Finset.coe_toList T).symm
    simpa [r, orderedRepresentatives] using h₁.trans h₂.symm

/-- The count list of the realized prefix is exactly the canonical ordered count prefix. -/
theorem map_topPrefixList (G T : Finset F) (k : ℕ) :
    ((orderedRepresentatives G T).take k).map (repCount G) =
      (descendingList (transversalRepMultiset G T)).take k := by
  rw [List.map_take, map_orderedRepresentatives]

private theorem sum_range_getD_eq_sum_take (l : List ℕ) {k : ℕ} (hk : k ≤ l.length) :
    (∑ i ∈ Finset.range k, l.getD i 0) = (l.take k).sum := by
  induction k generalizing l with
  | zero => simp
  | succ k ih =>
      obtain ⟨x, xs, rfl⟩ := l.exists_cons_of_ne_nil (by intro h; simp [h] at hk)
      rw [Finset.sum_range_succ', List.take_succ_cons, List.sum_cons]
      simp only [List.getD_cons_zero, List.getD_cons_succ]
      rw [ih xs (by simpa using hk)]
      omega

/-- Summing `repCount` over the realized representative prefix gives exactly the canonical profile
prefix sum.  This is the numerical input to the HBK normalized incidence union. -/
theorem sum_topPrefix_repCount (G T : Finset F) {k : ℕ} (hk : k ≤ T.card) :
    (∑ u ∈ topPrefix G T k, repCount G u) =
      ∑ i ∈ Finset.range k, transversalRepProfile G T i := by
  classical
  have hlen : k ≤ (descendingList (transversalRepMultiset G T)).length := by
    simpa [descendingList_length] using hk
  rw [show (∑ u ∈ topPrefix G T k, repCount G u) =
      (((orderedRepresentatives G T).take k).map (repCount G)).sum by
    simp [topPrefix, Finset.sum_mk, Multiset.sum_coe]]
  rw [map_topPrefixList]
  symm
  simpa [transversalRepProfile, orderedProfile] using
    sum_range_getD_eq_sum_take (descendingList (transversalRepMultiset G T)) hlen

end

end ArkLib.ProximityGap.Frontier.HBKTransversalTopPrefix

#print axioms ArkLib.ProximityGap.Frontier.HBKTransversalTopPrefix.topPrefix_subset
#print axioms ArkLib.ProximityGap.Frontier.HBKTransversalTopPrefix.topPrefix_card
#print axioms ArkLib.ProximityGap.Frontier.HBKTransversalTopPrefix.map_topPrefixList
#print axioms ArkLib.ProximityGap.Frontier.HBKTransversalTopPrefix.sum_topPrefix_repCount
