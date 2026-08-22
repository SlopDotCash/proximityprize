/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Multiset.Sort

/-!
# Canonical decreasing profile of a natural-number multiset

HBK orders the nonzero coset-intersection counts decreasingly, with multiplicity.  This file defines
that ordering abstractly for any `Multiset ℕ`, avoiding an arbitrary order on the underlying field
or coset representatives.

The profile is canonical up to equal entries, antitone, and zero after the multiset cardinality.
It is the container layer used to turn the actual multiset of HBK fiber sizes into the profile
consumed by production cap majorization. Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.HBKOrderedNatProfile

open scoped BigOperators

/-- Descending list of a natural-number multiset. -/
def descendingList (s : Multiset ℕ) : List ℕ := s.sort (fun a b => b ≤ a)

/-- Descending profile, padded by zero beyond the multiset cardinality. -/
def orderedProfile (s : Multiset ℕ) (i : ℕ) : ℕ := (descendingList s).getD i 0

@[simp] theorem descendingList_length (s : Multiset ℕ) :
    (descendingList s).length = s.card := by
  simp [descendingList]

theorem descendingList_pairwise (s : Multiset ℕ) :
    (descendingList s).Pairwise (fun a b => b ≤ a) := by
  exact Multiset.pairwise_sort _ _

/-- The profile is zero after all multiset entries have been exhausted. -/
theorem orderedProfile_eq_zero_of_card_le
    (s : Multiset ℕ) {i : ℕ} (hi : s.card ≤ i) : orderedProfile s i = 0 := by
  apply List.getD_eq_default
  simpa [descendingList_length] using hi

/-- The multiplicity-aware ordered profile is decreasing, including at the zero-padding boundary. -/
theorem orderedProfile_antitone_succ (s : Multiset ℕ) (i : ℕ) :
    orderedProfile s (i + 1) ≤ orderedProfile s i := by
  by_cases hnext : i + 1 < (descendingList s).length
  · have hi : i < (descendingList s).length := by omega
    let fi : Fin (descendingList s).length := ⟨i, hi⟩
    let fj : Fin (descendingList s).length := ⟨i + 1, hnext⟩
    have hfij : fi < fj := by simp [fi, fj]
    have hrel := (descendingList_pairwise s).rel_get_of_lt hfij
    rw [orderedProfile, orderedProfile,
      List.getD_eq_get (descendingList s) 0 fj,
      List.getD_eq_get (descendingList s) 0 fi]
    exact hrel
  · have hz : orderedProfile s (i + 1) = 0 := by
      apply orderedProfile_eq_zero_of_card_le
      rw [← descendingList_length]
      omega
    rw [hz]
    exact Nat.zero_le _

/-- The padded ordered profile is globally antitone. -/
theorem orderedProfile_antitone (s : Multiset ℕ) : Antitone (orderedProfile s) := by
  intro i j hij
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih => exact (orderedProfile_antitone_succ s j).trans ih

/-- A profile padded to any `N` beyond the multiset cardinality has zero boundary. -/
theorem orderedProfile_boundary
    (s : Multiset ℕ) {N : ℕ} (hN : s.card ≤ N) : orderedProfile s N = 0 :=
  orderedProfile_eq_zero_of_card_le s hN

private theorem sum_range_getD_sq (l : List ℕ) :
    (∑ i ∈ Finset.range l.length, (l.getD i 0) ^ 2) =
      (l.map (fun x => x ^ 2)).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons]
      simp only [List.getD_cons_zero, List.getD_cons_succ]
      rw [ih]
      omega

private theorem sum_range_getD (l : List ℕ) :
    (∑ i ∈ Finset.range l.length, l.getD i 0) = l.sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      rw [List.length_cons, Finset.sum_range_succ', List.sum_cons]
      simp only [List.getD_cons_zero, List.getD_cons_succ]
      rw [ih]
      omega

/-- Sorting and zero-padding preserve total mass. -/
theorem sum_orderedProfile (s : Multiset ℕ) :
    (∑ i ∈ Finset.range s.card, orderedProfile s i) = s.sum := by
  rw [← descendingList_length]
  simp only [orderedProfile]
  rw [sum_range_getD]
  have heq : (↑(descendingList s) : Multiset ℕ) = s := by
    simp [descendingList]
  exact congrArg Multiset.sum heq

/-- If the total mass is strictly below `N`, then the `N`-th decreasing entry is already zero.
This supplies a sharper zero boundary than the raw multiset cardinality when most entries vanish. -/
theorem orderedProfile_eq_zero_of_sum_lt
    (s : Multiset ℕ) {N : ℕ} (hN : N < s.card) (hsum : s.sum < N) :
    orderedProfile s N = 0 := by
  by_contra hne
  have hpos : 0 < orderedProfile s N := Nat.pos_of_ne_zero hne
  have hlower : N + 1 ≤ ∑ i ∈ Finset.range (N + 1), orderedProfile s i := by
    calc
      N + 1 = ∑ _i ∈ Finset.range (N + 1), 1 := by simp
      _ ≤ ∑ i ∈ Finset.range (N + 1), orderedProfile s i := by
        apply Finset.sum_le_sum
        intro i hi
        exact (Nat.succ_le_iff.mpr hpos).trans
          (orderedProfile_antitone s (by
            have := Finset.mem_range.mp hi
            omega))
  have hupper : (∑ i ∈ Finset.range (N + 1), orderedProfile s i) ≤ s.sum := by
    rw [← sum_orderedProfile s]
    exact Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
  omega

/-- Sorting and zero-padding preserve the squared mass of the multiset exactly. -/
theorem sum_orderedProfile_sq (s : Multiset ℕ) :
    (∑ i ∈ Finset.range s.card, (orderedProfile s i) ^ 2) =
      (s.map (fun x => x ^ 2)).sum := by
  rw [← descendingList_length]
  simp only [orderedProfile]
  rw [sum_range_getD_sq]
  have heq : (↑(descendingList s) : Multiset ℕ) = s := by
    simp [descendingList]
  have hmap := congrArg (Multiset.map (fun x : ℕ => x ^ 2)) heq
  have hsum := congrArg Multiset.sum hmap
  exact hsum

end ArkLib.ProximityGap.Frontier.HBKOrderedNatProfile

#print axioms ArkLib.ProximityGap.Frontier.HBKOrderedNatProfile.orderedProfile_antitone_succ
#print axioms ArkLib.ProximityGap.Frontier.HBKOrderedNatProfile.orderedProfile_boundary
#print axioms ArkLib.ProximityGap.Frontier.HBKOrderedNatProfile.orderedProfile_eq_zero_of_sum_lt
#print axioms ArkLib.ProximityGap.Frontier.HBKOrderedNatProfile.sum_orderedProfile_sq
#print axioms ArkLib.ProximityGap.Frontier.HBKOrderedNatProfile.sum_orderedProfile
