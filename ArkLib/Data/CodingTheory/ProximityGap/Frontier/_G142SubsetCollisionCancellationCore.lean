/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G141OffDiagonalAccidentIdentity

/-!
# G142: canonical cancellation cores of subset-sum accidents

Every distinct equal-sum pair of equal-cardinality finite subsets canonically cancels its
intersection.  The residual endpoints `S \ T` and `T \ S` are disjoint, have the same positive
cardinality, and retain equal sums.  Their common size is the cancellation depth.

If the original endpoints overlap, this depth is strictly below the original cardinality; if they
are disjoint, it is the full depth.  This is the structural weld needed to stratify G141's literal
off-diagonal accident census by the existing `depthFiber` convention.

Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G142SubsetCollisionCancellationCore

open scoped BigOperators

variable {A : Type*} [AddCommGroup A] [DecidableEq A]

/-- Cancelling the common intersection preserves equality of subset sums. -/
theorem sum_sdiff_eq_sum_sdiff_of_sum_eq
    {S T : Finset A} (hsum : ∑ x ∈ S, x = ∑ x ∈ T, x) :
    ∑ x ∈ S \ T, x = ∑ x ∈ T \ S, x := by
  have hST : S \ T = S \ (S ∩ T) := by
    ext x
    simp
  have hTS : T \ S = T \ (S ∩ T) := by
    ext x
    simp [and_comm]
  rw [hST, hTS, Finset.sum_sdiff_eq_sub Finset.inter_subset_left,
    Finset.sum_sdiff_eq_sub Finset.inter_subset_right, hsum]

/-- The two cancellation cores are support-disjoint. -/
theorem disjoint_sdiff_sdiff (S T : Finset A) : Disjoint (S \ T) (T \ S) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hy).1

/-- Equal-size endpoints leave equal-size cancellation cores. -/
theorem card_sdiff_eq_card_sdiff_of_card_eq
    {S T : Finset A} (hcard : S.card = T.card) :
    (S \ T).card = (T \ S).card := by
  rw [Finset.card_sdiff, Finset.card_sdiff, Finset.inter_comm S T, hcard]

/-- A distinct equal-cardinality pair has positive cancellation depth. -/
theorem card_sdiff_pos_of_ne_of_card_eq
    {S T : Finset A} (hne : S ≠ T) (hcard : S.card = T.card) :
    0 < (S \ T).card := by
  rw [Finset.card_pos]
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at h
  apply hne
  exact Finset.eq_of_subset_of_card_le h (by omega)

/-- Overlap forces the cancellation depth strictly below the original endpoint size. -/
theorem card_sdiff_lt_of_inter_nonempty
    {S T : Finset A} (hoverlap : (S ∩ T).Nonempty) :
    (S \ T).card < S.card := by
  rw [Finset.card_sdiff]
  have hpos : 0 < (S ∩ T).card := Finset.card_pos.mpr hoverlap
  rw [Finset.inter_comm] at hpos
  have hle : (T ∩ S).card ≤ S.card :=
    Finset.card_le_card Finset.inter_subset_right
  omega

/-- Disjoint endpoints are exactly the full-depth case. -/
theorem card_sdiff_eq_card_iff_disjoint (S T : Finset A) :
    (S \ T).card = S.card ↔ Disjoint S T := by
  rw [Finset.disjoint_iff_inter_eq_empty]
  constructor
  · intro h
    have hcard : (S ∩ T).card = 0 := by
      rw [Finset.card_sdiff] at h
      rw [Finset.inter_comm] at h
      have hle : (S ∩ T).card ≤ S.card :=
        Finset.card_le_card Finset.inter_subset_left
      omega
    exact Finset.card_eq_zero.mp hcard
  · intro h
    rw [Finset.card_sdiff, Finset.inter_comm, h]
    simp

/-- **Canonical cancellation-core package.** Every distinct equal-sum pair of `r`-subsets yields
disjoint equal-sum cores of a common positive depth at most `r`; overlap makes it strictly smaller. -/
theorem collision_cancellation_core
    {S T : Finset A} {r : ℕ}
    (hScard : S.card = r) (hTcard : T.card = r) (hne : S ≠ T)
    (hsum : ∑ x ∈ S, x = ∑ x ∈ T, x) :
    Disjoint (S \ T) (T \ S) ∧
      (∑ x ∈ S \ T, x = ∑ x ∈ T \ S, x) ∧
      (S \ T).card = (T \ S).card ∧
      0 < (S \ T).card ∧ (S \ T).card ≤ r ∧
      ((S ∩ T).Nonempty → (S \ T).card < r) := by
  have hcard : S.card = T.card := hScard.trans hTcard.symm
  refine ⟨disjoint_sdiff_sdiff S T, sum_sdiff_eq_sum_sdiff_of_sum_eq hsum,
    card_sdiff_eq_card_sdiff_of_card_eq hcard,
    card_sdiff_pos_of_ne_of_card_eq hne hcard, ?_, ?_⟩
  · rw [← hScard]
    exact Finset.card_le_card (Finset.sdiff_subset)
  · intro hoverlap
    simpa [← hScard] using card_sdiff_lt_of_inter_nonempty hoverlap

#print axioms sum_sdiff_eq_sum_sdiff_of_sum_eq
#print axioms card_sdiff_eq_card_sdiff_of_card_eq
#print axioms card_sdiff_pos_of_ne_of_card_eq
#print axioms card_sdiff_lt_of_inter_nonempty
#print axioms card_sdiff_eq_card_iff_disjoint
#print axioms collision_cancellation_core

end ArkLib.ProximityGap.Frontier.G142SubsetCollisionCancellationCore
