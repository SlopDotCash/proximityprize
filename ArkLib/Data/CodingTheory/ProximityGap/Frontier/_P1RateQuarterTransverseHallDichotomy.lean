/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Combinatorics.Hall.Finite

/-!
# Hall dichotomy for the P1 common-base petal assignment

The collapsed-cluster injection needs a distinct coordinate from every petal.
Hall gives an exact alternative: either such representatives exist, or some
subfamily has a union smaller than its index set.  A uniform petal floor then
forces every obstruction to be larger than that floor.  At P1 this means a
failed assignment already contains at least `55,924,057` compressed pencils.
-/

set_option autoImplicit false

open Finset

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterTransverseHallDichotomy

attribute [local instance] Classical.propDecidable

/-- **Quantitative Hall split.**  A finite family of sets, each of size at
least `s`, either has distinct representatives or has a Hall-obstructing
subfamily of size strictly greater than `s`. -/
theorem exists_injective_representatives_or_large_compressed_subfamily
    {J U : Type} [Finite J] [DecidableEq J] [DecidableEq U]
    (petal : J → Finset U) (s : Nat)
    (hpetal : ∀ j, s ≤ (petal j).card) :
    (∃ coord : J → U, Function.Injective coord ∧
        ∀ j, coord j ∈ petal j) ∨
      ∃ B : Finset J,
        s < B.card ∧ (B.biUnion petal).card < B.card := by
  classical
  by_cases hHall : ∀ B : Finset J, B.card ≤ (B.biUnion petal).card
  · left
    exact (Finset.all_card_le_biUnion_card_iff_existsInjective' petal).mp hHall
  · right
    push_neg at hHall
    obtain ⟨B, hcompressed⟩ := hHall
    have hBne : B.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hB
      rw [hB] at hcompressed
      simp at hcompressed
    obtain ⟨j, hj⟩ := hBne
    have hsub : petal j ⊆ B.biUnion petal := by
      intro x hx
      exact Finset.mem_biUnion.mpr ⟨j, hj, hx⟩
    have hfloor : s ≤ (B.biUnion petal).card :=
      (hpetal j).trans (Finset.card_le_card hsub)
    exact ⟨B, lt_of_le_of_lt hfloor hcompressed, hcompressed⟩

/-- Literal Johnson-light P1 specialization.  Failure of a system of distinct
petal representatives produces more than `55,924,056` pencils compressed
into fewer coordinates than pencils. -/
theorem p1_johnsonLight_matching_or_compressed_55924057
    {J U : Type} [Finite J] [DecidableEq J] [DecidableEq U]
    (petal : J → Finset U)
    (hpetal : ∀ j, 55924056 ≤ (petal j).card) :
    (∃ coord : J → U, Function.Injective coord ∧
        ∀ j, coord j ∈ petal j) ∨
      ∃ B : Finset J,
        55924057 ≤ B.card ∧ (B.biUnion petal).card < B.card := by
  rcases exists_injective_representatives_or_large_compressed_subfamily
    petal 55924056 hpetal with hmatching | ⟨B, hB, hcompressed⟩
  · exact Or.inl hmatching
  · exact Or.inr ⟨B, by omega, hcompressed⟩

/-! ## Compressed-family load amplification -/

/-- **Incidence averaging behind the Hall obstruction.**  If `n` petals each
contribute at least `s` incidences, all incidences are supported on only `v<n`
coordinates, and every coordinate has load at most `L`, then necessarily
`s<L`.  This arithmetic socket accepts the existing petal incidence identity
and a maximum-load upper bound without duplicating their finite-set API. -/
theorem load_gt_floor_of_compressed_incidence
    (n v s total L : Nat)
    (hs : 0 < s) (hcompressed : v < n)
    (hlower : n * s ≤ total) (hupper : total ≤ v * L) :
    s < L := by
  by_contra hnot
  have hL : L ≤ s := Nat.le_of_not_gt hnot
  have hmul : v * L ≤ v * s := Nat.mul_le_mul_left v hL
  have hstrict : v * s < n * s :=
    Nat.mul_lt_mul_of_pos_right hcompressed hs
  omega

/-- Literal P1 consequence: any compressed Johnson-light petal family whose
incidences are bounded by `v*L` has maximum load at least `55,924,057`. -/
theorem p1_compressed_incidence_forces_load_55924057
    (n v total L : Nat) (hcompressed : v < n)
    (hlower : n * 55924056 ≤ total) (hupper : total ≤ v * L) :
    55924057 ≤ L := by
  have hload := load_gt_floor_of_compressed_incidence
    n v 55924056 total L (by omega) hcompressed hlower hupper
  omega

end ArkLib.ProximityGap.Frontier.P1RateQuarterTransverseHallDichotomy

open ArkLib.ProximityGap.Frontier.P1RateQuarterTransverseHallDichotomy

#print axioms exists_injective_representatives_or_large_compressed_subfamily
#print axioms p1_johnsonLight_matching_or_compressed_55924057
#print axioms load_gt_floor_of_compressed_incidence
#print axioms p1_compressed_incidence_forces_load_55924057
