/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.NegationClosedPairingCount

/-!
# R387: matching topology in a nonzero four-sum fiber

Compare two four-tuples with the same sum and concatenate the first tuple with the negation of the
second. In characteristic zero, Lam--Leung supplies a perfect antipodal matching of these eight
slots. This file proves the finite topology needed for the R386 representation bound: if the sum
of the first four slots is nonzero, at most one matching edge can lie wholly inside those slots.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open Finset
open ArkLib.ProximityGap.NegationClosedWalk

namespace ArkLib.ProximityGap.Frontier.R387NonzeroFourFiberMatchingTopology

/-- The variable half of the eight relation slots. -/
def leftFour : Finset (Fin (2 * 4)) := Finset.univ.filter (fun i => (i : ℕ) < 4)

/-- One representative (`i < sigma i`) for each matching edge wholly inside `leftFour`. -/
def internalLeftEdges (σ : Equiv.Perm (Fin (2 * 4))) : Finset (Fin (2 * 4)) :=
  leftFour.filter (fun i => (i : ℕ) < (σ i : ℕ) ∧ σ i ∈ leftFour)

theorem leftFour_card : leftFour.card = 4 := by decide

private theorem internal_image_disjoint (σ : Equiv.Perm (Fin (2 * 4))) (hσ : IsPairing σ) :
    Disjoint (internalLeftEdges σ) ((internalLeftEdges σ).image σ) := by
  rw [Finset.disjoint_left]
  intro x hx hximg
  obtain ⟨e, he, hσe⟩ := Finset.mem_image.mp hximg
  have hxlt : (x : ℕ) < (σ x : ℕ) := (Finset.mem_filter.mp hx).2.1
  have helt : (e : ℕ) < (σ e : ℕ) := (Finset.mem_filter.mp he).2.1
  have hback : σ x = e := by
    rw [← hσe]
    exact hσ.1 e
  rw [hback] at hxlt
  have hval := congrArg Fin.val hσe
  omega

private theorem internal_union_subset_left (σ : Equiv.Perm (Fin (2 * 4))) :
    internalLeftEdges σ ∪ (internalLeftEdges σ).image σ ⊆ leftFour := by
  intro x hx
  rw [Finset.mem_union] at hx
  rcases hx with hx | hx
  · exact (Finset.mem_filter.mp hx).1
  · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_filter.mp he).2.2

/-- A matching on eight slots has at most two edges internal to a fixed four-slot half. -/
theorem internalLeftEdges_card_le_two (σ : Equiv.Perm (Fin (2 * 4))) (hσ : IsPairing σ) :
    (internalLeftEdges σ).card ≤ 2 := by
  have hdisj := internal_image_disjoint σ hσ
  have hsubset := Finset.card_le_card (internal_union_subset_left σ)
  rw [Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective (internalLeftEdges σ) σ.injective,
    leftFour_card] at hsubset
  omega

/-- If both possible internal edges occur, the matching preserves all of `leftFour`. -/
theorem maps_leftFour_of_internalLeftEdges_card_eq_two
    (σ : Equiv.Perm (Fin (2 * 4))) (hσ : IsPairing σ)
    (hcard : (internalLeftEdges σ).card = 2) :
    ∀ i ∈ leftFour, σ i ∈ leftFour := by
  have hdisj := internal_image_disjoint σ hσ
  have hsubset := internal_union_subset_left σ
  have hunioncard :
      (internalLeftEdges σ ∪ (internalLeftEdges σ).image σ).card = 4 := by
    rw [Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective (internalLeftEdges σ) σ.injective, hcard]
  have heq : internalLeftEdges σ ∪ (internalLeftEdges σ).image σ = leftFour :=
    Finset.eq_of_subset_of_card_le hsubset (by rw [hunioncard, leftFour_card])
  intro i hi
  rw [← heq, Finset.mem_union] at hi
  rcases hi with hi | hi
  · exact (Finset.mem_filter.mp hi).2.2
  · obtain ⟨e, he, hσe⟩ := Finset.mem_image.mp hi
    have hback : σ i = e := by
      rw [← hσe]
      exact hσ.1 e
    rw [hback]
    exact (Finset.mem_filter.mp he).1

/-- An antipodal matching that preserves `leftFour` forces the left values to sum to zero. -/
theorem sum_leftFour_eq_zero_of_maps
    {F : Type*} [Field F] [DecidableEq F]
    (c : Fin (2 * 4) → F) (σ : Equiv.Perm (Fin (2 * 4))) (hσ : IsPairing σ)
    (hpair : ∀ i, c (σ i) = -c i)
    (hmaps : ∀ i ∈ leftFour, σ i ∈ leftFour) :
    ∑ i ∈ leftFour, c i = 0 := by
  refine Finset.sum_involution (g := fun i _ => σ i) ?_ ?_ ?_ ?_
  · intro i hi
    rw [hpair i, add_neg_cancel]
  · intro i hi _ hfix
    exact (hσ.2 i) hfix
  · intro i hi
    exact hmaps i hi
  · intro i hi
    exact hσ.1 i

/-- **Nonzero-fiber topology.** A nonzero four-sum leaves at most one internal variable edge. -/
theorem internalLeftEdges_card_le_one_of_sum_ne_zero
    {F : Type*} [Field F] [DecidableEq F]
    (c : Fin (2 * 4) → F) (σ : Equiv.Perm (Fin (2 * 4))) (hσ : IsPairing σ)
    (hpair : ∀ i, c (σ i) = -c i)
    (hsum : ∑ i ∈ leftFour, c i ≠ 0) :
    (internalLeftEdges σ).card ≤ 1 := by
  have hle := internalLeftEdges_card_le_two σ hσ
  by_contra h
  have hcard : (internalLeftEdges σ).card = 2 := by omega
  exact hsum (sum_leftFour_eq_zero_of_maps c σ hσ hpair
    (maps_leftFour_of_internalLeftEdges_card_eq_two σ hσ hcard))

end ArkLib.ProximityGap.Frontier.R387NonzeroFourFiberMatchingTopology

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R387NonzeroFourFiberMatchingTopology.internalLeftEdges_card_le_one_of_sum_ne_zero
