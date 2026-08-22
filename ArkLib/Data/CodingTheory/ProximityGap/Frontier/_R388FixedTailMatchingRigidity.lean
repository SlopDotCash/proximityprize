/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R387NonzeroFourFiberMatchingTopology

/-!
# R388: one coordinate determines a fixed-tail nonzero matching cell

R387 shows that a nonzero four-sum permits at most one matching edge wholly inside the variable
four slots.  Choose the lower endpoint of that edge when it exists (and slot zero otherwise).
For two antipodally matched eight-tuples with the same fixed right half, agreement at this canonical
coordinate forces agreement on the entire left half.  This is the injection needed to bound each
fixed-reference matching cell by the subgroup cardinality.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open Finset
open ArkLib.ProximityGap.NegationClosedWalk

namespace ArkLib.ProximityGap.Frontier.R388FixedTailMatchingRigidity

open ArkLib.ProximityGap.Frontier.R387NonzeroFourFiberMatchingTopology

/-- Canonical free coordinate: the lower endpoint of the unique possible internal left edge. -/
def freeCoord (σ : Equiv.Perm (Fin (2 * 4))) : Fin (2 * 4) :=
  if h : (internalLeftEdges σ).Nonempty then (internalLeftEdges σ).min' h else ⟨0, by omega⟩

/-- The canonical coordinate always belongs to the variable half. -/
theorem freeCoord_mem_leftFour (σ : Equiv.Perm (Fin (2 * 4))) : freeCoord σ ∈ leftFour := by
  classical
  unfold freeCoord
  split
  · rename_i h
    have hm := Finset.min'_mem (internalLeftEdges σ) h
    exact (Finset.mem_filter.mp hm).1
  · simp [leftFour]

private theorem eq_freeCoord_of_mem_internal
    (σ : Equiv.Perm (Fin (2 * 4))) (hcard : (internalLeftEdges σ).card ≤ 1)
    {i : Fin (2 * 4)} (hi : i ∈ internalLeftEdges σ) : i = freeCoord σ := by
  classical
  have hne : (internalLeftEdges σ).Nonempty := ⟨i, hi⟩
  have hmin : (internalLeftEdges σ).min' hne ∈ internalLeftEdges σ :=
    Finset.min'_mem _ _
  have heq := Finset.card_le_one.mp hcard i hi ((internalLeftEdges σ).min' hne) hmin
  unfold freeCoord
  rw [dif_pos hne]
  exact heq

/-- Every variable slot is either cross-matched to the fixed right half or belongs to the unique
internal edge represented by `freeCoord`. -/
theorem left_controlled
    (σ : Equiv.Perm (Fin (2 * 4))) (hσ : IsPairing σ)
    (hcard : (internalLeftEdges σ).card ≤ 1) {i : Fin (2 * 4)} (hi : i ∈ leftFour) :
    σ i ∉ leftFour ∨ i = freeCoord σ ∨ σ i = freeCoord σ := by
  by_cases hmate : σ i ∈ leftFour
  · right
    rcases lt_trichotomy i (σ i) with hlt | heq | hgt
    · left
      apply eq_freeCoord_of_mem_internal σ hcard
      rw [internalLeftEdges, Finset.mem_filter]
      exact ⟨hi, hlt, hmate⟩
    · exact absurd heq.symm (hσ.2 i)
    · right
      apply eq_freeCoord_of_mem_internal σ hcard
      rw [internalLeftEdges, Finset.mem_filter]
      refine ⟨hmate, ?_, ?_⟩
      · simpa only [hσ.1 i] using hgt
      · simpa only [hσ.1 i] using hi
  · exact Or.inl hmate

/-- **Fixed-tail rigidity.** One canonical coordinate determines all four variable values. -/
theorem eq_on_leftFour_of_eq_freeCoord_of_eq_on_right
    {F : Type*} [Field F] [DecidableEq F]
    (c c' : Fin (2 * 4) → F) (σ : Equiv.Perm (Fin (2 * 4))) (hσ : IsPairing σ)
    (hcard : (internalLeftEdges σ).card ≤ 1)
    (hpair : ∀ i, c (σ i) = -c i) (hpair' : ∀ i, c' (σ i) = -c' i)
    (hright : ∀ i, i ∉ leftFour → c i = c' i)
    (hfree : c (freeCoord σ) = c' (freeCoord σ)) :
    ∀ i ∈ leftFour, c i = c' i := by
  intro i hi
  rcases left_controlled σ hσ hcard hi with hcross | hself | hmate
  · have hright' := hright (σ i) hcross
    have hc := hpair i
    have hc' := hpair' i
    apply neg_injective
    rw [← hc, ← hc', hright']
  · simpa [hself] using hfree
  · have hc := hpair i
    have hc' := hpair' i
    rw [hmate] at hc hc'
    apply neg_injective
    rw [← hc, ← hc', hfree]

end ArkLib.ProximityGap.Frontier.R388FixedTailMatchingRigidity

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R388FixedTailMatchingRigidity.eq_on_leftFour_of_eq_freeCoord_of_eq_on_right
