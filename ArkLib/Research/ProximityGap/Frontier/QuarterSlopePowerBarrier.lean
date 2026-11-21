/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Tactic

/-! # Image and degree restrictions on the quarter-rate direction maps -/

set_option autoImplicit false
namespace ArkLib.ProximityGap.Frontier.QuarterSlopePowerBarrier

/-- If the orbit map on all double sites loses at most one value, its restriction
to any collection of double sites also loses at most one value. -/
theorem restricted_image {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (S D : Finset α) (hS : S ⊆ D)
    (hD : D.card ≤ (D.image f).card + 1) : S.card ≤ (S.image f).card + 1 := by
  have hcover : D.image f ⊆ S.image f ∪ (D \ S).image f := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    by_cases hs : a ∈ S
    · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hs)
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_sdiff.mpr ⟨ha,hs⟩))
  have hcard := (Finset.card_le_card hcover).trans (Finset.card_union_le ..)
  have hdiff := Finset.card_image_le (f := f) (s := D \ S)
  rw [Finset.card_sdiff_of_subset hS] at hdiff
  have := Finset.card_le_card hS
  omega

/-- For a slope of degree at least two the participating sites force more than
half the length in distinct direction orbits. -/
theorem individual_image (d m image : ℕ) (hm : 2 ≤ m)
    (h : 2*(d+m) ≤ image+1) : 2*(d+1) < image := by omega

/-- The exact integer transition point for the non-toric (1,1) graph estimate. -/
theorem cube_cutoff (s : ℕ) : s^3 ≤ 108*1073741824^2 ↔ s ≤ 4993531 := by
  constructor
  · intro hs
    by_contra! h
    have h' := Nat.pow_le_pow_left (show 4993532 ≤ s by omega) 3
    norm_num at h' hs
    omega
  · intro hs
    exact (Nat.pow_le_pow_left hs 3).trans (by decide)

/-- A power slope of at least one third of the total degree cannot have a
companion of degree at most 75 satisfying the graph bound. -/
theorem companion_degree (a b : ℕ) (ha : 89478485 ≤ a)
    (hc : (a+b)^3 ≤ 108*b^2*1073741824^2) : 76 ≤ b := by
  by_contra! hb
  have h₁ := Nat.pow_le_pow_left (show 89478485 ≤ a+b by omega) 3
  have h₂ := Nat.pow_le_pow_left (show b ≤ 75 by omega) 2
  norm_num at h₁ h₂ hc
  omega

#print axioms companion_degree
#print axioms restricted_image
#print axioms individual_image
#print axioms cube_cutoff

end ArkLib.ProximityGap.Frontier.QuarterSlopePowerBarrier
