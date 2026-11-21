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

/-- Tally for three independent projective subgroup copies. The four bounds on
good sites correspond to distinct involution classes, a repeated invariant
copy, exactly two in a noninvariant class, and one noninvariant class. -/
theorem subgroup_distance (good miss₁ miss₂ miss₃ : ℕ)
    (hD : 1073741820 ≤ good + miss₁ + miss₂ + miss₃)
    (cases : good ≤ 6 * 4993531 + 1 ∨ good ≤ 536870912 + 2 ∨
      good ≤ 268435455 + 5 * 4993531 + 1 ∨
      good ≤ 2 * 268435455 + 4993531 / 2 + 1) :
    534374144 ≤ miss₁ + miss₂ + miss₃ ∧
      (178124715 ≤ miss₁ ∨ 178124715 ≤ miss₂ ∨ 178124715 ≤ miss₃) := by
  omega

/-- The function-field gcd inequality for a translated power excludes companions
below 69,148 at the largest possible degree scale. -/
theorem translated_companion (a b : ℤ) (ha : 89478485 ≤ a)
    (hc : (a + b - 2) ^ 2 ≤ 108 * 1073741824 * (b + 1)) : 69148 ≤ b := by
  by_contra! hb
  nlinarith [sq_nonneg (a + b - 2 - 89547630)]

/-- With the source power based at zero and infinity the cutoff increases by one. -/
theorem unshifted_companion (a b : ℤ) (ha : 89478485 ≤ a)
    (hc : (a + b) ^ 2 ≤ 108 * 1073741824 * b) : 69149 ≤ b := by
  by_contra! hb
  nlinarith [sq_nonneg (a + b - 89547633)]

/-- Two successive exponent tests around the first multiple of the domain order. -/
theorem power_companion (a b k r : ℤ) (ha : 89478485 ≤ a) (hk : 4 ≤ k) (hK : k ≤ 12)
    (hn : 1073741824 = k * a + r) (hr : 0 ≤ r) (hr' : r < a)
    (h₁ : a - r ≤ (k - 1) * b) (h₂ : r ≤ k * b) : 4436951 ≤ b := by
  interval_cases k <;> omega

/-- The fifth-power tests for both companions bound any unshifted power degree. -/
theorem power_degree_ceiling (a b c : ℤ) (h : a + b + c = 268435455)
    (hb : 0 < b) (hc : 0 < c)
    (h₁ : a + b ≤ 5 * b + |5 * a - 1073741824|)
    (h₂ : a + c ≤ 5 * c + |5 * a - 1073741824|) : a ≤ 201326591 := by
  by_cases hm : 0 ≤ 5 * a - 1073741824
  · rw [abs_of_nonneg hm] at h₁ h₂
    omega
  · rw [abs_of_neg (by omega : 5 * a - 1073741824 < 0)] at h₁ h₂
    omega

#print axioms power_companion
#print axioms power_degree_ceiling
#print axioms translated_companion
#print axioms unshifted_companion
#print axioms subgroup_distance
#print axioms companion_degree
#print axioms restricted_image
#print axioms individual_image
#print axioms cube_cutoff

end ArkLib.ProximityGap.Frontier.QuarterSlopePowerBarrier
