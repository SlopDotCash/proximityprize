/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.ReciprocalFiberLists

/-! # Keeping the sign of a reciprocal locator at a dyadic root of unity

Choose a square root of the quotient generator and a compatible square root of
minus one. These identities recover the exact locator from its exponent sum and
leaf vector. Two disjoint fibers can also accommodate the common vanishing roots
and the extra agreements prescribed separately at either anchor.
-/

namespace ProximityGap.SignedReciprocalLists

open Finset
variable {F J : Type*} [Field F]

/-- The signed contribution of one inverse pair at a square root of its element. -/
def weight (i x : F) : F := i * (x⁻¹ - x)

/-- The two orientations of an inverse pair have identical weight. -/
theorem reverse_weight (i x : F) : weight i (-x⁻¹) = weight i x := by
  simp [weight, sub_eq_add_neg, add_comm]

/-- The two children of a doubling node multiply to its weight. -/
theorem double_weight (i x : F) (hi : i^2 = -1) (hx : x ≠ 0) :
    weight i x * weight i (i / x) = weight i (x^2) := by
  have hn : i ≠ 0 := by intro h; simp [h] at hi
  unfold weight
  field_simp
  linear_combination (x^2 - 1) * hi

/-- The character of the orientation restores the sign before multiplying over roots. -/
theorem locator_factor (i x : F) (hi : i^2 = -1) (hx : x ≠ 0) :
    1 - x^2 = (-i * x) * weight i x := by
  unfold weight
  field_simp
  linear_combination (1-x^2) * hi

/-- Exact signed locator, before expanding the weights down the doubling tree. -/
theorem signed_locator (s : Finset J) (z : J → F) (i : F) (hi : i^2 = -1)
    (hz : ∀ j ∈ s, z j ≠ 0) :
    (∏ j ∈ s, (1 - (z j)^2)) = (-i)^s.card * (∏ j ∈ s, z j) * ∏ j ∈ s, weight i (z j) := by
  rw [prod_congr rfl (fun j hj => locator_factor i (z j) hi (hz j hj)), prod_mul_distrib,
    prod_mul_distrib, prod_const]

/-- Reserve any prescribed numbers of free sites on each fiber. The common
vanishing set occupies the remaining slots across the union. -/
theorem reserve_across_anchors [DecidableEq J] (p m : Finset J) (hpm : Disjoint p m)
    (u v w : ℕ) (hu : u ≤ p.card) (hv : v ≤ m.card) (hw : u+v+w ≤ p.card+m.card) :
    ∃ a ⊆ p, ∃ b ⊆ m, ∃ c ⊆ (p ∪ m) \ (a ∪ b), a.card = u ∧ b.card = v ∧ c.card = w := by
  obtain ⟨a, ha, hca⟩ := exists_subset_card_eq hu
  obtain ⟨b, hb, hcb⟩ := exists_subset_card_eq hv
  have hab := hpm.mono ha hb
  have huab : a ∪ b ⊆ p ∪ m := union_subset_union ha hb
  have hc : w ≤ ((p ∪ m) \ (a ∪ b)).card := by
    rw [card_sdiff_of_subset huab, card_union_of_disjoint hpm, card_union_of_disjoint hab, hca, hcb]
    omega
  obtain ⟨c, hsc, hcc⟩ := exists_subset_card_eq hc
  exact ⟨a,ha,b,hb,c,hsc,hca,hcb,hcc⟩

end ProximityGap.SignedReciprocalLists

#print axioms ProximityGap.SignedReciprocalLists.signed_locator
#print axioms ProximityGap.SignedReciprocalLists.double_weight
#print axioms ProximityGap.SignedReciprocalLists.reserve_across_anchors
