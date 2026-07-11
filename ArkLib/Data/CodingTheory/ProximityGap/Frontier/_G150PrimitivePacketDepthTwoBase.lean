/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G149PrimitivePacketChargeTransfer

/-!
# G150: primitive packet base classification at depths one and two

The primitive-packet programme begins with a characteristic-free rigidity fact.  A balanced core
cannot have depth one: equality of singleton sums identifies the two elements, contradicting
support disjointness.  Consequently every primitive packet has depth at least two.

Conversely, every balanced depth-two core is primitive.  Any proper balanced subcore would have
positive depth strictly below two, hence depth one, which is impossible.  Thus the depth-two leaves
are exactly the disjoint additive parallelograms counted by the ordinary additive-energy layer.

Feeding the universal minimum depth `2` into G149 shows that a depth-`t` core has at most `t/2`
primitive packets, in the exact form `2 * leafCount ≤ t`.

Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G150PrimitivePacketDepthTwoBase

open ArkLib.ProximityGap.Frontier.G147ConnectedBalancedCoreRecursion
open ArkLib.ProximityGap.Frontier.G148FinitePrimitivePacketTree
open ArkLib.ProximityGap.Frontier.G149PrimitivePacketChargeTransfer

variable {F : Type*} [AddCommGroup F] [DecidableEq F]

/-- No nonempty disjoint equal-sum core has singleton depth. -/
theorem not_balancedCore_of_left_card_eq_one {c : Finset F × Finset F}
    (hcard : c.1.card = 1) : ¬ IsBalancedCore c := by
  intro hc
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
  have hrightCard : c.2.card = 1 := hc.2.1 ▸ hcard
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hrightCard
  have hab : a = b := by
    simpa [ha, hb] using hc.2.2.2
  subst b
  have haL : a ∈ c.1 := by simp [ha]
  have haR : a ∈ c.2 := by simp [hb]
  exact (Finset.disjoint_left.mp hc.2.2.1) haL haR

/-- Every balanced core, hence every primitive packet, starts at depth at least two. -/
theorem balancedCore_two_le_left_card {c : Finset F × Finset F}
    (hc : IsBalancedCore c) : 2 ≤ c.1.card := by
  have hpos : 0 < c.1.card := Finset.card_pos.mpr hc.1
  by_contra h
  have hone : c.1.card = 1 := by omega
  exact not_balancedCore_of_left_card_eq_one hone hc

theorem primitiveCore_two_le_left_card {c : Finset F × Finset F}
    (hc : IsPrimitiveBalancedCore c) : 2 ≤ c.1.card :=
  balancedCore_two_le_left_card hc.1

/-- **Exact depth-two classification.** At depth two, balanced is equivalent to primitive. -/
theorem primitiveBalancedCore_iff_balanced_of_left_card_eq_two
    {c : Finset F × Finset F} (hcard : c.1.card = 2) :
    IsPrimitiveBalancedCore c ↔ IsBalancedCore c := by
  constructor
  · exact fun h => h.1
  · intro hc
    refine ⟨hc, ?_⟩
    rintro ⟨d, hd⟩
    have hdlt : d.1.card < c.1.card := properSubcore_left_card_lt hd
    have hdmin : 2 ≤ d.1.card := balancedCore_two_le_left_card hd.1
    omega

/-- **G150 capstone.** Every primitive-packet tree has at most half as many leaves as root depth. -/
theorem two_mul_leafCount_le_rootDepth {c : Finset F × Finset F}
    (T : PrimitivePacketTree c) : 2 * T.leafCount ≤ c.1.card := by
  exact mul_leafCount_le_rootDepth 2
    (fun _ hc => primitiveCore_two_le_left_card hc) T

/-- Existential packet decomposition with the sharpened universal leaf-count invariant. -/
theorem exists_primitivePacketTree_two_mul_leafCount_le
    (c : Finset F × Finset F) (hc : IsBalancedCore c) :
    ∃ T : PrimitivePacketTree c, 2 * T.leafCount ≤ c.1.card := by
  obtain ⟨T⟩ := exists_primitivePacketTree c hc
  exact ⟨T, two_mul_leafCount_le_rootDepth T⟩

#print axioms not_balancedCore_of_left_card_eq_one
#print axioms balancedCore_two_le_left_card
#print axioms primitiveCore_two_le_left_card
#print axioms primitiveBalancedCore_iff_balanced_of_left_card_eq_two
#print axioms two_mul_leafCount_le_rootDepth
#print axioms exists_primitivePacketTree_two_mul_leafCount_le

end ArkLib.ProximityGap.Frontier.G150PrimitivePacketDepthTwoBase
