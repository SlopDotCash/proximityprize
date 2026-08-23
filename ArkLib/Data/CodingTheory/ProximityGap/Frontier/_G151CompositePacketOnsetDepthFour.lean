/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G150PrimitivePacketDepthTwoBase

/-!
# G151: composite packet onset is depth four

G150 proves that every balanced packet has depth at least two.  Combining that with the exact G147
split immediately locates the first possible composite packet: a nonprimitive balanced core has two
balanced children, so its depth is at least four.

Consequently every balanced core of depth two or three is primitive.  At depth four the split case
is completely rigid at the level of sizes: it is exactly a disjoint union of two depth-two balanced
cores, hence two additive parallelogram packets by G150.  No characteristic-`p` arithmetic enters
this classification.

Thus genuinely connected characteristic-`p` packets occur already at depth three, but *composite*
connected-packet assemblies cannot occur before depth four.  This separates the depth-three
primitive census from the HBK-controlled two-parallelogram depth-four branch.

Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G151CompositePacketOnsetDepthFour

open ArkLib.ProximityGap.Frontier.G147ConnectedBalancedCoreRecursion
open ArkLib.ProximityGap.Frontier.G148FinitePrimitivePacketTree
open ArkLib.ProximityGap.Frontier.G150PrimitivePacketDepthTwoBase

variable {F : Type*} [AddCommGroup F] [DecidableEq F]

/-- **Composite-onset theorem.** Every nonprimitive balanced core has depth at least four. -/
theorem four_le_left_card_of_balanced_not_primitive {c : Finset F × Finset F}
    (hc : IsBalancedCore c) (hnp : ¬ IsPrimitiveBalancedCore c) : 4 ≤ c.1.card := by
  rcases primitive_or_split c hc with hprim |
    ⟨d, e, hd, he, hdlt, helt, hdisjL, hdisjR, hreconL, hreconR⟩
  · exact (hnp hprim).elim
  · have hdmin : 2 ≤ d.1.card := balancedCore_two_le_left_card hd.1
    have hemin : 2 ≤ e.1.card := balancedCore_two_le_left_card he
    have hcard : d.1.card + e.1.card = c.1.card := by
      rw [← Finset.card_union_of_disjoint hdisjL, hreconL]
    omega

/-- Every balanced core below depth four is primitive. -/
theorem primitive_of_balanced_of_left_card_lt_four {c : Finset F × Finset F}
    (hc : IsBalancedCore c) (hcard : c.1.card < 4) : IsPrimitiveBalancedCore c := by
  by_contra hnp
  exact (Nat.not_le_of_lt hcard) (four_le_left_card_of_balanced_not_primitive hc hnp)

/-- In particular, every balanced depth-three core is a genuinely primitive packet. -/
theorem primitiveBalancedCore_iff_balanced_of_left_card_eq_three
    {c : Finset F × Finset F} (hcard : c.1.card = 3) :
    IsPrimitiveBalancedCore c ↔ IsBalancedCore c := by
  constructor
  · exact fun h => h.1
  · intro hc
    exact primitive_of_balanced_of_left_card_lt_four hc (by omega)

/-- **Exact depth-four structural classification.** A balanced depth-four core is primitive, or
splits into two disjoint depth-two balanced (therefore primitive) packets which reconstruct it. -/
theorem depthFour_primitive_or_two_depthTwo
    {c : Finset F × Finset F} (hc : IsBalancedCore c) (hcard : c.1.card = 4) :
    IsPrimitiveBalancedCore c ∨
      ∃ d e : Finset F × Finset F,
        IsBalancedCore d ∧ IsBalancedCore e ∧
        d.1.card = 2 ∧ e.1.card = 2 ∧
        IsPrimitiveBalancedCore d ∧ IsPrimitiveBalancedCore e ∧
        Disjoint d.1 e.1 ∧ Disjoint d.2 e.2 ∧
        d.1 ∪ e.1 = c.1 ∧ d.2 ∪ e.2 = c.2 := by
  rcases primitive_or_split c hc with hprim |
    ⟨d, e, hd, he, hdlt, helt, hdisjL, hdisjR, hreconL, hreconR⟩
  · exact Or.inl hprim
  · right
    have hdmin : 2 ≤ d.1.card := balancedCore_two_le_left_card hd.1
    have hemin : 2 ≤ e.1.card := balancedCore_two_le_left_card he
    have hsum : d.1.card + e.1.card = 4 := by
      rw [← hcard, ← Finset.card_union_of_disjoint hdisjL, hreconL]
    have hdcard : d.1.card = 2 := by omega
    have hecard : e.1.card = 2 := by omega
    have hdprim :=
      (primitiveBalancedCore_iff_balanced_of_left_card_eq_two hdcard).2 hd.1
    have heprim :=
      (primitiveBalancedCore_iff_balanced_of_left_card_eq_two hecard).2 he
    exact ⟨d, e, hd.1, he, hdcard, hecard, hdprim, heprim,
      hdisjL, hdisjR, hreconL, hreconR⟩

theorem leafCount_pos {c : Finset F × Finset F}
    (T : PrimitivePacketTree c) : 0 < T.leafCount := by
  induction T with
  | leaf hc => simp [PrimitivePacketTree.leafCount]
  | split hc hd he hdlt helt hdisjL hdisjR hreconL hreconR left right ihL ihR =>
      simp only [PrimitivePacketTree.leafCount]
      omega

/-- Below composite onset, every packet tree consists of exactly one primitive leaf. -/
theorem leafCount_eq_one_of_rootDepth_lt_four
    {c : Finset F × Finset F} (T : PrimitivePacketTree c) (hcard : c.1.card < 4) :
    T.leafCount = 1 := by
  have hupper := two_mul_leafCount_le_rootDepth T
  have hpos := leafCount_pos T
  omega

#print axioms four_le_left_card_of_balanced_not_primitive
#print axioms primitive_of_balanced_of_left_card_lt_four
#print axioms primitiveBalancedCore_iff_balanced_of_left_card_eq_three
#print axioms depthFour_primitive_or_two_depthTwo
#print axioms leafCount_pos
#print axioms leafCount_eq_one_of_rootDepth_lt_four

end ArkLib.ProximityGap.Frontier.G151CompositePacketOnsetDepthFour
