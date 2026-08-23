/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G147ConnectedBalancedCoreRecursion

/-!
# G148: finite primitive-packet trees

G147 proves that one balanced core is primitive or splits into two smaller balanced cores.  Here
that local dichotomy is iterated by strong induction into an explicit finite binary packet tree.
Every leaf carries a proof that it is a primitive balanced core; every internal node carries the
disjointness and exact support-reconstruction equations from G147.

The tree also records exact mass conservation: the sum of the left-cardinalities of all primitive
leaves equals the depth of the root.  Since every primitive leaf is nonempty, the number of leaves
is at most the root depth.  These are the bookkeeping invariants needed to turn future primitive
Mann-packet classifications into full-depth census bounds.

This file does not classify the primitive leaves.  That characteristic-`p` classification/count is
the remaining arithmetic wall.

Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G148FinitePrimitivePacketTree

open ArkLib.ProximityGap.Frontier.G147ConnectedBalancedCoreRecursion

variable {F : Type*} [AddCommGroup F] [DecidableEq F]

/-- A finite decomposition tree of a balanced core into primitive connected packets. -/
inductive PrimitivePacketTree : (Finset F × Finset F) → Type _
  | leaf {c : Finset F × Finset F} (hc : IsPrimitiveBalancedCore c) :
      PrimitivePacketTree c
  | split {c d e : Finset F × Finset F}
      (hc : IsBalancedCore c)
      (hd : IsProperBalancedSubcore d c) (he : IsBalancedCore e)
      (hdlt : d.1.card < c.1.card) (helt : e.1.card < c.1.card)
      (hdisjL : Disjoint d.1 e.1) (hdisjR : Disjoint d.2 e.2)
      (hreconL : d.1 ∪ e.1 = c.1) (hreconR : d.2 ∪ e.2 = c.2)
      (left : PrimitivePacketTree d) (right : PrimitivePacketTree e) :
      PrimitivePacketTree c

/-- Number of primitive leaves. -/
def PrimitivePacketTree.leafCount {c : Finset F × Finset F} :
    PrimitivePacketTree c → ℕ
  | .leaf _ => 1
  | .split _ _ _ _ _ _ _ _ _ left right => left.leafCount + right.leafCount

/-- Sum of the left-cardinalities of all primitive leaves. -/
def PrimitivePacketTree.leafDepthSum {c : Finset F × Finset F} :
    PrimitivePacketTree c → ℕ
  | .leaf _ => c.1.card
  | .split _ _ _ _ _ _ _ _ _ left right => left.leafDepthSum + right.leafDepthSum

/-- Every packet tree root is balanced. -/
theorem PrimitivePacketTree.root_balanced {c : Finset F × Finset F}
    (T : PrimitivePacketTree c) : IsBalancedCore c := by
  cases T with
  | leaf hc => exact hc.1
  | split hc => exact hc

/-- **Exact primitive mass conservation.** -/
theorem PrimitivePacketTree.leafDepthSum_eq_rootDepth {c : Finset F × Finset F}
    (T : PrimitivePacketTree c) : T.leafDepthSum = c.1.card := by
  induction T with
  | leaf hc => rfl
  | split hc hd he hdlt helt hdisjL hdisjR hreconL hreconR left right ihL ihR =>
      simp only [leafDepthSum, ihL, ihR]
      rw [← Finset.card_union_of_disjoint hdisjL, hreconL]

/-- Every primitive leaf contributes at least one unit of depth, so there are at most `depth`
leaves. -/
theorem PrimitivePacketTree.leafCount_le_rootDepth {c : Finset F × Finset F}
    (T : PrimitivePacketTree c) : T.leafCount ≤ c.1.card := by
  rw [← T.leafDepthSum_eq_rootDepth]
  induction T with
  | leaf hc => exact Finset.card_pos.mpr hc.1.1
  | split hc hd he hdlt helt hdisjL hdisjR hreconL hreconR left right ihL ihR =>
      simp only [leafCount, leafDepthSum]
      exact Nat.add_le_add ihL ihR

/-- **G148 capstone.** Every balanced core has a finite decomposition tree with primitive leaves. -/
theorem exists_primitivePacketTree (c : Finset F × Finset F) (hc : IsBalancedCore c) :
    Nonempty (PrimitivePacketTree c) := by
  induction hn : c.1.card using Nat.strong_induction_on generalizing c with
  | h n ih =>
      rcases primitive_or_split c hc with hprim |
        ⟨d, e, hd, he, hdlt, helt, hdisjL, hdisjR, hreconL, hreconR⟩
      · exact ⟨PrimitivePacketTree.leaf hprim⟩
      · have Td : Nonempty (PrimitivePacketTree d) :=
          ih d.1.card (hn ▸ hdlt) d hd.1 rfl
        have Te : Nonempty (PrimitivePacketTree e) :=
          ih e.1.card (hn ▸ helt) e he rfl
        exact ⟨PrimitivePacketTree.split hc hd he hdlt helt hdisjL hdisjR
          hreconL hreconR Td.some Te.some⟩

/-- Existential package exporting the two quantitative tree invariants. -/
theorem exists_primitivePacketTree_with_invariants
    (c : Finset F × Finset F) (hc : IsBalancedCore c) :
    ∃ T : PrimitivePacketTree c,
      T.leafDepthSum = c.1.card ∧ T.leafCount ≤ c.1.card := by
  obtain ⟨T⟩ := exists_primitivePacketTree c hc
  exact ⟨T, T.leafDepthSum_eq_rootDepth, T.leafCount_le_rootDepth⟩

#print axioms PrimitivePacketTree.root_balanced
#print axioms PrimitivePacketTree.leafDepthSum_eq_rootDepth
#print axioms PrimitivePacketTree.leafCount_le_rootDepth
#print axioms exists_primitivePacketTree
#print axioms exists_primitivePacketTree_with_invariants

end ArkLib.ProximityGap.Frontier.G148FinitePrimitivePacketTree
