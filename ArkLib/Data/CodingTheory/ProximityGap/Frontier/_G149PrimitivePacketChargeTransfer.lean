/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G148FinitePrimitivePacketTree

/-!
# G149: primitive-packet charge transfer

G148 decomposes a balanced full-depth core into finitely many primitive leaves and proves exact
depth-mass conservation.  This file adds the enumerative consumer: arbitrary nonnegative charges
on primitive packets sum through the tree.  In particular, a primitive bound linear in packet
depth transfers with the same constant to every composite core.

We also flatten the leaf supports and prove that their unions reconstruct both root supports.
Finally, if arithmetic exclusions force every primitive packet to have depth at least `s`, then a
depth-`t` core contains at most `t / s` primitive packets in the exact multiplicative form
`s * leafCount ≤ t`.

These statements are generic bookkeeping.  The missing production input is a bound/classification
for primitive characteristic-`p` packets; G149 makes any such input immediately composable.

Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G149PrimitivePacketChargeTransfer

open ArkLib.ProximityGap.Frontier.G147ConnectedBalancedCoreRecursion
open ArkLib.ProximityGap.Frontier.G148FinitePrimitivePacketTree

variable {F : Type*} [AddCommGroup F] [DecidableEq F]

/-- Union of the left supports of all primitive leaves. -/
def leafLeftUnion {c : Finset F × Finset F} :
    PrimitivePacketTree c → Finset F
  | .leaf _ => c.1
  | .split _ _ _ _ _ _ _ _ _ left right => leafLeftUnion left ∪ leafLeftUnion right

/-- Union of the right supports of all primitive leaves. -/
def leafRightUnion {c : Finset F × Finset F} :
    PrimitivePacketTree c → Finset F
  | .leaf _ => c.2
  | .split _ _ _ _ _ _ _ _ _ left right => leafRightUnion left ∪ leafRightUnion right

/-- Sum of an arbitrary natural-number charge over primitive leaves. -/
def leafCharge (w : Finset F × Finset F → ℕ)
    {c : Finset F × Finset F} : PrimitivePacketTree c → ℕ
  | .leaf _ => w c
  | .split _ _ _ _ _ _ _ _ _ left right => leafCharge w left + leafCharge w right

/-- Flattening preserves the complete left support. -/
theorem leafLeftUnion_eq_root {c : Finset F × Finset F}
    (T : PrimitivePacketTree c) : leafLeftUnion T = c.1 := by
  induction T with
  | leaf hc => rfl
  | split hc hd he hdlt helt hdisjL hdisjR hreconL hreconR left right ihL ihR =>
      simp only [leafLeftUnion, ihL, ihR]
      exact hreconL

/-- Flattening preserves the complete right support. -/
theorem leafRightUnion_eq_root {c : Finset F × Finset F}
    (T : PrimitivePacketTree c) : leafRightUnion T = c.2 := by
  induction T with
  | leaf hc => rfl
  | split hc hd he hdlt helt hdisjL hdisjR hreconL hreconR left right ihL ihR =>
      simp only [leafRightUnion, ihL, ihR]
      exact hreconR

/-- A linear charge bound on primitive packets sums with the same constant over every packet
tree, first in the exact leaf-depth gauge. -/
theorem leafCharge_le_mul_leafDepthSum
    (w : Finset F × Finset F → ℕ) (K : ℕ)
    (hprimitive : ∀ c, IsPrimitiveBalancedCore c → w c ≤ K * c.1.card)
    {c : Finset F × Finset F} (T : PrimitivePacketTree c) :
    leafCharge w T ≤ K * T.leafDepthSum := by
  induction T with
  | leaf hc => exact hprimitive _ hc
  | split hc hd he hdlt helt hdisjL hdisjR hreconL hreconR left right ihL ihR =>
      simp only [leafCharge, PrimitivePacketTree.leafDepthSum]
      calc
        leafCharge w left + leafCharge w right ≤
            K * left.leafDepthSum + K * right.leafDepthSum := Nat.add_le_add ihL ihR
        _ = K * (left.leafDepthSum + right.leafDepthSum) :=
          (Nat.mul_add _ _ _).symm

/-- **G149 charge capstone.** A primitive depth-linear estimate transfers unchanged to the root. -/
theorem leafCharge_le_mul_rootDepth
    (w : Finset F × Finset F → ℕ) (K : ℕ)
    (hprimitive : ∀ c, IsPrimitiveBalancedCore c → w c ≤ K * c.1.card)
    {c : Finset F × Finset F} (T : PrimitivePacketTree c) :
    leafCharge w T ≤ K * c.1.card := by
  rw [← T.leafDepthSum_eq_rootDepth]
  exact leafCharge_le_mul_leafDepthSum w K hprimitive T

/-- If every primitive packet has depth at least `s`, then `s` times the leaf count is bounded by
the exact root depth.  This is the direct consumer for short-packet exclusions. -/
theorem mul_leafCount_le_rootDepth
    (s : ℕ) (hmin : ∀ c : Finset F × Finset F,
      IsPrimitiveBalancedCore c → s ≤ c.1.card)
    {c : Finset F × Finset F} (T : PrimitivePacketTree c) :
    s * T.leafCount ≤ c.1.card := by
  rw [← T.leafDepthSum_eq_rootDepth]
  induction T with
  | leaf hc => simpa [PrimitivePacketTree.leafCount, PrimitivePacketTree.leafDepthSum] using hmin _ hc
  | split hc hd he hdlt helt hdisjL hdisjR hreconL hreconR left right ihL ihR =>
      simp only [PrimitivePacketTree.leafCount, PrimitivePacketTree.leafDepthSum]
      calc
        s * (left.leafCount + right.leafCount) =
            s * left.leafCount + s * right.leafCount := Nat.mul_add _ _ _
        _ ≤ left.leafDepthSum + right.leafDepthSum := Nat.add_le_add ihL ihR

#print axioms leafLeftUnion_eq_root
#print axioms leafRightUnion_eq_root
#print axioms leafCharge_le_mul_leafDepthSum
#print axioms leafCharge_le_mul_rootDepth
#print axioms mul_leafCount_le_rootDepth

end ArkLib.ProximityGap.Frontier.G149PrimitivePacketChargeTransfer
