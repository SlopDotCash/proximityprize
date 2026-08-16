/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Multiset.UnionInter

/-!
# G83M: canonical maximal common-multiset cancellation

The factorial-corrected padding decoder needs a canonical decomposition of two endpoint
multiplicity profiles into one common padding multiset and two disjoint primitive cores.  This file
provides that decomposition abstractly for multisets.

For `common = left ∩ right`, define the residual cores by multiset subtraction.  We prove:

* exact reconstruction of both endpoints;
* the two residual cores are disjoint;
* equal-length endpoints give equal core depths;
* `common` is maximal among multisets contained in both endpoints;
* in an additive cancellation monoid, equality of endpoint sums descends to equality of residual
  core sums.

This is the canonical cancellation kernel.  G81D supplies the relative permutation between the two
orders of `common`; the remaining step toward the full G81C decoder is tuple-position reconstruction.
Issue #466/#505.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G83MMaximalCommonCancellation

variable {A : Type*} [DecidableEq A]

/-- The unique maximal multiset contained in both endpoints. -/
def commonPart (left right : Multiset A) : Multiset A := left ∩ right

/-- The left primitive residual after maximal common cancellation. -/
def leftCore (left right : Multiset A) : Multiset A := left - commonPart left right

/-- The right primitive residual after maximal common cancellation. -/
def rightCore (left right : Multiset A) : Multiset A := right - commonPart left right

theorem left_reconstruct (left right : Multiset A) :
    leftCore left right + commonPart left right = left := by
  rw [leftCore, commonPart, Multiset.sub_inter]
  exact Multiset.sub_add_inter left right

theorem right_reconstruct (left right : Multiset A) :
    rightCore left right + commonPart left right = right := by
  unfold rightCore commonPart
  rw [Multiset.inter_comm]
  rw [Multiset.sub_inter]
  exact Multiset.sub_add_inter right left

/-- **Primitivity.**  Maximal cancellation leaves disjoint residual supports. -/
theorem core_disjoint (left right : Multiset A) :
    Disjoint (leftCore left right) (rightCore left right) := by
  rw [← Multiset.inter_eq_zero_iff_disjoint]
  ext a
  simp only [Multiset.count_inter, Multiset.count_zero, leftCore, rightCore, commonPart,
    Multiset.count_sub]
  omega

/-- Equal-length endpoints leave residual cores of equal depth. -/
theorem core_card_eq {left right : Multiset A} (hcard : left.card = right.card) :
    (leftCore left right).card = (rightCore left right).card := by
  have hleft := congrArg Multiset.card (left_reconstruct left right)
  have hright := congrArg Multiset.card (right_reconstruct left right)
  simp only [Multiset.card_add] at hleft hright
  omega

/-- **Maximality.**  Every multiset contained in both endpoints is contained in `commonPart`. -/
theorem le_commonPart {padding left right : Multiset A}
    (hleft : padding ≤ left) (hright : padding ≤ right) :
    padding ≤ commonPart left right :=
  Multiset.le_inter hleft hright

/-- The common part itself is contained in both endpoints. -/
theorem commonPart_le (left right : Multiset A) :
    commonPart left right ≤ left ∧ commonPart left right ≤ right :=
  ⟨Multiset.inter_le_left, Multiset.inter_le_right⟩

/-- Additive endpoint equality descends through common cancellation to the primitive cores. -/
theorem core_sum_eq_of_sum_eq [AddCancelCommMonoid A]
    {left right : Multiset A} (hsum : left.sum = right.sum) :
    (leftCore left right).sum = (rightCore left right).sum := by
  have hleft := congrArg Multiset.sum (left_reconstruct left right)
  have hright := congrArg Multiset.sum (right_reconstruct left right)
  simp only [Multiset.sum_add] at hleft hright
  apply add_right_cancel (b := (commonPart left right).sum)
  rw [hleft, hsum, ← hright]

end ArkLib.ProximityGap.Frontier.G83MMaximalCommonCancellation

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.G83MMaximalCommonCancellation.left_reconstruct
#print axioms ArkLib.ProximityGap.Frontier.G83MMaximalCommonCancellation.right_reconstruct
#print axioms ArkLib.ProximityGap.Frontier.G83MMaximalCommonCancellation.core_disjoint
#print axioms ArkLib.ProximityGap.Frontier.G83MMaximalCommonCancellation.core_card_eq
#print axioms ArkLib.ProximityGap.Frontier.G83MMaximalCommonCancellation.le_commonPart
#print axioms ArkLib.ProximityGap.Frontier.G83MMaximalCommonCancellation.core_sum_eq_of_sum_eq
