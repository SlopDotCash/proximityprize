/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RigidityIterated2kLift
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvX_AntipodalTransversalEvenCardLe

/-!
# A nonzero first-coefficient anchor for odd disjoint dyadic locators

Two disjoint odd-cardinality subsets of a dyadic root-of-unity group cannot
have the same sum in characteristic zero.  Indeed, the existing dyadic
collision law makes each set negation-closed, while a fixed-point-free
negation-closed finite set has even cardinality.

For degree-seven split locators, the sum is (up to sign) the coefficient of
`X^6`.  This theorem supplies the nonzero anchor used by the prize-field
minor-norm lift.
-/

set_option autoImplicit false

open Finset BigOperators

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOddAnchor

variable {F : Type} [Field F]

/-- Vanishing minors against one nonzero anchor make two coefficient-difference
vectors proportional.  This is the final linear-algebra step in the anchored
minor lift. -/
theorem proportional_of_anchor_minors
    {index : Type} (x y : index → F) (anchor : index)
    (hanchor : x anchor ≠ 0)
    (hminor : ∀ j, x anchor * y j - x j * y anchor = 0) :
    ∃ lambda : F, ∀ j, y j = lambda * x j := by
  refine ⟨y anchor / x anchor, fun j ↦ ?_⟩
  have hj := hminor j
  field_simp [hanchor]
  linear_combination hj

/-- Disjoint odd-cardinality dyadic root sets have distinct first elementary
symmetric sums. -/
theorem sum_ne_of_disjoint_odd_card
    [CharZero F]
    {m : ℕ} (hm : 1 ≤ m) {zeta : F}
    (hzeta : IsPrimitiveRoot zeta (2 ^ m))
    {A B : Finset F}
    (hA : ∀ x ∈ A,
      Round29IteratedLift.IsSignedPow zeta (2 ^ (m - 1)) x)
    (hB : ∀ x ∈ B,
      Round29IteratedLift.IsSignedPow zeta (2 ^ (m - 1)) x)
    (hdisjoint : Disjoint A B)
    (hzero : (0 : F) ∉ A)
    (hodd : Odd A.card) :
    (∑ x ∈ A, x) ≠ ∑ x ∈ B, x := by
  classical
  intro hsum
  have hneg := Round29IteratedLift.antipodal_closure_unconditional
    hm hzeta hA hB hdisjoint hsum
  have heven := AntipodalTransversal.negClosed_card_even A two_ne_zero hzero hneg
  exact (Nat.not_even_iff_odd.mpr hodd) heven

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOddAnchor

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOddAnchor
#print axioms proportional_of_anchor_minors
#print axioms sum_ne_of_disjoint_odd_card
