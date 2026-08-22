/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R395PairMultiplicitySixRootReduction
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R400SixPlacementAntipodalCover

/-!
# R401: pair multiplicity ten is a six-support exclusion

R395 proves that every unordered pair support has at most two ordered realizations and that distinct
supports at one sum are disjoint. Consequently, excluding six supports gives ordered multiplicity
at most ten. Combined with R400, the finite `105|G|` target reduces to:

* no nonzero sum has six unordered supports; and
* the primitive four-fiber has size at most `45|G|`.

The first item is now a concrete twelve-root simultaneous cyclotomic obstruction rather than a
pointwise representation-count slogan. `NoSixPairSupports` is deliberately a property of the
particular `G`; it is false uniformly over fields, and an arithmetic producer must include the
quartic prize-regime guard.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.R401PairMultiplicityTenSupportReduction

open ArkLib.ProximityGap.Frontier.R390CharZeroNonzeroRepFourBound
open ArkLib.ProximityGap.Frontier.R392PairFiberNecessaryForFourFiber
open ArkLib.ProximityGap.Frontier.R395PairMultiplicitySixRootReduction
open ArkLib.ProximityGap.Frontier.R400SixPlacementAntipodalCover

variable {F : Type*} [Field F] [DecidableEq F]

/-- The six-support exclusion at every nonzero target. -/
def NoSixPairSupports (G : Finset F) : Prop :=
  ∀ c : F, c ≠ 0 → (pairSupports G c).card ≤ 5

/-- Six-support exclusion implies ordered pair multiplicity at most ten. -/
theorem pairMultiplicityTen_of_noSixPairSupports
    (G : Finset F) (hsix : NoSixPairSupports G) : PairMultiplicityTen G := by
  intro c hc
  calc
    (pairFiber G c).card ≤ 2 * (pairSupports G c).card :=
      card_pairFiber_le_two_mul_pairSupports G c
    _ ≤ 2 * 5 := Nat.mul_le_mul_left 2 (hsix c hc)
    _ = 10 := by norm_num

/-- **Support-level finite `105|G|` capstone.** -/
theorem card_fourFiber_le_105_mul_card_of_noSixSupports
    (G : Finset F) (hneg : ∀ x ∈ G, -x ∈ G)
    (hsix : NoSixPairSupports G) (hprimitive : PrimitiveFourBoundFortyFive G)
    {c : F} (hc : c ≠ 0) :
    (fourFiber G c).card ≤ 105 * G.card :=
  card_fourFiber_le_105_mul_card_of_ten G hneg
    (pairMultiplicityTen_of_noSixPairSupports G hsix) hprimitive hc

end ArkLib.ProximityGap.Frontier.R401PairMultiplicityTenSupportReduction

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R401PairMultiplicityTenSupportReduction.pairMultiplicityTen_of_noSixPairSupports
#print axioms
  ArkLib.ProximityGap.Frontier.R401PairMultiplicityTenSupportReduction.card_fourFiber_le_105_mul_card_of_noSixSupports
