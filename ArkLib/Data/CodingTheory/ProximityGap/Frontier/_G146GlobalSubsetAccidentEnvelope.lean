/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G145LowerDepthMultiplicityEnvelope

/-!
# G146: global subset-accident and energy envelope

G145 bounds one exact cancellation-depth stratum by a full-depth core census times the number of
possible common intersections.  This file sums that estimate over every positive depth.  It then
welds the result to G141's exact diagonal/off-diagonal collision identity, producing a direct upper
bound for the fiber energy of the injective-subset sum map.

The result isolates the remaining arithmetic input in the family of full-depth quantities
`depthFiber G t t`; every lower-depth collision is charged to one such core and the exact binomial
padding multiplicity `choose (|G| - 2t) (r-t)`.  This is the finite-census interface needed by a
subsequent Möbius--Mann connected-packet analysis of the full-depth fibers.

Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G146GlobalSubsetAccidentEnvelope

open scoped BigOperators
open ArkLib.ProximityGap.Frontier.G140QuantitativeAccidentDCFloor
open ArkLib.ProximityGap.Frontier.G141OffDiagonalAccidentIdentity
open ArkLib.ProximityGap.Frontier.G143DepthStratifiedSubsetAccidents
open ArkLib.ProximityGap.Frontier.G145LowerDepthMultiplicityEnvelope
open ArkLib.ProximityGap.Frontier.G95CardinalityDeepCapNoGo

variable {F : Type*} [AddCommGroup F] [Fintype F] [DecidableEq F]

/-- **Global accident envelope.** Every subset-sum accident is charged to its positive-depth
disjoint core and its common-intersection choice. -/
theorem subsetAccidents_card_le_sum_depthFiber_choose (G : Finset F) (r : ℕ) :
    (subsetAccidents G r).card ≤
      ∑ t ∈ Finset.Icc 1 r,
        depthFiber G t t * (G.card - 2 * t).choose (r - t) := by
  rw [card_subsetAccidents_eq_sum_positive_strata]
  exact Finset.sum_le_sum fun t _ => stratum_card_le_depthFiber_mul_choose G r t

/-- The source cardinality of the subset-sum map is the corresponding binomial coefficient. -/
theorem card_subsetFamily (G : Finset F) (r : ℕ) :
    Fintype.card (SubsetFamily G r) = G.card.choose r := by
  change Fintype.card ↑(G.powersetCard r) = _
  rw [Fintype.card_coe, Finset.card_powersetCard]

/-- Exact energy decomposition into the diagonal subset count and positive-depth accidents. -/
theorem subsetSum_fiberEnergy_eq_choose_add_sum_strata (G : Finset F) (r : ℕ) :
    fiberEnergy (subsetSumMap G r) =
      G.card.choose r +
        ∑ t ∈ Finset.Icc 1 r, (subsetAccidentStratum G r t).card := by
  calc
    fiberEnergy (subsetSumMap G r) =
        Fintype.card (SubsetFamily G r) + (subsetAccidents G r).card := by
      rw [fiberEnergy_eq_card_collisionPairs,
        card_collisionPairs_eq_card_add_offDiagonal]
      rfl
    _ = G.card.choose r +
        ∑ t ∈ Finset.Icc 1 r, (subsetAccidentStratum G r t).card := by
      rw [card_subsetFamily, card_subsetAccidents_eq_sum_positive_strata]

/-- **G146 capstone.** The full subset-sum fiber energy is bounded by the diagonal plus a weighted
sum of full-depth ordered-word fibers. -/
theorem subsetSum_fiberEnergy_le_choose_add_depthFiber_sum (G : Finset F) (r : ℕ) :
    fiberEnergy (subsetSumMap G r) ≤
      G.card.choose r +
        ∑ t ∈ Finset.Icc 1 r,
          depthFiber G t t * (G.card - 2 * t).choose (r - t) := by
  rw [subsetSum_fiberEnergy_eq_choose_add_sum_strata]
  exact Nat.add_le_add_left
    (Finset.sum_le_sum fun t _ => stratum_card_le_depthFiber_mul_choose G r t) _

#print axioms subsetAccidents_card_le_sum_depthFiber_choose
#print axioms card_subsetFamily
#print axioms subsetSum_fiberEnergy_eq_choose_add_sum_strata
#print axioms subsetSum_fiberEnergy_le_choose_add_depthFiber_sum

end ArkLib.ProximityGap.Frontier.G146GlobalSubsetAccidentEnvelope
