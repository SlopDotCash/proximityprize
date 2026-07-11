/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterScaleArithmetic
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterDeterminantMultiplicity

/-!
# P1 rate-quarter rank-three determinant audit

The three-line determinant has degree at most `2*k-2`.  Its core-multiplicity
consumer therefore fires only when the three core cardinalities exceed
`N + 2*(k-1)`.  This file records the exact literal-P1 onset and compares it
with the two unconditional core-mass floors available from threshold incidence:

* three-set Bonferroni: `3*T-N = 704643074`;
* one sharp Plotkin anchor plus two universal pair intersections:
  `327272221 + 2*(2*T-N) = 550968437`.

Both are far below the determinant onset `1610612735`.  Thus determinant
multiplicity remains a valid amplifier, but cannot fire from the current
rank-three seed without a genuinely new core-growth input.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterRankThreeDeterminantAudit

open P1RateQuarterScaleArithmetic

/-- Literal predecessor agreement threshold. -/
abbrev T : Nat := 592794966

/-- First core sum that strictly exceeds the determinant degree budget after
subtracting the `N`-coordinate universe. -/
abbrev determinantCoreSumOnset : Nat := N + 2 * (k - 1) + 1

theorem determinantCoreSumOnset_eq : determinantCoreSumOnset = 1610612735 := by
  norm_num [determinantCoreSumOnset, N, k]

/-- Three threshold-size sets force this much total pair-intersection mass. -/
theorem threeThreshold_pairCoreMassFloor_eq :
    3 * T - N = 704643074 := by
  norm_num [T, N]

/-- The strongest presently unconditional seed obtained by combining the exact
Plotkin anchor with the two universal inclusion--exclusion pair floors. -/
theorem pinnedAnchor_plus_two_pairFloors_eq :
    327272221 + 2 * (2 * T - N) = 550968437 := by
  norm_num [T, N]

/-- Bonferroni alone misses determinant collapse by `905,969,661` core incidences. -/
theorem bonferroni_determinant_deficit_eq :
    determinantCoreSumOnset - (3 * T - N) = 905969661 := by
  norm_num [determinantCoreSumOnset, T, N, k]

/-- The pinned-anchor-plus-baseline estimate is weaker still. -/
theorem pinnedAnchor_determinant_deficit_eq :
    determinantCoreSumOnset -
      (327272221 + 2 * (2 * T - N)) = 1059644298 := by
  norm_num [determinantCoreSumOnset, T, N, k]

/-- Exact no-go comparison: neither current unconditional core-mass floor
reaches the three-line determinant-collapse onset. -/
theorem current_coreMass_floors_below_determinant_onset :
    3 * T - N < determinantCoreSumOnset ∧
      327272221 + 2 * (2 * T - N) < determinantCoreSumOnset := by
  norm_num [determinantCoreSumOnset, T, N, k]

/-- After paying the pinned anchor core, this is the remaining two-core mass
needed to reach determinant collapse. -/
theorem remaining_twoCore_mass_needed_eq :
    determinantCoreSumOnset - 327272221 = 1283340514 := by
  norm_num [determinantCoreSumOnset, N, k]

/-- Consequently, reaching the determinant onset forces at least one of the
other two cores to have size `641,670,257`. -/
theorem one_other_core_ge_641670257_of_onset
    (z₁ z₂ : Nat)
    (honset : determinantCoreSumOnset ≤ 327272221 + z₁ + z₂) :
    641670257 ≤ z₁ ∨ 641670257 ≤ z₂ := by
  have hOnset := determinantCoreSumOnset_eq
  omega

/-- Two cores below `641,670,257` cannot supplement the pinned anchor enough
to trigger the determinant-degree consumer. -/
theorem pinnedAnchor_sum_below_onset_of_other_cores_le
    (z₁ z₂ : Nat) (hz₁ : z₁ ≤ 641670256) (hz₂ : z₂ ≤ 641670256) :
    327272221 + z₁ + z₂ < determinantCoreSumOnset := by
  have hOnset := determinantCoreSumOnset_eq
  omega

/-! ## One-line petal recursion no-go -/

/-- Fresh agreement size available after deleting one line core. -/
abbrev freshAgreementFloor : Nat := T - (k - 1)

/-- Integer Rankin/Plotkin update forced from a source core lower bound `c`.
The `+1` encodes the strict intersection conclusion. -/
abbrev petalUpdate (c : Nat) : Nat :=
  (freshAgreementFloor ^ 2 - 1) / (N - c) + 1

theorem freshAgreementFloor_eq : freshAgreementFloor = 324359511 := by
  norm_num [freshAgreementFloor, T, k]

/-- The optimized high-core petal does not bootstrap: its next isolated-line
iterate drops by more than thirty-two million coordinates. -/
theorem petalUpdate_145836060_eq : petalUpdate 145836060 = 113383381 := by
  norm_num [petalUpdate, freshAgreementFloor, T, k, N]

/-- Exact attracting integer fixed point of the one-line reduced Plotkin map. -/
theorem petalUpdate_fixedPoint_eq : petalUpdate 109061044 = 109061044 := by
  norm_num [petalUpdate, freshAgreementFloor, T, k, N]

/-- The fixed point is strictly weaker than the universal inclusion--exclusion
pair-core floor.  Therefore independent one-line petal iteration cannot create
the new mass needed by determinant collapse. -/
theorem petalUpdate_fixedPoint_below_universal_pair_floor :
    petalUpdate 109061044 < 2 * T - N := by
  norm_num [petalUpdate, freshAgreementFloor, T, k, N]

end ArkLib.ProximityGap.Frontier.P1RateQuarterRankThreeDeterminantAudit

open ArkLib.ProximityGap.Frontier.P1RateQuarterRankThreeDeterminantAudit

#print axioms determinantCoreSumOnset_eq
#print axioms threeThreshold_pairCoreMassFloor_eq
#print axioms pinnedAnchor_plus_two_pairFloors_eq
#print axioms bonferroni_determinant_deficit_eq
#print axioms pinnedAnchor_determinant_deficit_eq
#print axioms current_coreMass_floors_below_determinant_onset
#print axioms remaining_twoCore_mass_needed_eq
#print axioms one_other_core_ge_641670257_of_onset
#print axioms pinnedAnchor_sum_below_onset_of_other_cores_le
#print axioms freshAgreementFloor_eq
#print axioms petalUpdate_145836060_eq
#print axioms petalUpdate_fixedPoint_eq
#print axioms petalUpdate_fixedPoint_below_universal_pair_floor
