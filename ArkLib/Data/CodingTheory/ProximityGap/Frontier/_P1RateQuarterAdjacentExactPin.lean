/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._MCAAdjacentFloorExactPin
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterCommonFactorCanonicalBridge
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterPredecessorGenericSplit

/-!
# Conditional exact P1 pin at the common-factor endpoint

The common-factor construction is bad at radius

`480946859 / 2^30 = 43/96 + 1/(3*2^30)`,

while `_P1RateQuarterPredecessorGenericSplit` reduces goodness at its immediate
predecessor `480946858 / 2^30` to one named structured-floor residual.  The
generic adjacent-floor connector therefore pins `mcaDeltaStar` exactly once
that residual is supplied.

The strong common-factor canonical bridge has already transported the bad-label
family from `Coord` to `Fin N`.  This file consumes that bridge, so every final
theorem is stated on the single literal prize-code surface

`evalCode g N (k - 1)`.

The remaining hypothesis is exactly
`PredecessorStructuredFloorResidual canonicalDomain`; no additional incidence,
reindexing, or endpoint-continuity assumption is hidden in the connector.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option maxHeartbeats 800000
set_option maxRecDepth 500000

open _root_.ProximityGap Code
open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterAdjacentExactPin

open ArkLib.ProximityGap.PrizeShapePrimeP30
open ArkLib.ProximityGap.KKH26
open P1RateQuarterScaleArithmetic
open P1RateQuarterCommonFactorArithmetic
open P1RateQuarterPredecessorGenericSplit
open P1RateQuarterCanonicalCodeBridge
open P1RateQuarterCommonFactorCanonicalBridge
open MCAAdjacentFloorExactPin

local instance localInstance_P1RateQuarterAdjacentExactPin_1 : Fact (Nat.Prime P) := ⟨prime_P⟩
local instance localInstance_P1RateQuarterAdjacentExactPin_2 : NeZero N := ⟨by norm_num [N]⟩
attribute [local instance] Classical.propDecidable

local notation "epsilonP1" =>
  ((((2 : ℕ) ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞)
local notation "deltaCommon" => P1RateQuarterCommonFactorArithmetic.delta

/-- The strongest operational upper bound, now on the same canonical code
surface used by the predecessor theorem. -/
theorem canonical_mcaDeltaStar_le_common_delta :
    ProximityGap.MCAThresholdLedger.mcaDeltaStar
        (F := F) (A := F) canonicalCode epsilonP1 ≤ deltaCommon := by
  rw [← evalCode_eq_canonicalCode]
  exact evalCode_commonFactor_mcaDeltaStar_le

/-- The common-factor endpoint is the Hamming-lattice point with radius
numerator `480946859`. -/
theorem common_delta_eq_latticeRadius :
    deltaCommon = latticeRadius N radiusNumerator := by
  rfl

/-- The generic-split radius is exactly the immediate predecessor of the
common-factor endpoint. -/
theorem predecessor_delta_eq_predecessorRadius :
    P1RateQuarterPredecessorGenericSplit.predecessorDelta =
      predecessorRadius N radiusNumerator := by
  apply NNReal.coe_injective
  push_cast
  norm_num [P1RateQuarterPredecessorGenericSplit.predecessorDelta,
    P1RateQuarterPredecessorGenericSplit.predecessorRadiusNumerator,
    P1RateQuarterPredecessorGenericSplit.predecessorThreshold,
    predecessorRadius, radiusNumerator, amplifiedThreshold, amplifiedCore,
    N, m, r, d]

/-- Conditional goodness of the immediate predecessor, restated on the
canonical code and generic adjacent-floor radius. -/
theorem canonical_predecessor_good_of_structured
    (hstructured : PredecessorStructuredFloorResidual canonicalDomain) :
    epsMCA (F := F) (A := F) canonicalCode
        (predecessorRadius N radiusNumerator) ≤ epsilonP1 := by
  rw [← predecessor_delta_eq_predecessorRadius]
  simpa [canonicalCode,
    P1RateQuarterPredecessorGenericSplit.predecessorCode] using
    (epsMCA_predecessor_le_prizeEpsilon canonicalDomain hstructured)

/-- **Conditional exact P1 pin on the canonical Reed--Solomon surface.**

The only hypothesis is the structured near-direction bound at the immediate
predecessor.  The far case, budget arithmetic, strong next-rung bad family,
coordinate transport, and supremum endpoint are all discharged. -/
theorem canonical_mcaDeltaStar_eq_common_delta_of_structured
    (hstructured : PredecessorStructuredFloorResidual canonicalDomain) :
    ProximityGap.MCAThresholdLedger.mcaDeltaStar
        (F := F) (A := F) canonicalCode epsilonP1 = deltaCommon := by
  rw [common_delta_eq_latticeRadius]
  apply mcaDeltaStar_eq_latticeRadius_of_predecessor_good_of_upper
      (F := F) (A := F) (a := radiusNumerator)
  · norm_num [radiusNumerator, amplifiedThreshold, amplifiedCore, m, r, d]
  · norm_num [radiusNumerator, amplifiedThreshold, amplifiedCore, N, m, r, d]
  · exact canonical_predecessor_good_of_structured hstructured
  · rw [← common_delta_eq_latticeRadius]
    exact canonical_mcaDeltaStar_le_common_delta

/-- Literal `evalCode` form of the conditional exact pin. -/
theorem evalCode_rateQuarter_mcaDeltaStar_eq_common_delta_of_structured
    (hstructured : PredecessorStructuredFloorResidual canonicalDomain) :
    ProximityGap.MCAThresholdLedger.mcaDeltaStar
        (F := F) (A := F) (evalCode g N (k - 1)) epsilonP1 = deltaCommon := by
  rw [evalCode_eq_canonicalCode]
  exact canonical_mcaDeltaStar_eq_common_delta_of_structured hstructured

/-- Closed-form literal-code statement of the conditional exact pin. -/
theorem evalCode_rateQuarter_mcaDeltaStar_eq_advertised_of_structured
    (hstructured : PredecessorStructuredFloorResidual canonicalDomain) :
    ProximityGap.MCAThresholdLedger.mcaDeltaStar
        (F := F) (A := F) (evalCode g N (k - 1)) epsilonP1 =
      (43 / 96 : ℝ≥0) + 1 / (3 * N : ℕ) := by
  rw [← delta_eq_fortyThree_over_ninetySix_correction]
  exact evalCode_rateQuarter_mcaDeltaStar_eq_common_delta_of_structured hstructured

end ArkLib.ProximityGap.Frontier.P1RateQuarterAdjacentExactPin

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.P1RateQuarterAdjacentExactPin
#print axioms canonical_mcaDeltaStar_le_common_delta
#print axioms predecessor_delta_eq_predecessorRadius
#print axioms canonical_predecessor_good_of_structured
#print axioms canonical_mcaDeltaStar_eq_common_delta_of_structured
#print axioms evalCode_rateQuarter_mcaDeltaStar_eq_advertised_of_structured
