/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterCanonicalCodeBridge
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterCommonFactorBadCount

/-!
# The saturated common-factor endpoint on the literal P1 code

The saturated construction is naturally indexed by the fibre decomposition
`Coord`.  The coordinate equivalence from
`_P1RateQuarterCanonicalCodeBridge` transports its improved received stack to
`Fin N` without changing any MCA event.  This places the unconditional
`43/96 + 1/(3N)` endpoint on the prize's literal
`evalCode g N (k - 1)` surface.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Finset
open _root_.ProximityGap Code
open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterCommonFactorCanonicalBridge

open ArkLib.ProximityGap.PrizeShapePrimeP30
open ArkLib.ProximityGap.KKH26
open P1RateQuarterScaleArithmetic
open P1RateQuarterScaleConstruction
open P1RateQuarterCanonicalCodeBridge
open P1RateQuarterCommonFactorArithmetic
open P1RateQuarterCommonFactorConstruction
open P1RateQuarterCommonFactorBadCount
open P1RateQuarterBadLabelFamilyConnector
open MCAReindexEquiv

local instance : Fact (Nat.Prime P) := ⟨prime_P⟩
local instance : NeZero N := ⟨by norm_num [N]⟩
attribute [local instance] Classical.propDecidable

local notation "δsat" => P1RateQuarterCommonFactorArithmetic.delta

/-- The improved received stack reindexed onto the literal power domain. -/
noncomputable def canonicalAmplifiedStack : WordStack F (Fin 2) (Fin N) :=
  fun i => reindexWord coordEquiv (amplifiedU commonLocatorData i)

/-- Reindexing preserves every saturated certificate event. -/
theorem canonical_saturatedScalarLabel_mcaEvent
    (x : SaturatedCertificate) :
    mcaEvent canonicalCode δsat
      (canonicalAmplifiedStack 0) (canonicalAmplifiedStack 1)
      (saturatedScalarLabel x) := by
  apply (mcaEvent_reindex_reedSolomon_iff coordEquiv domain canonicalDomain
    domain_eq_canonicalDomain k δsat
    (amplifiedU commonLocatorData 0) (amplifiedU commonLocatorData 1)
    (saturatedScalarLabel x)).2
  exact saturatedScalarLabel_mcaEvent commonLocatorData x

/-- The literal-code stack has at least `N+2` bad scalars at the improved
radius. -/
theorem canonical_saturated_badScalar_filter_card_ge_N_add_two :
    N + 2 ≤ (Finset.univ.filter fun gamma : F =>
      mcaEvent canonicalCode δsat
        (canonicalAmplifiedStack 0) (canonicalAmplifiedStack 1) gamma).card := by
  rw [← saturatedCertificate_card]
  exact certificate_card_le_badEvent_filter_card canonicalCode δsat
    canonicalAmplifiedStack saturatedScalarLabel saturatedScalarLabel_injective
    canonical_saturatedScalarLabel_mcaEvent

/-- Operational upper bound on the literal P1 `evalCode` surface. -/
theorem evalCode_commonFactor_mcaDeltaStar_le :
    ProximityGap.MCAThresholdLedger.mcaDeltaStar
        (F := F) (A := F) (evalCode g N (k - 1))
        ((((2 : ℕ) ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞) ≤ δsat := by
  rw [evalCode_eq_canonicalCode]
  exact P1.mcaDeltaStar_le_of_N_add_two_badLabels canonicalCode δsat
    canonicalAmplifiedStack saturatedScalarLabel saturatedCertificate_card
    saturatedScalarLabel_injective canonical_saturatedScalarLabel_mcaEvent

/-- Closed-form improved endpoint on the literal prize code. -/
theorem evalCode_commonFactor_mcaDeltaStar_le_fortyThree_over_ninetySix_correction :
    ProximityGap.MCAThresholdLedger.mcaDeltaStar
        (F := F) (A := F) (evalCode g N (k - 1))
        ((((2 : ℕ) ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞) ≤
      (43 / 96 : ℝ≥0) + 1 / (3 * N : ℕ) := by
  rw [← delta_eq_fortyThree_over_ninetySix_correction]
  exact evalCode_commonFactor_mcaDeltaStar_le

/-- The improved literal-code endpoint is strictly below the rate-quarter
Johnson radius. -/
theorem evalCode_commonFactor_mcaDeltaStar_lt_half :
    ProximityGap.MCAThresholdLedger.mcaDeltaStar
        (F := F) (A := F) (evalCode g N (k - 1))
        ((((2 : ℕ) ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞) <
      (1 / 2 : ℝ≥0) :=
  evalCode_commonFactor_mcaDeltaStar_le.trans_lt (by
    rw [delta_eq_fortyThree_over_ninetySix_correction]
    norm_num [N])

end ArkLib.ProximityGap.Frontier.P1RateQuarterCommonFactorCanonicalBridge

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.P1RateQuarterCommonFactorCanonicalBridge
#print axioms canonical_saturatedScalarLabel_mcaEvent
#print axioms canonical_saturated_badScalar_filter_card_ge_N_add_two
#print axioms evalCode_commonFactor_mcaDeltaStar_le
#print axioms evalCode_commonFactor_mcaDeltaStar_le_fortyThree_over_ninetySix_correction
#print axioms evalCode_commonFactor_mcaDeltaStar_lt_half
