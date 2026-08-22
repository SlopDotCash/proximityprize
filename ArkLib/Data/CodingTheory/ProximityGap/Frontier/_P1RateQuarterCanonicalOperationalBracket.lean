/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._MCAReindexThresholdEquiv
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterCanonicalCodeBridge
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterOperationalBracket

/-!
# A two-sided operational bracket on the literal P1 rate-quarter code

The fibre-indexed construction already carries an unconditional operational
bracket.  The threshold-level coordinate invariance theorem transports that
entire statement to the canonical `Fin N` power domain, and the canonical
code bridge identifies it with the literal `evalCode g N (k - 1)` surface.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open _root_.ProximityGap Code
open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterCanonicalOperationalBracket

open ArkLib.ProximityGap.PrizeShapePrimeP30
open ArkLib.ProximityGap.KKH26
open P1RateQuarterScaleArithmetic
open P1RateQuarterScaleConstruction
open P1RateQuarterCanonicalCodeBridge
open P1RateQuarterScaleFinalConsumer
open P1RateQuarterOperationalBracket
open MCAReindexThresholdEquiv

local instance localInstance_P1RateQuarterCanonicalOperationalBracket_1 : Fact (Nat.Prime P) := ⟨prime_P⟩
local instance localInstance_P1RateQuarterCanonicalOperationalBracket_2 : NeZero N := ⟨by norm_num [N]⟩

local notation "epsilonP1" =>
  ((((2 : ℕ) ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞)

/-- The canonical and fibre-indexed prize thresholds are exactly equal. -/
theorem canonical_mcaDeltaStar_eq_fibre_mcaDeltaStar :
    ProximityGap.MCAThresholdLedger.mcaDeltaStar
        (F := F) (A := F) canonicalCode epsilonP1 =
      ProximityGap.MCAThresholdLedger.mcaDeltaStar
        (F := F) (A := F)
        P1RateQuarterScaleFinalConsumer.certificateCode epsilonP1 := by
  exact mcaDeltaStar_reindex_reedSolomon_eq coordEquiv domain canonicalDomain
    domain_eq_canonicalDomain k epsilonP1

/-- Operational lower bracket for the literal prize code. -/
theorem threeEighths_le_evalCode_rateQuarter_mcaDeltaStar :
    (3 / 8 : ℝ≥0) ≤
      ProximityGap.MCAThresholdLedger.mcaDeltaStar
        (F := F) (A := F) (evalCode g N (k - 1)) epsilonP1 := by
  rw [evalCode_eq_canonicalCode, canonical_mcaDeltaStar_eq_fibre_mcaDeltaStar]
  exact threeEighths_le_rateQuarter_mcaDeltaStar

/-- Unconditional two-sided bracket on the literal `evalCode` surface. -/
theorem evalCode_rateQuarter_mcaDeltaStar_mem_operational_bracket :
    (3 / 8 : ℝ≥0) ≤
        ProximityGap.MCAThresholdLedger.mcaDeltaStar
          (F := F) (A := F) (evalCode g N (k - 1)) epsilonP1 ∧
      ProximityGap.MCAThresholdLedger.mcaDeltaStar
          (F := F) (A := F) (evalCode g N (k - 1)) epsilonP1 ≤
        (23 / 48 : ℝ≥0) - 2 / (3 * N : ℕ) :=
  ⟨threeEighths_le_evalCode_rateQuarter_mcaDeltaStar,
    evalCode_rateQuarter_mcaDeltaStar_le_advertised⟩

end ArkLib.ProximityGap.Frontier.P1RateQuarterCanonicalOperationalBracket

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.P1RateQuarterCanonicalOperationalBracket
#print axioms canonical_mcaDeltaStar_eq_fibre_mcaDeltaStar
#print axioms threeEighths_le_evalCode_rateQuarter_mcaDeltaStar
#print axioms evalCode_rateQuarter_mcaDeltaStar_mem_operational_bracket
