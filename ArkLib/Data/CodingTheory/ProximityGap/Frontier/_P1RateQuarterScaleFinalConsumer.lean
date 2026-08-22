/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterScaleBadCount
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterScaleOperationalCountConnector

/-!
# The prize-scale rate-quarter operational consumer

The construction and bad-count modules supply the three unsafe hole events and the injective
`N - 1 + 3` scalar certificate.  This consumer identifies that certificate with the literal
bad-event filter, derives its `epsMCA` mass, and records the resulting operational upper ledger
at `delta = 23/48 - 2/(3N)` and prize error `2^-128`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open _root_.ProximityGap Code
open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterScaleFinalConsumer

open ArkLib.ProximityGap.PrizeShapePrimeP30
open P1RateQuarterScaleArithmetic
open P1RateQuarterScaleConstruction
open P1RateQuarterScaleOperationalCountConnector

local instance localInstance_P1RateQuarterScaleFinalConsumer_1 : Fact (Nat.Prime P) := ⟨prime_P⟩
attribute [local instance] Classical.propDecidable

/-- The concrete rate-quarter Reed--Solomon code as a set. -/
abbrev certificateCode : Set (Coord → F) :=
  (ReedSolomon.code domain k : Submodule F (Coord → F))

/-- The `N - 1` safe labels and three unsafe hole labels as one finite set. -/
noncomputable def certificateLabels : Finset F :=
  P1RateQuarterScaleBadCount.badScalars

/-- In particular, the construction supplies all three unsafe hole events. -/
theorem three_unsafe_hole_events (i : Fin 3) :
    mcaEvent certificateCode delta (u 0) (u 1)
      (P1RateQuarterScaleBadCount.unsafeGamma i) :=
  P1RateQuarterScaleBadCount.unsafe_mcaEvent i

/-- The safe labels and three unsafe labels are distinct, giving exactly `N+2` scalars. -/
theorem certificateLabels_card : certificateLabels.card = N + 2 := by
  exact P1RateQuarterScaleBadCount.badScalars_card

/-- Literal filter form of the strict count, with no incidence proxy in the statement. -/
theorem N_lt_badScalar_filter_card :
    N < (Finset.univ.filter fun gamma : F =>
      mcaEvent certificateCode delta (u 0) (u 1) gamma).card := by
  exact lt_of_lt_of_le (by omega : N < N + 2)
    P1RateQuarterScaleBadCount.badScalar_filter_card_ge_N_add_two

/-- The `N+2` scalar family gives its normalized lower bound on `epsMCA`. -/
theorem rateQuarter_epsMCA_lower_bound :
    ((N + 2 : ℕ) : ℝ≥0∞) / (P : ℝ≥0∞) ≤
      epsMCA (F := F) (A := F) certificateCode delta := by
  exact epsMCA_ge_N_add_two_div_P_of_badScalar_filter_card
    certificateCode u
    P1RateQuarterScaleBadCount.badScalar_filter_card_ge_N_add_two

/-- The certificate mass is strictly larger than the prize error `2^-128`. -/
theorem prizeEpsilon_lt_certificateMass :
    ((((2 : ℕ) ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞) <
      ((N + 2 : ℕ) : ℝ≥0∞) / (P : ℝ≥0∞) := by
  exact prizeEpsilon_lt_N_add_two_div_P

theorem prizeEpsilon_lt_rateQuarter_epsMCA :
    ((((2 : ℕ) ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞) <
      epsMCA (F := F) (A := F) certificateCode delta :=
  prizeEpsilon_lt_certificateMass.trans_le rateQuarter_epsMCA_lower_bound

/-- The prize error is already exceeded at the rate-quarter Johnson radius. -/
theorem prizeEpsilon_lt_rateQuarter_epsMCA_half :
    ((((2 : ℕ) ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞) <
      epsMCA (F := F) (A := F) certificateCode (1 / 2) :=
  prizeEpsilon_lt_rateQuarter_epsMCA.trans_le
    (epsMCA_mono certificateCode delta_lt_half.le)

/-- Operational prize-scale upper ledger at the strongest thickened rate-quarter radius. -/
theorem rateQuarter_mcaDeltaStar_le :
    ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := F)
        certificateCode
        ((((2 : ℕ) ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞) ≤
      delta :=
  ProximityGap.MCAThresholdLedger.mcaDeltaStar_le_of_bad _ _
    prizeEpsilon_lt_rateQuarter_epsMCA

/-- The operational threshold lies strictly below the rate-quarter Johnson
radius `1-sqrt(1/4)=1/2`. -/
theorem rateQuarter_mcaDeltaStar_lt_half :
    ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := F)
        certificateCode
        ((((2 : ℕ) ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞) <
      (1 / 2 : ℝ≥0) :=
  rateQuarter_mcaDeltaStar_le.trans_lt delta_lt_half

/-- The ledger radius has the advertised correction below `23/48`. -/
theorem rateQuarter_mcaDeltaStar_le_twentyThree_over_fortyEight_correction :
    ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := F)
        certificateCode
        ((((2 : ℕ) ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞) ≤
      (23 / 48 : ℝ≥0) - 2 / (3 * N : ℕ) := by
  rw [← delta_eq_twentyThree_over_fortyEight_correction]
  exact rateQuarter_mcaDeltaStar_le

#print axioms N_lt_badScalar_filter_card
#print axioms rateQuarter_epsMCA_lower_bound
#print axioms prizeEpsilon_lt_rateQuarter_epsMCA_half
#print axioms rateQuarter_mcaDeltaStar_lt_half
#print axioms rateQuarter_mcaDeltaStar_le_twentyThree_over_fortyEight_correction

end ArkLib.ProximityGap.Frontier.P1RateQuarterScaleFinalConsumer
