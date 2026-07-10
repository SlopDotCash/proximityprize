/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._PackingPrizeP30Ceilings
import ArkLib.Data.CodingTheory.ProximityGap.RatesBracket

/-!
# A prize-shaped operational threshold below Johnson

For the certified prime

`P = 2^30 * (2^128 + 192) + 1`,

overlap packing gives an operational MCA threshold ceiling of `1/2` at
security `2^-128` for rates `1/4`, `1/8`, and `1/16`.  This file records the
consequential Johnson comparison: the ceiling is strictly below Johnson at
rates `1/8` and `1/16`, and equals Johnson at rate `1/4`.  Hence every radius in
the advertised open above-Johnson window violates the target MCA budget.
-/

set_option autoImplicit false

open scoped NNReal ENNReal
open ProximityGap ProximityGap.MCAThresholdLedger
open ArkLib.ProximityGap.KKH26

namespace ArkLib.ProximityGap.Frontier.PrizeShapeFirstPrimeBelowJohnson

open ArkLib.ProximityGap

local instance firstPrimeFact : Fact (Nat.Prime PrizeShapePrimeP30.P) :=
  ⟨PrizeShapePrimeP30.prime_P⟩

noncomputable abbrev firstPrimeRateEighthThreshold : ℝ≥0 :=
  mcaDeltaStar
    (F := ZMod PrizeShapePrimeP30.P) (A := ZMod PrizeShapePrimeP30.P)
    (evalCode PrizeShapePrimeP30.g (2 ^ 30) (2 ^ 27 - 1))
    (((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞)

noncomputable abbrev firstPrimeRateQuarterThreshold : ℝ≥0 :=
  mcaDeltaStar
    (F := ZMod PrizeShapePrimeP30.P) (A := ZMod PrizeShapePrimeP30.P)
    (evalCode PrizeShapePrimeP30.g (2 ^ 30) (2 ^ 28 - 1))
    (((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞)

noncomputable abbrev firstPrimeRateSixteenthThreshold : ℝ≥0 :=
  mcaDeltaStar
    (F := ZMod PrizeShapePrimeP30.P) (A := ZMod PrizeShapePrimeP30.P)
    (evalCode PrizeShapePrimeP30.g (2 ^ 30) (2 ^ 26 - 1))
    (((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞)

/-- **Rate one eighth is below Johnson.**  The certified operational threshold
is at most `1/2`, while `1-sqrt(1/8) > 0.64644`. -/
theorem firstPrime_rateEighth_deltaStar_lt_johnson :
    (firstPrimeRateEighthThreshold : ℝ) <
      1 - Real.sqrt (1 / 8 : ℝ) := by
  unfold firstPrimeRateEighthThreshold
  have hhalf :
      ((mcaDeltaStar
        (F := ZMod PrizeShapePrimeP30.P) (A := ZMod PrizeShapePrimeP30.P)
        (evalCode PrizeShapePrimeP30.g (2 ^ 30) (2 ^ 27 - 1))
        (((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞) : ℝ≥0) : ℝ) ≤ 1 / 2 := by
    exact_mod_cast
      ArkLib.ProximityGap.PackingPrizeP30Ceilings.rateEighth_mcaDeltaStar_le_half
  exact lt_of_le_of_lt hhalf <|
    lt_trans (by norm_num : (1 / 2 : ℝ) < 0.64644)
      ArkLib.CodingTheory.PrizeRatesBracket.bracket_rate_eighth.1

/-- **Rate one quarter reaches at most Johnson.**  Here Johnson is exactly
`1/2`, and overlap packing supplies the matching operational ceiling. -/
theorem firstPrime_rateQuarter_deltaStar_le_johnson :
    (firstPrimeRateQuarterThreshold : ℝ) ≤
      1 - Real.sqrt (1 / 4 : ℝ) := by
  unfold firstPrimeRateQuarterThreshold
  rw [ArkLib.CodingTheory.PrizeRatesBracket.bracket_rate_quarter.1]
  exact_mod_cast
    ArkLib.ProximityGap.PackingPrizeP30Ceilings.rateQuarter_mcaDeltaStar_le_half

/-- **Rate one sixteenth is below Johnson.**  The certified operational
threshold is at most `1/2`, while the Johnson radius is exactly `3/4`. -/
theorem firstPrime_rateSixteenth_deltaStar_lt_johnson :
    (firstPrimeRateSixteenthThreshold : ℝ) <
      1 - Real.sqrt (1 / 16 : ℝ) := by
  unfold firstPrimeRateSixteenthThreshold
  rw [ArkLib.CodingTheory.PrizeRatesBracket.bracket_rate_sixteenth.1]
  have hhalf :
      mcaDeltaStar
        (F := ZMod PrizeShapePrimeP30.P) (A := ZMod PrizeShapePrimeP30.P)
        (evalCode PrizeShapePrimeP30.g (2 ^ 30) (2 ^ 26 - 1))
        (((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞) ≤ (1 / 2 : ℝ≥0) :=
    ArkLib.ProximityGap.PackingPrizeP30Ceilings.rateSixteenth_mcaDeltaStar_le_half
  exact lt_of_le_of_lt (by exact_mod_cast hhalf) (by norm_num)

/-- The advertised above-Johnson lower bracket is false for the first
prize-shaped rate-`1/8` operational instance. -/
theorem not_johnson_le_firstPrime_rateEighth_deltaStar :
    ¬(1 - Real.sqrt (1 / 8 : ℝ) ≤
      (firstPrimeRateEighthThreshold : ℝ)) :=
  not_le.mpr firstPrime_rateEighth_deltaStar_lt_johnson

/-- The same failure at rate `1/16`. -/
theorem not_johnson_le_firstPrime_rateSixteenth_deltaStar :
    ¬(1 - Real.sqrt (1 / 16 : ℝ) ≤
      (firstPrimeRateSixteenthThreshold : ℝ)) :=
  not_le.mpr firstPrime_rateSixteenth_deltaStar_lt_johnson

open Classical in
/-- If an operational threshold lies below a real radius `J`, then no radius
at or above `J` can satisfy the target budget. -/
theorem not_good_at_or_above_of_deltaStar_lt
    {F : Type} [Field F] [Fintype F]
    {n : Nat} [NeZero n] (C : Set (Fin n → F)) (epsilonStar : ℝ≥0∞)
    (J : ℝ) (hbelow : ((mcaDeltaStar (F := F) (A := F) C epsilonStar : ℝ≥0) : ℝ) < J)
    (delta : ℝ≥0) (hJ : J ≤ (delta : ℝ)) (hdelta : delta ≤ 1) :
    ¬epsMCA (F := F) (A := F) C delta ≤ epsilonStar := by
  intro hgood
  have hle := le_mcaDeltaStar_of_good
    (F := F) (A := F) C epsilonStar hdelta hgood
  have hleR : (delta : ℝ) ≤
      ((mcaDeltaStar (F := F) (A := F) C epsilonStar : ℝ≥0) : ℝ) := by
    exact_mod_cast hle
  linarith

/-- **The entire advertised rate-`1/8` Johnson window misses the security
budget** for the first certified prize-shaped field. -/
theorem firstPrime_rateEighth_not_good_at_or_above_johnson
    (delta : ℝ≥0)
    (hJ : 1 - Real.sqrt (1 / 8 : ℝ) ≤ (delta : ℝ))
    (hdelta : delta ≤ 1) :
    ¬epsMCA
      (F := ZMod PrizeShapePrimeP30.P) (A := ZMod PrizeShapePrimeP30.P)
      (evalCode PrizeShapePrimeP30.g (2 ^ 30) (2 ^ 27 - 1)) delta ≤
        (((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞) := by
  apply not_good_at_or_above_of_deltaStar_lt
    (evalCode PrizeShapePrimeP30.g (2 ^ 30) (2 ^ 27 - 1))
    (((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞)
    (1 - Real.sqrt (1 / 8 : ℝ))
    firstPrime_rateEighth_deltaStar_lt_johnson delta hJ hdelta

/-- The same empty operational Johnson window at rate `1/16`. -/
theorem firstPrime_rateSixteenth_not_good_at_or_above_johnson
    (delta : ℝ≥0)
    (hJ : 1 - Real.sqrt (1 / 16 : ℝ) ≤ (delta : ℝ))
    (hdelta : delta ≤ 1) :
    ¬epsMCA
      (F := ZMod PrizeShapePrimeP30.P) (A := ZMod PrizeShapePrimeP30.P)
      (evalCode PrizeShapePrimeP30.g (2 ^ 30) (2 ^ 26 - 1)) delta ≤
        (((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞) := by
  apply not_good_at_or_above_of_deltaStar_lt
    (evalCode PrizeShapePrimeP30.g (2 ^ 30) (2 ^ 26 - 1))
    (((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞)
    (1 - Real.sqrt (1 / 16 : ℝ))
    firstPrime_rateSixteenth_deltaStar_lt_johnson delta hJ hdelta

/-- **The entire advertised open rate-`1/4` Johnson window misses the security
budget.**  The threshold ceiling equals Johnson, so this statement uses the
strict lower endpoint of the advertised window. -/
theorem firstPrime_rateQuarter_not_good_above_johnson
    (delta : ℝ≥0)
    (hJ : 1 - Real.sqrt (1 / 4 : ℝ) < (delta : ℝ))
    (hdelta : delta ≤ 1) :
    ¬epsMCA
      (F := ZMod PrizeShapePrimeP30.P) (A := ZMod PrizeShapePrimeP30.P)
      (evalCode PrizeShapePrimeP30.g (2 ^ 30) (2 ^ 28 - 1)) delta ≤
        (((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞) := by
  intro hgood
  have hhalfR : (1 / 2 : ℝ) < (delta : ℝ) := by
    rw [← ArkLib.CodingTheory.PrizeRatesBracket.bracket_rate_quarter.1]
    exact hJ
  have hle := le_mcaDeltaStar_of_good
    (F := ZMod PrizeShapePrimeP30.P) (A := ZMod PrizeShapePrimeP30.P)
    (evalCode PrizeShapePrimeP30.g (2 ^ 30) (2 ^ 28 - 1))
    (((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞) hdelta hgood
  have hleR : (delta : ℝ) ≤ (1 / 2 : ℝ) := by
    exact_mod_cast hle.trans
      ArkLib.ProximityGap.PackingPrizeP30Ceilings.rateQuarter_mcaDeltaStar_le_half
  exact (not_lt_of_ge hleR) hhalfR

#print axioms firstPrime_rateEighth_deltaStar_lt_johnson
#print axioms firstPrime_rateQuarter_deltaStar_le_johnson
#print axioms firstPrime_rateSixteenth_deltaStar_lt_johnson
#print axioms not_johnson_le_firstPrime_rateEighth_deltaStar
#print axioms not_johnson_le_firstPrime_rateSixteenth_deltaStar
#print axioms firstPrime_rateEighth_not_good_at_or_above_johnson
#print axioms firstPrime_rateSixteenth_not_good_at_or_above_johnson
#print axioms firstPrime_rateQuarter_not_good_above_johnson

end ArkLib.ProximityGap.Frontier.PrizeShapeFirstPrimeBelowJohnson
