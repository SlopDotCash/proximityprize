/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._PrizeShapeLowRateExactPins
import ArkLib.Data.CodingTheory.ProximityGap.RatesBracket

/-!
# A prize-shaped operational threshold below Johnson

For the certified prime

`P = 2^30 * (2^128 + 192) + 1`,

the exact rate-`1/8` and rate-`1/16` operational MCA thresholds at security
`2^-128` are both `1/2`.  This file records the consequential comparison that
was absent from the original prize dossier: both values lie strictly below
the corresponding Johnson radii.

The second certified prime has the same length, rate `1/16`, and security
target but threshold strictly above `1/2`.  Thus the operational threshold is
genuinely field-sensitive in this prize-shaped regime.
-/

set_option autoImplicit false

open scoped NNReal ENNReal
open ProximityGap ProximityGap.MCAThresholdLedger
open ArkLib.ProximityGap.KKH26
open ArkLib.ProximityGap.Frontier.PrizeShapeLowRateExactPins

namespace ArkLib.ProximityGap.Frontier.PrizeShapeFirstPrimeBelowJohnson

open ArkLib.ProximityGap

local instance firstPrimeFact : Fact (Nat.Prime PrizeShapePrimeP30.P) :=
  ⟨PrizeShapePrimeP30.prime_P⟩

local instance secondPrimeFact : Fact (Nat.Prime PrizeShapePrimeP30Second.P) :=
  ⟨PrizeShapePrimeP30Second.prime_P⟩

noncomputable abbrev firstPrimeRateEighthThreshold : ℝ≥0 :=
  mcaDeltaStar
    (F := ZMod PrizeShapePrimeP30.P) (A := ZMod PrizeShapePrimeP30.P)
    (evalCode PrizeShapePrimeP30.g (2 ^ 30) (2 ^ 27 - 1))
    (((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞)

noncomputable abbrev firstPrimeRateSixteenthThreshold : ℝ≥0 :=
  mcaDeltaStar
    (F := ZMod PrizeShapePrimeP30.P) (A := ZMod PrizeShapePrimeP30.P)
    (evalCode PrizeShapePrimeP30.g (2 ^ 30) (2 ^ 26 - 1))
    (((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞)

noncomputable abbrev secondPrimeRateSixteenthThreshold : ℝ≥0 :=
  mcaDeltaStar
    (F := ZMod PrizeShapePrimeP30Second.P)
    (A := ZMod PrizeShapePrimeP30Second.P)
    (evalCode PrizeShapePrimeP30Second.g (2 ^ 30) (2 ^ 26 - 1))
    (((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞)

/-- **Rate one eighth is below Johnson.**  The certified operational threshold
is `1/2`, while `1-sqrt(1/8) > 0.64644`. -/
theorem firstPrime_rateEighth_deltaStar_lt_johnson :
    (firstPrimeRateEighthThreshold : ℝ) <
      1 - Real.sqrt (1 / 8 : ℝ) := by
  unfold firstPrimeRateEighthThreshold
  rw [firstPrime_rateEighth_deltaStar_eq_half]
  exact lt_trans (by norm_num : (1 / 2 : ℝ) < 0.64644)
    ArkLib.CodingTheory.PrizeRatesBracket.bracket_rate_eighth.1

/-- **Rate one sixteenth is below Johnson.**  The certified operational
threshold is `1/2`, while the Johnson radius is exactly `3/4`. -/
theorem firstPrime_rateSixteenth_deltaStar_lt_johnson :
    (firstPrimeRateSixteenthThreshold : ℝ) <
      1 - Real.sqrt (1 / 16 : ℝ) := by
  unfold firstPrimeRateSixteenthThreshold
  rw [firstPrime_rateSixteenth_deltaStar_eq_half,
    ArkLib.CodingTheory.PrizeRatesBracket.bracket_rate_sixteenth.1]
  norm_num

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

/-- **Prize-shaped field sensitivity.**  At fixed length `2^30`, rate
`1/16`, and security target `2^-128`, the first certified field has threshold
exactly `1/2`, whereas the second certified field has threshold strictly
larger than `1/2`. -/
theorem prizeShape_rateSixteenth_threshold_field_sensitive :
    firstPrimeRateSixteenthThreshold < secondPrimeRateSixteenthThreshold := by
  unfold firstPrimeRateSixteenthThreshold secondPrimeRateSixteenthThreshold
  rw [firstPrime_rateSixteenth_deltaStar_eq_half]
  exact secondPrime_rateSixteenth_half_lt_deltaStar

/-- If an operational threshold lies below a real radius `J`, then no radius
at or above `J` can satisfy the target budget. -/
theorem not_good_at_or_above_of_deltaStar_lt
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
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

#print axioms firstPrime_rateEighth_deltaStar_lt_johnson
#print axioms firstPrime_rateSixteenth_deltaStar_lt_johnson
#print axioms not_johnson_le_firstPrime_rateEighth_deltaStar
#print axioms not_johnson_le_firstPrime_rateSixteenth_deltaStar
#print axioms prizeShape_rateSixteenth_threshold_field_sensitive
#print axioms firstPrime_rateEighth_not_good_at_or_above_johnson
#print axioms firstPrime_rateSixteenth_not_good_at_or_above_johnson

end ArkLib.ProximityGap.Frontier.PrizeShapeFirstPrimeBelowJohnson
