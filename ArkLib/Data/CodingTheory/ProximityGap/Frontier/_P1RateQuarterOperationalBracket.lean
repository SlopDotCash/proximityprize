/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterScaleFinalConsumer
import ArkLib.Data.CodingTheory.ProximityGap.MCAUDRBound

/-!
# A two-sided operational bracket for the first-prime rate-quarter code

The full unique-decoding MCA bound supplies the good side at radius `3/8`.
At this point the literal bad-scalar budget is at most `N`, and the certified
prime satisfies `N/P <= 2^-128`.  The explicit thickened construction supplies
the bad side at `23/48-2/(3N)`.

This does not pin delta-star, but it gives an unconditional two-sided bracket
on the same concrete code and error target.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open _root_.ProximityGap Code
open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterOperationalBracket

open ArkLib.ProximityGap.PrizeShapePrimeP30
open P1RateQuarterScaleArithmetic
open P1RateQuarterScaleConstruction
open P1RateQuarterScaleFinalConsumer

local instance localInstance_P1RateQuarterOperationalBracket_1 : Fact (Nat.Prime P) := ⟨prime_P⟩
local instance localInstance_P1RateQuarterOperationalBracket_2 : NeZero k := ⟨by norm_num [k]⟩

/-- A finite count budget `E * Q ≤ p` gives the normalized `ENNReal` budget
`E / p ≤ Q⁻¹`. -/
theorem natCast_div_le_inv_of_mul_le {E Q p : ℕ}
    (hQ : 0 < Q) (hp : 0 < p) (hbudget : E * Q ≤ p) :
    (E : ℝ≥0∞) / (p : ℝ≥0∞) ≤ ((Q : ℝ≥0∞)⁻¹ : ℝ≥0∞) := by
  have hp0 : (p : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  have hpTop : (p : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top p
  rw [ENNReal.div_le_iff hp0 hpTop]
  have hQ0 : (Q : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  have hQTop : (Q : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top Q
  calc
    (E : ℝ≥0∞) ≤ (E : ℝ≥0∞) * Q * (Q : ℝ≥0∞)⁻¹ := by
      rw [mul_assoc, ENNReal.mul_inv_cancel hQ0 hQTop, mul_one]
    _ ≤ (p : ℝ≥0∞) * (Q : ℝ≥0∞)⁻¹ := by
      gcongr
      exact_mod_cast hbudget
    _ = (Q : ℝ≥0∞)⁻¹ * (p : ℝ≥0∞) := mul_comm _ _

/-- The exact rate-quarter relative unique-decoding radius. -/
noncomputable abbrev lowerDelta : ℝ≥0 := 3 / 8

theorem k_le_card_coord : k ≤ Fintype.card Coord := by
  rw [card_coord]
  norm_num [k, N]

theorem lowerDelta_le_relativeUniqueDecodingRadius :
    lowerDelta ≤ relativeUniqueDecodingRadius
      (ι := Coord) (F := F) (C := ReedSolomon.code domain k) := by
  rw [ReedSolomon.relativeUniqueDecodingRadius_RS_eq' k_le_card_coord,
    card_coord]
  have hrate : (k : ℝ≥0) / (N : ℝ≥0) = 1 / 4 := by
    apply NNReal.coe_injective
    push_cast
    norm_num [k, N]
  rw [hrate]
  have hquarter : (1 / 4 : ℝ≥0) ≤ 1 := by
    rw [← NNReal.coe_le_coe]
    push_cast
    norm_num
  rw [← NNReal.coe_le_coe]
  push_cast [NNReal.coe_sub hquarter]
  norm_num [lowerDelta]

theorem lowerDelta_agreement_ceiling :
    ⌈(1 - lowerDelta) * (Fintype.card Coord : ℝ≥0)⌉₊ = 5 * N / 8 := by
  rw [card_coord]
  have hdelta : lowerDelta ≤ 1 := by
    rw [← NNReal.coe_le_coe]
    push_cast
    norm_num [lowerDelta]
  have hmass :
      (1 - lowerDelta) * (N : ℝ≥0) = ((5 * N / 8 : ℕ) : ℝ≥0) := by
    apply NNReal.coe_injective
    rw [NNReal.coe_mul, NNReal.coe_sub hdelta]
    push_cast
    norm_num [lowerDelta, N]
  rw [hmass, Nat.ceil_natCast]

theorem lowerDelta_full_udr_regime :
    2 * (Fintype.card Coord -
        ⌈(1 - lowerDelta) * (Fintype.card Coord : ℝ≥0)⌉₊) <
      Fintype.card Coord - k + 1 := by
  rw [lowerDelta_agreement_ceiling, card_coord]
  norm_num [N, k]

/-- The unique-decoding bound fits inside the exact prize error budget. -/
theorem epsMCA_lowerDelta_le_prizeEpsilon :
    epsMCA (F := F) (A := F) certificateCode lowerDelta ≤
      ((((2 : ℕ) ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞) := by
  refine (ProximityGap.UDRwire.epsMCA_rs_udr_le_full
    domain k k_le_card_coord lowerDelta
    lowerDelta_le_relativeUniqueDecodingRadius
    lowerDelta_full_udr_regime).trans ?_
  have hbudget : N * 2 ^ 128 ≤ ArkLib.ProximityGap.PrizeShapePrimeP30.P := by
    norm_num [N, ArkLib.ProximityGap.PrizeShapePrimeP30.P]
  simpa only [card_coord, F, ZMod.card] using
    natCast_div_le_inv_of_mul_le (E := N) (Q := 2 ^ 128)
      (p := ArkLib.ProximityGap.PrizeShapePrimeP30.P)
      (by norm_num) (by norm_num [ArkLib.ProximityGap.PrizeShapePrimeP30.P]) hbudget

theorem threeEighths_le_rateQuarter_mcaDeltaStar :
    (3 / 8 : ℝ≥0) ≤
      ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := F)
        certificateCode
        ((((2 : ℕ) ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞) := by
  apply ProximityGap.MCAThresholdLedger.le_mcaDeltaStar_of_good
  · rw [← NNReal.coe_le_coe]
    push_cast
    norm_num
  · exact epsMCA_lowerDelta_le_prizeEpsilon

/-- Unconditional two-sided bracket on the concrete fibre-indexed code. -/
theorem rateQuarter_mcaDeltaStar_mem_operational_bracket :
    (3 / 8 : ℝ≥0) ≤
        ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := F)
          certificateCode
          ((((2 : ℕ) ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞) ∧
      ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := F)
          certificateCode
          ((((2 : ℕ) ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞) ≤
        (23 / 48 : ℝ≥0) - 2 / (3 * N : ℕ) :=
  ⟨threeEighths_le_rateQuarter_mcaDeltaStar,
    rateQuarter_mcaDeltaStar_le_twentyThree_over_fortyEight_correction⟩

end ArkLib.ProximityGap.Frontier.P1RateQuarterOperationalBracket

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.P1RateQuarterOperationalBracket
#print axioms epsMCA_lowerDelta_le_prizeEpsilon
#print axioms threeEighths_le_rateQuarter_mcaDeltaStar
#print axioms rateQuarter_mcaDeltaStar_mem_operational_bracket
