/-
Copyright (c) 2026 Mikhail Izhutkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mikhail Izhutkin (mashingaan, @mashingaan)
-/
import Research.ProximityPrize.MCAUDRBound
import Research.ProximityPrize.KKH26RegimeSplit
import Research.ProximityPrize.Frontier._PrizeShapeRateHalfBracket

/-!
# Full unique-decoding floor for the literal first sponsor code

Specializes the existing `UDRwire.epsMCA_rs_udr_le_full` theorem to length
`2^30`, dimension `2^29`, the certified first field and the original `epsStar`.
The mathematical unique-decoding bound is due to the existing BCIKS20 chain.
This module supplies its exact canonical-code and threshold-ledger consumer.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

open scoped NNReal ENNReal
open ProximityGap Code

namespace ProximityGap.FirstSponsorUDRFloor

open ArkLib.ProximityGap.PrizeShapePrimeP30
open ArkLib.ProximityGap.KKH26

local notation "pSponsor" => ArkLib.ProximityGap.PrizeShapePrimeP30.P

local instance : Fact (Nat.Prime pSponsor) := ⟨prime_P⟩
local instance : NeZero (2 ^ 30 : ℕ) := ⟨by norm_num⟩
local instance : NeZero (2 ^ 29 : ℕ) := ⟨by norm_num⟩

theorem generator_ne_zero : ArkLib.ProximityGap.PrizeShapePrimeP30.g ≠ 0 :=
  KKH26RegimeSplit.ne_zero_of_orderOf_eq orderOf_g

def domain : Fin (2 ^ 30) ↪ ZMod pSponsor :=
  KKH26RegimeSplit.powDomain ArkLib.ProximityGap.PrizeShapePrimeP30.g orderOf_g generator_ne_zero

abbrev code : Set (Fin (2 ^ 30) → ZMod pSponsor) :=
  (ReedSolomon.code domain (2 ^ 29) : Submodule (ZMod pSponsor) (Fin (2 ^ 30) → ZMod pSponsor))

theorem canonical_code_eq : evalCode ArkLib.ProximityGap.PrizeShapePrimeP30.g (2 ^ 30) (2 ^ 29 - 1) = code := by
  rw [KKH26RegimeSplit.evalCode_eq_reedSolomon ArkLib.ProximityGap.PrizeShapePrimeP30.g orderOf_g generator_ne_zero
    (2 ^ 29 - 1)]
  norm_num [code, domain]

theorem quarter_le_udr :
    (1 / 4 : ℝ≥0) ≤ relativeUniqueDecodingRadius
      (ι := Fin (2 ^ 30)) (F := ZMod pSponsor) (C := ReedSolomon.code domain (2 ^ 29)) := by
  rw [ReedSolomon.relativeUniqueDecodingRadius_RS_eq'
    (by norm_num : 2 ^ 29 ≤ Fintype.card (Fin (2 ^ 30))), Fintype.card_fin]
  have hrate : ((2 ^ 29 : ℕ) : ℝ≥0) / ((2 ^ 30 : ℕ) : ℝ≥0) = 1 / 2 := by
    apply NNReal.coe_injective
    push_cast
    norm_num
  rw [hrate]
  have hhalf : (1 / 2 : ℝ≥0) ≤ 1 := by
    rw [← NNReal.coe_le_coe]
    push_cast
    norm_num
  rw [← NNReal.coe_le_coe]
  push_cast [NNReal.coe_sub hhalf]
  norm_num

theorem quarter_agreement_ceiling :
    ⌈(1 - (1 / 4 : ℝ≥0)) * (Fintype.card (Fin (2 ^ 30)) : ℝ≥0)⌉₊ =
      805306368 := by
  have hmass : (1 - (1 / 4 : ℝ≥0)) *
      (Fintype.card (Fin (2 ^ 30)) : ℝ≥0) = (805306368 : ℕ) := by
    have hdelta : (1 / 4 : ℝ≥0) ≤ 1 := by
      rw [← NNReal.coe_le_coe]
      push_cast
      norm_num
    apply NNReal.coe_injective
    rw [NNReal.coe_mul, NNReal.coe_sub hdelta]
    push_cast
    norm_num
  rw [hmass, Nat.ceil_natCast]

theorem quarter_full_udr_regime :
    2 * (Fintype.card (Fin (2 ^ 30)) -
      ⌈(1 - (1 / 4 : ℝ≥0)) * (Fintype.card (Fin (2 ^ 30)) : ℝ≥0)⌉₊) <
        Fintype.card (Fin (2 ^ 30)) - 2 ^ 29 + 1 := by
  rw [quarter_agreement_ceiling]
  norm_num

theorem canonical_epsMCA_quarter_le :
    epsMCA (F := ZMod pSponsor) (A := ZMod pSponsor)
      (evalCode ArkLib.ProximityGap.PrizeShapePrimeP30.g (2 ^ 30) (2 ^ 29 - 1)) (1 / 4) ≤ (epsStar : ℝ≥0∞) := by
  rw [canonical_code_eq]
  refine (UDRwire.epsMCA_rs_udr_le_full domain (2 ^ 29)
    (by norm_num) (1 / 4) quarter_le_udr quarter_full_udr_regime).trans ?_
  rw [Fintype.card_fin, ZMod.card]
  have h := ArkLib.ProximityGap.Frontier.PrizeShapeRateHalfBracket.natCast_div_le_inv_of_mul_le
    (E := 2 ^ 30) (Q := 2 ^ 128) (p := pSponsor)
    (by norm_num) prime_P.pos
    (by norm_num [ArkLib.ProximityGap.PrizeShapePrimeP30.P])
  rwa [ArkLib.ProximityGap.Frontier.PrizeShapeRateHalfBracket.epsStar_coe_eq_natCast_inv]

theorem quarter_le_canonical_threshold :
    (1 / 4 : ℝ≥0) ≤ MCAThresholdLedger.mcaDeltaStar
      (F := ZMod pSponsor) (A := ZMod pSponsor)
      (evalCode ArkLib.ProximityGap.PrizeShapePrimeP30.g (2 ^ 30) (2 ^ 29 - 1)) (epsStar : ℝ≥0∞) := by
  apply MCAThresholdLedger.le_mcaDeltaStar_of_good
  · rw [← NNReal.coe_le_coe]
    push_cast
    norm_num
  · exact canonical_epsMCA_quarter_le

end ProximityGap.FirstSponsorUDRFloor

#print axioms ProximityGap.UDRwire.epsMCA_rs_udr_le_full
#print axioms ProximityGap.FirstSponsorUDRFloor.canonical_epsMCA_quarter_le
#print axioms ProximityGap.FirstSponsorUDRFloor.quarter_le_canonical_threshold
