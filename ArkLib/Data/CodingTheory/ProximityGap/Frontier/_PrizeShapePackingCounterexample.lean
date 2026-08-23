/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._PackingBudgetFirstJump
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._PrizeShapePrimeP30

/-!
# A concrete prize-scale low-budget packing ceiling

The certified prime

`P = 2^30 * (2^128 + 192) + 1`

has `floor(P / 2^128) = 2^30` and contains the explicitly certified order-`2^30`
element `PrizeShapePrimeP30.g`.  The overlap-packing theorem therefore applies at the
literal field-normalized budget `B = n`.

For each of the three lower advertised rates `1/4`, `1/8`, and `1/16`, it gives the
unconditional operational ceiling `mcaDeltaStar <= 1/2`.  In particular, a theorem
placing all such tight-budget instances strictly above the Johnson radius cannot be
correct without an additional field-size/budget hypothesis.

This file proves only the bad-side ceiling.  A matching good-side theorem below `1/2`
for the production dimensions is a separate obligation.
-/

set_option autoImplicit false

open scoped NNReal ENNReal
open ProximityGap ProximityGap.MCAThresholdLedger

namespace ArkLib.ProximityGap.PrizeShapePackingCounterexample

open ArkLib.ProximityGap.KKH26
open ArkLib.ProximityGap.PackingBudgetFirstJump
open ArkLib.ProximityGap.PrizeShapePrimeP30

local instance fact_prime_P : Fact (Nat.Prime P) := ⟨prime_P⟩
local instance neZero_n : NeZero (2 ^ 30 : ℕ) := ⟨by norm_num⟩

/-- The certified field has a literal bad point at radius `1/2` for every
dimension from `2` through `2^29-1`.  This is the strict all-stack incidence
counterexample underlying the threshold ceilings below. -/
theorem inv_lt_epsMCA_half_of_two_le_dimension_lt_half
    (k : ℕ) (hk : 2 ≤ k) (hkhalf : k ≤ 2 ^ 29 - 1) :
    (((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞) <
      epsMCA (F := ZMod P) (A := ZMod P)
        (evalCode g (2 ^ 30) (k - 1)) (1 / 2 : ℝ≥0) := by
  exact inv_lt_epsMCA_half_of_floor_eq_length
    (p := P) (n := 2 ^ 30) (k := k) (Q := 2 ^ 128) (g := g)
    orderOf_g (by norm_num) hk (by norm_num) P_div_two_pow_128
    (by simpa using hkhalf) (by norm_num)

/-- The concrete certified field obeys the tight-budget packing ceiling for every
dimension between `2` and one quarter of the block length. -/
theorem mcaDeltaStar_le_half_of_two_le_dimension_le_quarter
    (k : ℕ) (hk : 2 ≤ k) (hkquarter : k ≤ 2 ^ 28) :
    mcaDeltaStar (F := ZMod P) (A := ZMod P)
        (evalCode g (2 ^ 30) (k - 1))
        (((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞)
      ≤ (1 / 2 : ℝ≥0) := by
  apply mcaDeltaStar_le_half_of_floor_eq_length
      (p := P) (n := 2 ^ 30) (k := k) (Q := 2 ^ 128) (g := g)
      orderOf_g (by norm_num) hk (by norm_num) P_div_two_pow_128
  · simpa using hkquarter
  · norm_num

/-- Concrete exact-rate `1/4` instance. -/
theorem rateQuarter_mcaDeltaStar_le_half :
    mcaDeltaStar (F := ZMod P) (A := ZMod P)
        (evalCode g (2 ^ 30) (2 ^ 28 - 1))
        (((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞)
      ≤ (1 / 2 : ℝ≥0) :=
  mcaDeltaStar_le_half_of_two_le_dimension_le_quarter (2 ^ 28) (by norm_num) (by norm_num)

/-- Concrete exact-rate `1/8` instance. -/
theorem rateEighth_mcaDeltaStar_le_half :
    mcaDeltaStar (F := ZMod P) (A := ZMod P)
        (evalCode g (2 ^ 30) (2 ^ 27 - 1))
        (((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞)
      ≤ (1 / 2 : ℝ≥0) :=
  mcaDeltaStar_le_half_of_two_le_dimension_le_quarter (2 ^ 27) (by norm_num) (by norm_num)

/-- Concrete exact-rate `1/16` instance. -/
theorem rateSixteenth_mcaDeltaStar_le_half :
    mcaDeltaStar (F := ZMod P) (A := ZMod P)
        (evalCode g (2 ^ 30) (2 ^ 26 - 1))
        (((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞)
      ≤ (1 / 2 : ℝ≥0) :=
  mcaDeltaStar_le_half_of_two_le_dimension_le_quarter (2 ^ 26) (by norm_num) (by norm_num)

end ArkLib.ProximityGap.PrizeShapePackingCounterexample

#print axioms ArkLib.ProximityGap.PrizeShapePackingCounterexample.mcaDeltaStar_le_half_of_two_le_dimension_le_quarter
#print axioms ArkLib.ProximityGap.PrizeShapePackingCounterexample.inv_lt_epsMCA_half_of_two_le_dimension_lt_half
#print axioms ArkLib.ProximityGap.PrizeShapePackingCounterexample.rateQuarter_mcaDeltaStar_le_half
#print axioms ArkLib.ProximityGap.PrizeShapePackingCounterexample.rateEighth_mcaDeltaStar_le_half
#print axioms ArkLib.ProximityGap.PrizeShapePackingCounterexample.rateSixteenth_mcaDeltaStar_le_half
