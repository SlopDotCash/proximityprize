/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._PackingBudgetFirstJump
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._PrizeShapePrimeP30

/-!
# Concrete tight-budget packing ceilings at the prize-shaped `2^30` field

The certified prime in `_PrizeShapePrimeP30` has

* `P / 2^128 = 2^30`, and
* an explicit element `g : ZMod P` of order `2^30`.

The overlap packing therefore gives an unconditional bad point at radius `1/2` for the
rate-`1/4`, rate-`1/8`, and rate-`1/16` Reed--Solomon codes on this smooth domain.  These are
the faithful operational `mcaDeltaStar` ceilings; no far-line, monomial-extremality, or
catalogue-completeness hypothesis occurs below.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped NNReal ENNReal
open ProximityGap ProximityGap.MCAThresholdLedger
open ArkLib.ProximityGap.KKH26
open ArkLib.ProximityGap.PackingBudgetFirstJump

namespace ArkLib.ProximityGap.PackingPrizeP30Ceilings

open PrizeShapePrimeP30

local instance : Fact (Nat.Prime P) := ⟨prime_P⟩
local instance : NeZero (2 ^ 30 : ℕ) := ⟨by norm_num⟩

/-- At rate `1/4` (`k = 2^28`), the faithful operational threshold is at most `1/2`,
the Johnson radius. -/
theorem rateQuarter_mcaDeltaStar_le_half :
    mcaDeltaStar (F := ZMod P) (A := ZMod P)
        (evalCode g (2 ^ 30) (2 ^ 28 - 1))
        (((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞)
      ≤ (1 / 2 : ℝ≥0) := by
  refine mcaDeltaStar_le_half_of_floor_eq_length
    (p := P) (n := 2 ^ 30) (k := 2 ^ 28) (Q := 2 ^ 128) (g := g)
    orderOf_g (by norm_num) (by norm_num) (by norm_num) P_div_two_pow_128
    (by norm_num) ?_
  norm_num

/-- At rate `1/8` (`k = 2^27`), the faithful operational threshold is at most `1/2`,
strictly below the Johnson radius. -/
theorem rateEighth_mcaDeltaStar_le_half :
    mcaDeltaStar (F := ZMod P) (A := ZMod P)
        (evalCode g (2 ^ 30) (2 ^ 27 - 1))
        (((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞)
      ≤ (1 / 2 : ℝ≥0) := by
  refine mcaDeltaStar_le_half_of_floor_eq_length
    (p := P) (n := 2 ^ 30) (k := 2 ^ 27) (Q := 2 ^ 128) (g := g)
    orderOf_g (by norm_num) (by norm_num) (by norm_num) P_div_two_pow_128
    (by norm_num) ?_
  norm_num

/-- At rate `1/16` (`k = 2^26`), the faithful operational threshold is at most `1/2`,
strictly below the Johnson radius `3/4`. -/
theorem rateSixteenth_mcaDeltaStar_le_half :
    mcaDeltaStar (F := ZMod P) (A := ZMod P)
        (evalCode g (2 ^ 30) (2 ^ 26 - 1))
        (((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞)
      ≤ (1 / 2 : ℝ≥0) := by
  refine mcaDeltaStar_le_half_of_floor_eq_length
    (p := P) (n := 2 ^ 30) (k := 2 ^ 26) (Q := 2 ^ 128) (g := g)
    orderOf_g (by norm_num) (by norm_num) (by norm_num) P_div_two_pow_128
    (by norm_num) ?_
  norm_num

/-- The three prize rates below `1/2`, packaged as one audit-facing result. -/
theorem three_lower_prize_rates_mcaDeltaStar_le_half :
    mcaDeltaStar (F := ZMod P) (A := ZMod P)
          (evalCode g (2 ^ 30) (2 ^ 28 - 1))
          (((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞) ≤ (1 / 2 : ℝ≥0) ∧
      mcaDeltaStar (F := ZMod P) (A := ZMod P)
          (evalCode g (2 ^ 30) (2 ^ 27 - 1))
          (((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞) ≤ (1 / 2 : ℝ≥0) ∧
      mcaDeltaStar (F := ZMod P) (A := ZMod P)
          (evalCode g (2 ^ 30) (2 ^ 26 - 1))
          (((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞) ≤ (1 / 2 : ℝ≥0) :=
  ⟨rateQuarter_mcaDeltaStar_le_half, rateEighth_mcaDeltaStar_le_half,
    rateSixteenth_mcaDeltaStar_le_half⟩

end ArkLib.ProximityGap.PackingPrizeP30Ceilings

/-! ## Axiom audit -/

#print axioms ArkLib.ProximityGap.PackingPrizeP30Ceilings.rateQuarter_mcaDeltaStar_le_half
#print axioms ArkLib.ProximityGap.PackingPrizeP30Ceilings.rateEighth_mcaDeltaStar_le_half
#print axioms ArkLib.ProximityGap.PackingPrizeP30Ceilings.rateSixteenth_mcaDeltaStar_le_half
