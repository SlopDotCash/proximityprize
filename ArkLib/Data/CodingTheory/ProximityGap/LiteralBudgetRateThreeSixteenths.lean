/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LiteralBudgetPin
import ArkLib.Data.CodingTheory.ProximityGap.Mu6DeepRung

/-!
# Two literal-budget exact pins at rate `3/16`

`LiteralBudgetPin` certifies a prime `P = 1314883 * 2^128 + 1`, an order-32 generator,
and the literal-budget `r = 8` pin.  The same field lies in the adjacent `r = 7` band:

* `floor(choose(32, 7) / 7) = 480836 <= floor(P / 2^128) = 1314883`;
* `floor(P / 2^128) = 1314883 < 2^7 * choose(16, 7) = 1464320`.

Consequently the dimension-6 code has

`mcaDeltaStar(evalCode g 32 5, 2^-128) = 25/32`.

This code has rate `6/32 = 3/16`.  `Mu6DeepRung` independently pins the dimension-12,
length-64 code at the same rate and normalized error threshold `epsilon* = 2^-128` to `51/64`.
Their exact thresholds differ by `1/64`.  Thus there is no universal finite-instance exact
identity depending only on `(rate, epsilon*)`; length, field budget, or finer code data must
remain in any such identity.

The two pins use different certified prime fields and hence different integer bad-scalar
budgets.  The comparison does not refute formulas that retain the length, field size,
`floor(|F| * epsilon*)`, or a fixed field-scaling regime.
-/

set_option autoImplicit false

open scoped NNReal ENNReal
open ProximityGap ProximityGap.MCAThresholdLedger
open ArkLib.ProximityGap.KKH26
open ProximityGap.StaircaseBandTheorem

namespace ArkLib.ProximityGap.LiteralBudgetRateThreeSixteenths

open ArkLib.ProximityGap.LiteralBudgetPin

local instance fact_prime_literal_P : Fact (Nat.Prime LiteralBudgetPin.P) :=
  ⟨LiteralBudgetPin.prime_P⟩

local instance fact_prime_mu6_P : Fact (Nat.Prime Mu6DeepRung.P) :=
  ⟨Mu6DeepRung.prime_P⟩

private theorem choose_32_7 : (32 : ℕ).choose 7 = 3365856 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide

private theorem choose_16_7 : (16 : ℕ).choose 7 = 11440 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide

/-- **The omitted adjacent literal-budget pin.**  At rate `6/32 = 3/16`, the exact
operational threshold is one Hamming rung below capacity: `25/32`. -/
theorem deltaStar_pin_literal_budget_dimSix :
    mcaDeltaStar (F := ZMod LiteralBudgetPin.P) (A := ZMod LiteralBudgetPin.P)
        (evalCode
          (365776689002390431616511545157923604483360578 : ZMod LiteralBudgetPin.P)
          32 5)
        (1 / 2 ^ 128)
      = 25 / 32 := by
  haveI : NeZero (32 : ℕ) := ⟨by norm_num⟩
  have h := KKH26CeilingMarch.kkh26_march_deltaStar_pin
    (p := LiteralBudgetPin.P) (μ := 5) (r := 7)
    (g := (365776689002390431616511545157923604483360578 :
      ZMod LiteralBudgetPin.P))
    (n := 32) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by exact LiteralBudgetPin.orderOf_gP) (by norm_num)
    (1 / 2 ^ 128) ?hlo ?hhi
  case hlo =>
    have hc : ((32 : ℕ).choose 7 / 7 : ℕ) = 480836 := by
      rw [choose_32_7]
    rw [hc]
    exact band_lo_general (by norm_num) (by norm_num)
  case hhi =>
    have hc : (2 ^ 7 * (2 ^ (5 - 1)).choose 7 : ℕ) = 1464320 := by
      show (2 ^ 7 * (16 : ℕ).choose 7 : ℕ) = 1464320
      rw [choose_16_7]
      norm_num
    rw [hc]
    exact band_hi_general (e := 1464319) (q := LiteralBudgetPin.P) (by norm_num)
  rw [h]
  have e7 : (((7 : ℕ)) : ℝ≥0) = (7 : ℝ≥0) := by norm_num
  rw [e7]
  have hd : (7 : ℝ≥0) / ((2 : ℝ≥0) ^ 5) = 7 / 32 := by norm_num
  rw [hd]
  refine tsub_eq_of_eq_add ?_
  norm_num

/-- The two exact pins have the same actual rate `3/16` and normalized error threshold
`epsilon* = 2^-128`. -/
theorem literal_rate_three_sixteenths_two_scale_profile :
    ((6 : ℝ≥0) / 32 = 3 / 16) ∧
    ((12 : ℝ≥0) / 64 = 3 / 16) ∧
    mcaDeltaStar (F := ZMod LiteralBudgetPin.P) (A := ZMod LiteralBudgetPin.P)
        (evalCode
          (365776689002390431616511545157923604483360578 :
            ZMod LiteralBudgetPin.P)
          32 5)
        (1 / 2 ^ 128)
      = 25 / 32 ∧
    mcaDeltaStar (F := ZMod Mu6DeepRung.P) (A := ZMod Mu6DeepRung.P)
        (evalCode
          (218028241209259214929338402535096146560619661187581 :
            ZMod Mu6DeepRung.P)
          64 11)
        (1 / 2 ^ 128)
      = 51 / 64 := by
  refine ⟨by norm_num, by norm_num, deltaStar_pin_literal_budget_dimSix, ?_⟩
  exact Mu6DeepRung.deltaStar_pin_mu6_dim12

/-- At the same rate and normalized error threshold, the length-64 exact threshold exceeds
the length-32 threshold by exactly one length-64 Hamming rung. -/
theorem literal_rate_three_sixteenths_two_scale_drift :
    mcaDeltaStar (F := ZMod Mu6DeepRung.P) (A := ZMod Mu6DeepRung.P)
        (evalCode
          (218028241209259214929338402535096146560619661187581 : ZMod Mu6DeepRung.P)
          64 11)
        (1 / 2 ^ 128)
      - mcaDeltaStar (F := ZMod LiteralBudgetPin.P) (A := ZMod LiteralBudgetPin.P)
          (evalCode
            (365776689002390431616511545157923604483360578 :
              ZMod LiteralBudgetPin.P)
            32 5)
          (1 / 2 ^ 128)
      = 1 / 64 := by
  rw [Mu6DeepRung.deltaStar_pin_mu6_dim12, deltaStar_pin_literal_budget_dimSix]
  refine tsub_eq_of_eq_add ?_
  norm_num

/-- **A concrete counterexample to universal finite-instance rate-and-error-only identities.**
The two explicit codes have the same rate `3/16` and normalized error threshold `2^-128`, but
different lengths, fields, integer budgets, and operational thresholds. -/
theorem literal_rate_only_threshold_REFUTED :
    ((6 : ℝ≥0) / 32 = (12 : ℝ≥0) / 64) ∧
    mcaDeltaStar (F := ZMod LiteralBudgetPin.P) (A := ZMod LiteralBudgetPin.P)
          (evalCode
            (365776689002390431616511545157923604483360578 :
              ZMod LiteralBudgetPin.P)
            32 5)
          (1 / 2 ^ 128)
      ≠ mcaDeltaStar (F := ZMod Mu6DeepRung.P) (A := ZMod Mu6DeepRung.P)
          (evalCode
            (218028241209259214929338402535096146560619661187581 :
              ZMod Mu6DeepRung.P)
            64 11)
          (1 / 2 ^ 128) := by
  constructor
  · norm_num
  · rw [deltaStar_pin_literal_budget_dimSix,
      Mu6DeepRung.deltaStar_pin_mu6_dim12]
    norm_num

end ArkLib.ProximityGap.LiteralBudgetRateThreeSixteenths

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.LiteralBudgetRateThreeSixteenths.deltaStar_pin_literal_budget_dimSix
#print axioms
  ArkLib.ProximityGap.LiteralBudgetRateThreeSixteenths.literal_rate_three_sixteenths_two_scale_profile
#print axioms
  ArkLib.ProximityGap.LiteralBudgetRateThreeSixteenths.literal_rate_three_sixteenths_two_scale_drift
#print axioms
  ArkLib.ProximityGap.LiteralBudgetRateThreeSixteenths.literal_rate_only_threshold_REFUTED
