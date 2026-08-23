/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26DeltaStarPinAllWitness

/-!
# A second concrete unconditional δ* pin: `δ* = 5/8` at `r = 3` (#389)

`KKH26DeltaStarPinAllWitness.deltaStar_pin_concrete_F4129` pins `δ* = 3/4` (the `r = 2` rung) for
the explicit smooth RS code over `ZMod 4129` at the order-8 element `g = 777`.  This file pins the
**next rung** of the same code — `r = 3` — giving a *different* unconditional δ* value:

> **`deltaStar_pin_concrete_F4129_r3`** — `δ* = 5/8 = 1 − 3/2³` for the order-8 element `g = 777`
> over `ZMod 4129`, at `ε* = 18/4129`, with **zero hypotheses** (no `CensusDomination`).

It is the same `kkh26_deltaStar_pin_allWitness` engine with `r = 3` (still in the bulk range
`r ≤ 2^{μ-1} = 4`): the all-witness budget is `C(8,3)/C(3,2) = 56/3 = 18`, strictly below the
KKH26 supply `2³·C(4,3) = 32`, so the `ε*`-interval `[18/4129, 32/4129)` is non-empty and the
threshold is pinned.  Together with the `r = 2` pin (`δ* = 3/4`) this exhibits two distinct
unconditional δ* rungs of one explicit code, confirming the `1 − r/2^μ` rung law concretely.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`/`native_decide`.
-/

open Finset Polynomial
open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap ProximityGap.MCAThresholdLedger ArkLib.ProximityGap.KKH26
open ProximityGap.KKH26DeltaStarReduction ProximityGap.SpikeFloor

namespace ProximityGap.Ownership.KKH26AllWitnessPin

/-- **A second concrete δ* pin (the `r = 3` rung): `δ* = 5/8` over `ZMod 4129`.**  Same explicit
order-8 code as `deltaStar_pin_concrete_F4129`, next rung; fully discharged, zero hypotheses. -/
theorem deltaStar_pin_concrete_F4129_r3 :
    mcaDeltaStar (F := ZMod 4129) (A := ZMod 4129)
        (evalCode (777 : ZMod 4129) 8 ((3 - 2) * 1)) ((18 : ℝ≥0∞) / 4129)
      = 1 - ((3 : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ 3) := by
  haveI : NeZero (8 : ℕ) := ⟨by norm_num⟩
  have hg : orderOf (777 : ZMod 4129) = 2 ^ 3 * 1 := by
    have h8 : (777 : ZMod 4129) ^ (2 ^ 3) = 1 := by decide
    have h4 : ¬ (777 : ZMod 4129) ^ (2 ^ 2) = 1 := by decide
    simpa using orderOf_eq_prime_pow (p := 2) (n := 2) h4 h8
  have hb1 : (Nat.choose 8 ((3 - 2) * 1 + 2) / Nat.choose (3 * 1) ((3 - 2) * 1 + 1) : ℕ) = 18 := by
    decide
  have hb2 : (2 ^ 3 * Nat.choose (2 ^ (3 - 1)) 3 : ℕ) = 32 := by decide
  exact kkh26_deltaStar_pin_allWitness (p := 4129) (n := 8) (μ := 3) (m := 1) (r := 3)
    (g := 777) (by norm_num) (le_refl 1) (by norm_num) hg (by norm_num) (by norm_num) (by norm_num)
    ((18 : ℝ≥0∞) / 4129)
    (by rw [hb1]; norm_num)
    (by
      rw [hb2, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
      exact ENNReal.mul_lt_mul_right (ENNReal.inv_ne_zero.mpr ENNReal.ofNat_ne_top)
        (ENNReal.inv_ne_top.mpr (by norm_num)) (by norm_num))

#print axioms ProximityGap.Ownership.KKH26AllWitnessPin.deltaStar_pin_concrete_F4129_r3

end ProximityGap.Ownership.KKH26AllWitnessPin
