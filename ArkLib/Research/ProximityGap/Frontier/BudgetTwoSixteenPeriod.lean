/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.QuarterBudgetTwoThreshold
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSecondMoment
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# A nearly maximal additive period at order sixteen on the budget-two field

At the explicit nonzero frequency below, the real part of the sum of the sixteen
additive character values exceeds `16 − 10⁻⁸`. A list of short signed representatives
certifies the bound by the elementary inequality `cos x ≥ 1 − x²/2`.
-/

namespace ProximityGap.BudgetTwoSixteenPeriod

open Finset ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open QuarterBudgetTwoThreshold (p)

/-- The order-sixteen root obtained from the budget-two domain generator. -/
abbrev root : ZMod p := 236023637409912314118267886612795304038

/-- The period root is the designated generator to the index-`2^26` power. -/
theorem root_eq_generator_pow :
    root = (QuarterBudgetTwoThreshold.generator : ZMod p) ^ (2 ^ 26 : ℕ) := by
  rw [← ArkLib.ProximityGap.BinaryPower.binaryPow_eq_pow]
  decide

/-- The designated connection set has sixteen distinct powers. -/
theorem root_order : orderOf root = 16 := by
  have hhalf : root ^ (2 ^ 3 : ℕ) ≠ 1 := by decide
  have hfull : root ^ (2 ^ 4 : ℕ) = 1 := by decide
  exact orderOf_eq_prime_pow (x := root) hhalf hfull

/-- An explicit frequency with nearly maximal positive period. -/
abbrev frequency : ZMod p := 1307463472926189116010105893757615

private def halfLifts : Fin 8 → ℤ :=
  ![1307463472926189116010105893757615, 1217213402380520060931723266171796,
    -4623970535421946185229367553984506, -4540030564452956472041107461504927,
    -1840291758657348960221460084463293, 4196607567946251668078509417313931,
    -3798276392765071985090165618619890, -5364116073431666686754060219048751]

private def lift (i : Fin 16) : ℤ :=
  if hi : i.val < 8 then halfLifts ⟨i.val, hi⟩ else -halfLifts ⟨i.val - 8, by omega⟩

private abbrev totalSq : ℕ :=
  218765767759997288981939408699527325026704798281539339161408758083834

private theorem valid_lifts : ∀ i : Fin 16, ((lift i : ℤ) : ZMod p) = frequency * root ^ i.val := by
  decide

private theorem lift_energy : ∑ i : Fin 16, (lift i) ^ 2 = totalSq := by decide

private theorem phase_lower (z : ℤ) :
    1 - 20 * ((z : ℝ) ^ 2 / (p : ℝ) ^ 2) ≤ (ZMod.stdAddChar (z : ZMod p)).re := by
  rw [ZMod.stdAddChar_coe]
  have heq : (2 * Real.pi * Complex.I * z / p : ℂ) =
      ((2 * Real.pi * z / p : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [heq, Complex.exp_ofReal_mul_I_re]
  have hpi : 2 * Real.pi ^ 2 ≤ 20 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hs : 0 ≤ (z : ℝ) ^ 2 / (p : ℝ) ^ 2 := by positivity
  calc
    _ ≤ 1 - (2 * Real.pi ^ 2) * ((z : ℝ) ^ 2 / (p : ℝ) ^ 2) := by gcongr
    _ = 1 - (2 * Real.pi * z / p) ^ 2 / 2 := by ring
    _ ≤ _ := Real.one_sub_sq_div_two_le_cos

/-- The witness is a nonprincipal frequency. -/
theorem frequency_ne_zero : frequency ≠ 0 := by decide

/-- The positive real part of the actual order-sixteen additive period is within
`10⁻⁸` of the degree for the budget-two field. -/
theorem real_period_gt (D : Fin 16 ↪ ZMod p) (hD : ∀ i, D i = root ^ i.val) :
    (16 - 1 / 100000000 : ℝ) < (eta ZMod.stdAddChar (Finset.univ.map D) frequency).re := by
  have hsum : ∑ i : Fin 16, (lift i : ℝ) ^ 2 = (totalSq : ℝ) := by exact_mod_cast lift_energy
  calc
    _ < 16 - 20 * (totalSq / (p : ℝ) ^ 2) := by norm_num [totalSq, p]
    _ = ∑ i : Fin 16, (1 - 20 * ((lift i : ℝ) ^ 2 / (p : ℝ) ^ 2)) := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_div, hsum]
      simp
    _ ≤ ∑ i : Fin 16, (ZMod.stdAddChar (frequency * D i)).re := by
      apply Finset.sum_le_sum
      intro i _
      rw [hD, ← valid_lifts i]
      exact phase_lower _
    _ = _ := by simp [eta, Complex.re_sum]

end ProximityGap.BudgetTwoSixteenPeriod

#print axioms ProximityGap.BudgetTwoSixteenPeriod.frequency_ne_zero
#print axioms ProximityGap.BudgetTwoSixteenPeriod.real_period_gt

#print axioms ProximityGap.BudgetTwoSixteenPeriod.root_eq_generator_pow
#print axioms ProximityGap.BudgetTwoSixteenPeriod.root_order
