/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BadFamilyCensus
import ArkLib.Research.ProximityGap.Support.BinaryPower
import Mathlib.NumberTheory.LucasPrimality

/-! # A rate-quarter field at the unique-decoding budget

The generator has order \(2^{30}\), and two disjoint exceptional sets exceed
the \(2^{-128}\) budget at exactly \(3/8\) of the block length.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
open ProximityGap ArkLib.ProximityGap.KKH26
open ArkLib.ProximityGap.BinaryPower (binaryPow_eq_pow)
open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.Frontier.RateQuarterApolarBudget

abbrev P : ℕ := 137015778580855056324475321314283763769844695041

theorem prime_P : Nat.Prime P := by
  have hp : (3 : ZMod P) ^ (P - 1) = 1 := by rw [← binaryPow_eq_pow]; decide
  apply lucas_primality P 3 hp
  intro q hq hd
  rw [show P - 1 = 2^120 * (5 * (17 * (17 * (83 * 859459)))) by decide] at hd
  rcases hq.dvd_mul.mp hd with htwo | hodd
  · have heq := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow htwo)
    subst q
    rw [← binaryPow_eq_pow]
    decide
  · simp only [hq.dvd_mul, Nat.prime_dvd_prime_iff_eq hq (by decide : Nat.Prime 5),
      Nat.prime_dvd_prime_iff_eq hq (by decide : Nat.Prime 17),
      Nat.prime_dvd_prime_iff_eq hq (by decide : Nat.Prime 83),
      Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 859459)] at hodd
    rcases hodd with rfl | rfl | rfl | rfl | rfl <;> rw [← binaryPow_eq_pow] <;> decide

instance : Fact (Nat.Prime P) := ⟨prime_P⟩

abbrev generator : ZMod P := 92365554320529815296747239188837152885411596825

theorem generator_order : orderOf generator = 1073741824 := by
  apply orderOf_eq_prime_pow (p := 2) (n := 29)
  · rw [← binaryPow_eq_pow]; decide
  · rw [← binaryPow_eq_pow]; decide

theorem budget : P / 2^128 = 402653184 := by decide

/-- The rate-quarter construction works on every order-\(2^{30}\) subgroup. -/
theorem bad_scalar_mass_of_order {p : ℕ} [Fact (Nat.Prime p)] {g : ZMod p}
    (hg : orderOf g = 1073741824) :
    (805306370 : ℝ≥0∞) / (p : ℝ≥0∞) ≤
      epsMCA (F := ZMod p) (evalCode g 1073741824 268435455) (3 / 8) := by
  have h := BadFamilyCensus.bisimplex_epsMCA_lower_bound (d := 268435455)
    (e := 402653184) hg (by decide) (by decide) (by decide) (by decide)
  have ht : (1 : ℝ≥0) - (671088640 : ℝ≥0) / 1073741824 = 3 / 8 :=
    tsub_eq_of_eq_add (by norm_num)
  change (805306370 : ℝ≥0∞) / (p : ℝ≥0∞) ≤ epsMCA (F := ZMod p)
    (evalCode g 1073741824 268435455) (1 - (671088640 : ℝ≥0) / 1073741824) at h
  rwa [ht] at h

/-- The actual field and subgroup attain the same lower bound. -/
theorem bad_scalar_mass :
    (805306370 : ℝ≥0∞) / (P : ℝ≥0∞) ≤
      epsMCA (F := ZMod P) (evalCode generator 1073741824 268435455) (3 / 8) :=
  bad_scalar_mass_of_order generator_order

end ArkLib.ProximityGap.Frontier.RateQuarterApolarBudget

#print axioms ArkLib.ProximityGap.Frontier.RateQuarterApolarBudget.prime_P
#print axioms ArkLib.ProximityGap.Frontier.RateQuarterApolarBudget.generator_order
#print axioms ArkLib.ProximityGap.Frontier.RateQuarterApolarBudget.budget
#print axioms ArkLib.ProximityGap.Frontier.RateQuarterApolarBudget.bad_scalar_mass
