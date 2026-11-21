/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BadFamilyCensus
import ArkLib.Research.ProximityGap.Support.BinaryPower
import Mathlib.NumberTheory.LucasPrimality

/-! # Production field and failure at one quarter for the apolar predecessor bound

The Lucas certificate, subgroup order, rounded budget and bad endpoint use
the repository's existing finite-field and two-line constructions.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
open ProximityGap ArkLib.ProximityGap.KKH26
open ArkLib.ProximityGap.BinaryPower (binaryPow_eq_pow)
open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.Frontier.RateHalfApolarBudget

/-- The production-length field with exactly \(2^{28}+3\) allowed bad scalars. -/
abbrev P : ℕ := 91343853369979269099964682909737195747164553217

theorem prime_P : Nat.Prime P := by
  have hmain : (3 : ZMod P) ^ (P - 1) = 1 := by rw [← binaryPow_eq_pow]; decide
  refine lucas_primality P 3 hmain ?_
  intro v hv hd
  rw [show P - 1 = 2^122 * (79 * (223 * 975187)) by decide] at hd
  rcases hv.dvd_mul.mp hd with htwo | hodd
  · have heq := (Nat.prime_dvd_prime_iff_eq hv Nat.prime_two).mp (hv.dvd_of_dvd_pow htwo)
    subst v
    rw [← binaryPow_eq_pow]
    decide
  · simp only [hv.dvd_mul, Nat.prime_dvd_prime_iff_eq hv (by decide : Nat.Prime 79),
      Nat.prime_dvd_prime_iff_eq hv (by decide : Nat.Prime 223),
      Nat.prime_dvd_prime_iff_eq hv (by norm_num : Nat.Prime 975187)] at hodd
    rcases hodd with rfl | rfl | rfl <;> rw [← binaryPow_eq_pow] <;> decide

instance : Fact (Nat.Prime P) := ⟨prime_P⟩

abbrev generator : ZMod P := 39947002152884693406992285236833299620967665422

theorem generator_order : orderOf generator = 1073741824 := by
  apply orderOf_eq_prime_pow (p := 2) (n := 29)
  · rw [← binaryPow_eq_pow]; decide
  · rw [← binaryPow_eq_pow]; decide

theorem budget : P / 2^128 = 268435459 := by decide

/-- The two-line witness supplies over half a billion bad scalars over every eligible field. -/
theorem bad_scalar_mass_of_order {p : ℕ} [Fact (Nat.Prime p)] {g : ZMod p}
    (hg : orderOf g = 1073741824) :
    (536870914 : ℝ≥0∞) / (p : ℝ≥0∞) ≤
      epsMCA (F := ZMod p) (evalCode g 1073741824 536870911) (1 / 4) := by
  have h := BadFamilyCensus.bisimplex_epsMCA_lower_bound (d := 536870911)
    (e := 268435456) hg (by decide) (by decide) (by decide) (by decide)
  have ht : (1 : ℝ≥0) - (805306368 : ℝ≥0) / 1073741824 = 1 / 4 := tsub_eq_of_eq_add (by norm_num)
  change (536870914 : ℝ≥0∞) / (p : ℝ≥0∞) ≤ epsMCA (F := ZMod p)
    (evalCode g 1073741824 536870911) (1 - (805306368 : ℝ≥0) / 1073741824) at h
  rwa [ht] at h

/-- The two-line witness supplies over half a billion bad scalars. -/
theorem bad_scalar_mass :
    (536870914 : ℝ≥0∞) / (P : ℝ≥0∞) ≤
      epsMCA (F := ZMod P) (evalCode generator 1073741824 536870911) (1 / 4) :=
  bad_scalar_mass_of_order generator_order

namespace Boundary

/-- The explicit field at the sharpest proved budget endpoint. -/

abbrev P : ℕ := 91343853062927602073649116268957764822404956161

private theorem prime_factor : Nat.Prime 13743895457 := by
  let v := 13743895457
  have hp : (3 : ZMod v) ^ (v - 1) = 1 := by rw [← binaryPow_eq_pow]; decide
  apply lucas_primality v 3 hp
  intro q hq hd
  rw [show v - 1 = 2^5 * (23 * (67 * (109 * 2557))) by decide] at hd
  rcases hq.dvd_mul.mp hd with htwo | hodd
  · have heq := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow htwo)
    subst q
    rw [← binaryPow_eq_pow]
    decide
  · simp only [hq.dvd_mul, Nat.prime_dvd_prime_iff_eq hq (by decide : Nat.Prime 23),
      Nat.prime_dvd_prime_iff_eq hq (by decide : Nat.Prime 67),
      Nat.prime_dvd_prime_iff_eq hq (by decide : Nat.Prime 109),
      Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2557)] at hodd
    rcases hodd with rfl | rfl | rfl | rfl <;> rw [← binaryPow_eq_pow] <;> decide

theorem prime_P : Nat.Prime P := by
  have hp : (3 : ZMod P) ^ (P - 1) = 1 := by rw [← binaryPow_eq_pow]; decide
  apply lucas_primality P 3 hp
  intro q hq hd
  rw [show P - 1 = 2^120 * (5 * 13743895457) by decide] at hd
  rcases hq.dvd_mul.mp hd with htwo | hodd
  · have heq := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow htwo)
    subst q
    rw [← binaryPow_eq_pow]
    decide
  · simp only [hq.dvd_mul, Nat.prime_dvd_prime_iff_eq hq (by decide : Nat.Prime 5),
      Nat.prime_dvd_prime_iff_eq hq prime_factor] at hodd
    rcases hodd with rfl | rfl <;> rw [← binaryPow_eq_pow] <;> decide

instance : Fact (Nat.Prime P) := ⟨prime_P⟩

abbrev generator : ZMod P := 15880532512442061028676049873222051690399817336

theorem generator_order : orderOf generator = 1073741824 := by
  apply orderOf_eq_prime_pow (p := 2) (n := 29)
  · rw [← binaryPow_eq_pow]; decide
  · rw [← binaryPow_eq_pow]; decide

theorem budget : P / 2^128 = 268435458 := by decide

/-- The two-line witness supplies over half a billion bad scalars. -/
theorem bad_scalar_mass :
    (536870914 : ℝ≥0∞) / (P : ℝ≥0∞) ≤
      epsMCA (F := ZMod P) (evalCode generator 1073741824 536870911) (1 / 4) :=
  bad_scalar_mass_of_order generator_order

end Boundary

end ArkLib.ProximityGap.Frontier.RateHalfApolarBudget

#print axioms ArkLib.ProximityGap.Frontier.RateHalfApolarBudget.prime_P
#print axioms ArkLib.ProximityGap.Frontier.RateHalfApolarBudget.generator_order
#print axioms ArkLib.ProximityGap.Frontier.RateHalfApolarBudget.budget
#print axioms ArkLib.ProximityGap.Frontier.RateHalfApolarBudget.bad_scalar_mass

#print axioms ArkLib.ProximityGap.Frontier.RateHalfApolarBudget.Boundary.prime_P
#print axioms ArkLib.ProximityGap.Frontier.RateHalfApolarBudget.Boundary.generator_order
#print axioms ArkLib.ProximityGap.Frontier.RateHalfApolarBudget.Boundary.budget
#print axioms ArkLib.ProximityGap.Frontier.RateHalfApolarBudget.Boundary.bad_scalar_mass
