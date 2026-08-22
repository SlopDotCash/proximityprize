/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G119PrefixMajorizationSquare
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HBKCubeRootIncrementBounds
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G120HBKMajorizationProductionBudget

/-!
# Production HBK cap majorization

This file composes G119's sharp prefix-majorization theorem with the explicit coefficient-4 cap.
Any decreasing, zero-padded production fiber profile whose prefixes lie below that cap has squared
mass satisfying G120's relaxed target `3S ≤ 1072·2^40`.

The remaining HBK consumer seam is therefore only to construct the ordered fiber profile and prove
its prefix domination from G118. Issue #466.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.HBKProductionCapMajorization

open scoped BigOperators
open G119PrefixMajorizationSquare
open HBKCubeRootIncrementBounds
open G120HBKMajorizationProductionBudget

/-- Real-valued production majorization consumer. -/
theorem nine_mul_sum_sq_le_cap_budget
    (a : ℕ → ℝ) (haN : a (2 ^ 30) = 0)
    (hadrop : ∀ i < 2 ^ 30, 0 ≤ a i - a (i + 1))
    (hprefix : ∀ i < 2 ^ 30,
      (∑ j ∈ Finset.range (i + 1), a j) ≤
        ∑ j ∈ Finset.range (i + 1), productionCapIncrement j) :
    9 * (∑ i ∈ Finset.range (2 ^ 30), a i ^ 2) ≤ 3216 * 2 ^ 40 := by
  have hcapN : productionCapIncrement (2 ^ 30) = 0 := by
    simp [productionCapIncrement]
  have hcapdrop : ∀ i < 2 ^ 30,
      0 ≤ productionCapIncrement i - productionCapIncrement (i + 1) := by
    intro i _
    linarith [productionCapIncrement_antitone_succ i]
  have hmajor := sum_sq_le_sum_sq_of_prefix_le a productionCapIncrement (2 ^ 30)
    haN hcapN hadrop hcapdrop hprefix
  have hcapeq := sum_productionCapIncrement_sq_eq_of_ge
    (show 4096 ≤ 2 ^ 30 by norm_num)
  calc
    9 * (∑ i ∈ Finset.range (2 ^ 30), a i ^ 2) ≤
        9 * (∑ i ∈ Finset.range (2 ^ 30), productionCapIncrement i ^ 2) := by
      gcongr
    _ = 9 * (∑ i ∈ Finset.range 4096, productionCapIncrement i ^ 2) := by rw [hcapeq]
    _ ≤ 3216 * 2 ^ 40 := productionCapIncrement_sq_budget

/-- Natural-valued fiber-profile form, already in G120's exact target units. -/
theorem three_mul_sum_sq_le_production_target
    (a : ℕ → ℕ) (haN : a (2 ^ 30) = 0)
    (hadrop : ∀ i < 2 ^ 30, a (i + 1) ≤ a i)
    (hprefix : ∀ i < 2 ^ 30,
      ((∑ j ∈ Finset.range (i + 1), a j : ℕ) : ℝ) ≤
        ∑ j ∈ Finset.range (i + 1), productionCapIncrement j) :
    3 * (∑ i ∈ Finset.range (2 ^ 30), a i ^ 2) ≤ 1072 * 2 ^ 40 := by
  let ar : ℕ → ℝ := fun i => a i
  have harN : ar (2 ^ 30) = 0 := by
    change (a (2 ^ 30) : ℝ) = 0
    exact_mod_cast haN
  have hardrop : ∀ i < 2 ^ 30, 0 ≤ ar i - ar (i + 1) := by
    intro i hi
    dsimp [ar]
    exact sub_nonneg.mpr (by exact_mod_cast hadrop i hi)
  have harprefix : ∀ i < 2 ^ 30,
      (∑ j ∈ Finset.range (i + 1), ar j) ≤
        ∑ j ∈ Finset.range (i + 1), productionCapIncrement j := by
    intro i hi
    simpa [ar] using hprefix i hi
  have hreal := nine_mul_sum_sq_le_cap_budget ar harN hardrop harprefix
  have hnat :
      9 * (∑ i ∈ Finset.range (2 ^ 30), a i ^ 2) ≤ 3216 * 2 ^ 40 := by
    simp only [ar, ← Nat.cast_pow, ← Nat.cast_sum] at hreal
    exact_mod_cast hreal
  omega

/-- **End-to-end production energy consumer.** Once the ordered nonzero-coset profile has the
explicit cap prefixes and HBK equation (9) identifies energy with `h²+h·Σaᵢ²`, the exact G97
coefficient follows. -/
theorem production_energy_sq_le_of_profile
    (a : ℕ → ℕ) (E : ℕ) (haN : a (2 ^ 30) = 0)
    (hadrop : ∀ i < 2 ^ 30, a (i + 1) ≤ a i)
    (hprefix : ∀ i < 2 ^ 30,
      ((∑ j ∈ Finset.range (i + 1), a j : ℕ) : ℝ) ≤
        ∑ j ∈ Finset.range (i + 1), productionCapIncrement j)
    (henergy : E = (2 ^ 30) ^ 2 + (2 ^ 30) *
      (∑ i ∈ Finset.range (2 ^ 30), a i ^ 2)) :
    E ^ 2 ≤ 128 * (2 ^ 30) ^ 5 := by
  have htarget := three_mul_sum_sq_le_production_target a haN hadrop hprefix
  rw [henergy]
  exact production_energy_sq_le_of_three_mul_nonzero_sq_mass_le htarget

end ArkLib.ProximityGap.Frontier.HBKProductionCapMajorization

#print axioms
  ArkLib.ProximityGap.Frontier.HBKProductionCapMajorization.nine_mul_sum_sq_le_cap_budget
#print axioms
  ArkLib.ProximityGap.Frontier.HBKProductionCapMajorization.three_mul_sum_sq_le_production_target
#print axioms
  ArkLib.ProximityGap.Frontier.HBKProductionCapMajorization.production_energy_sq_le_of_profile
