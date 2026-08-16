/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# G120: exact production budget for the HBK majorization lane

HBK equation (9) is `E = h^2 + h*S`, where `S` is the squared mass of the nonzero coset
representatives.  At `h=2^30`, the sharp coefficient-4 cap calculation is targeted at

`9*S ≤ 3088 * 2^40`.

This file verifies that this concrete integer target is sufficient for G97's required
`E^2 ≤ 128*h^5`.  The constant corresponds to an effective normalized coefficient
`3088/(9*32) = 10 + 13/18`, safely below `sqrt(128)` even after retaining the exact diagonal
term `h^2`.  Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G120HBKMajorizationProductionBudget

/-- Exact arithmetic consumer for the remaining nonzero-fiber squared-mass target. -/
theorem production_energy_sq_le_of_nine_mul_nonzero_sq_mass_le
    {S : ℕ} (hS : 9 * S ≤ 3088 * 2 ^ 40) :
    (((2 ^ 30) ^ 2 + (2 ^ 30) * S) ^ 2 : ℕ) ≤
      128 * (2 ^ 30) ^ 5 := by
  let E := (2 ^ 30) ^ 2 + (2 ^ 30) * S
  let M := 9 * (2 ^ 30) ^ 2 + (2 ^ 30) * (3088 * 2 ^ 40)
  have hscaled : 9 * E ≤ M := by
    dsimp [E, M]
    nlinarith
  have hsq : (9 * E) ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left hscaled 2
  have hnumeric : M ^ 2 ≤ 81 * (128 * (2 ^ 30) ^ 5) := by
    norm_num [M]
  have h81 : 81 * E ^ 2 ≤ 81 * (128 * (2 ^ 30) ^ 5) := by
    calc
      81 * E ^ 2 = (9 * E) ^ 2 := by ring
      _ ≤ M ^ 2 := hsq
      _ ≤ 81 * (128 * (2 ^ 30) ^ 5) := hnumeric
  exact Nat.le_of_mul_le_mul_left h81 (by norm_num)

/-- The target coefficient has explicit slack below `128`: its restored energy envelope squares
strictly below the production budget. -/
theorem production_majorization_envelope_strict_slack :
    (9 * (2 ^ 30) ^ 2 + (2 ^ 30) * (3088 * 2 ^ 40)) ^ 2 <
      81 * (128 * (2 ^ 30) ^ 5) := by
  norm_num

/-- Relaxed target matched by the elementary cube-root telescoping proof.  Its normalized
coefficient is `1072/(3*32) = 11 + 1/6`, which still leaves production slack. -/
theorem production_energy_sq_le_of_three_mul_nonzero_sq_mass_le
    {S : ℕ} (hS : 3 * S ≤ 1072 * 2 ^ 40) :
    (((2 ^ 30) ^ 2 + (2 ^ 30) * S) ^ 2 : ℕ) ≤
      128 * (2 ^ 30) ^ 5 := by
  let E := (2 ^ 30) ^ 2 + (2 ^ 30) * S
  let M := 3 * (2 ^ 30) ^ 2 + (2 ^ 30) * (1072 * 2 ^ 40)
  have hscaled : 3 * E ≤ M := by
    dsimp [E, M]
    nlinarith
  have hsq : (3 * E) ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left hscaled 2
  have hnumeric : M ^ 2 ≤ 9 * (128 * (2 ^ 30) ^ 5) := by
    norm_num [M]
  have h9 : 9 * E ^ 2 ≤ 9 * (128 * (2 ^ 30) ^ 5) := by
    calc
      9 * E ^ 2 = (3 * E) ^ 2 := by ring
      _ ≤ M ^ 2 := hsq
      _ ≤ 9 * (128 * (2 ^ 30) ^ 5) := hnumeric
  exact Nat.le_of_mul_le_mul_left h9 (by norm_num)

end ArkLib.ProximityGap.Frontier.G120HBKMajorizationProductionBudget

#print axioms
  ArkLib.ProximityGap.Frontier.G120HBKMajorizationProductionBudget.production_energy_sq_le_of_nine_mul_nonzero_sq_mass_le
#print axioms
  ArkLib.ProximityGap.Frontier.G120HBKMajorizationProductionBudget.production_majorization_envelope_strict_slack
#print axioms
  ArkLib.ProximityGap.Frontier.G120HBKMajorizationProductionBudget.production_energy_sq_le_of_three_mul_nonzero_sq_mass_le
