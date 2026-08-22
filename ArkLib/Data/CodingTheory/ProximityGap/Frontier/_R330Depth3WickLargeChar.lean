/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FS5TrivialCountClosedForm
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R327Depth3ExcessVanishing

/-!
# R330: large-characteristic depth-3 Wick bound

The exact closed-form depth-3 energy from R329 is below the Gaussian Wick
target, so the FS5 headroom consumer yields `GaussianEnergyBound` outright.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.R330Depth3WickLargeChar

open ArkLib.ProximityGap.Frontier.FS5TrivialCountClosedForm
open ArkLib.ProximityGap.Frontier.R327Depth3ExcessVanishing
open ArkLib.ProximityGap.GaussPeriodMomentBound

theorem gaussianEnergyBound_three_of_characteristic_above_height
    {k prime : ℕ} {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {ζ : F} {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (hm : 0 < 2 ^ k) (hprim : IsPrimitiveRoot ζ (2 * 2 ^ k))
    (hhalfTurn : ζ ^ (2 ^ k) = -1)
    (hprime : 2 ^ ((k + 1 + 3) * 2 ^ (k + 1)) < prime)
    [CharP F prime] :
    GaussianEnergyBound (Gset ζ (2 ^ k)) 3 := by
  apply gaussianEnergyBound_three_of_wraparound_headroom hψ hm hprim
  rw [wraparoundExcess_eq_zero_of_characteristic_above_height
    (k := k) (prime := prime) (ζ := ζ) hhalfTurn hprime]
  have hcard : ((Gset ζ (2 ^ k)).card : ℝ) = (2 * (2 ^ k : ℕ) : ℝ) := by
    exact_mod_cast Gset_card hm hprim
  rw [hcard]
  have hx : 0 ≤ (2 * (((2 ^ k : ℕ) : ℝ))) := by positivity
  have hx2 : 2 ≤ (2 * (((2 ^ k : ℕ) : ℝ))) := by
    have hk : (1 : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by
      exact_mod_cast (Nat.one_le_two_pow : 1 ≤ 2 ^ k)
    calc
      (2 : ℝ) = 2 * 1 := by ring
      _ ≤ 2 * ((2 ^ k : ℕ) : ℝ) := mul_le_mul_of_nonneg_left hk (by norm_num)
  have hlin : 0 ≤ 45 * (2 * (((2 ^ k : ℕ) : ℝ))) - 40 := by
    rw [sub_nonneg]
    calc
      (40 : ℝ) ≤ 45 * 2 := by norm_num
      _ ≤ 45 * (2 * (((2 ^ k : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left hx2 (by norm_num)
  calc
    ((0 : ℤ) : ℝ) ≤ (2 * (((2 ^ k : ℕ) : ℝ))) *
        (45 * (2 * (((2 ^ k : ℕ) : ℝ))) - 40) :=
      by simpa only [Int.cast_zero] using mul_nonneg hx hlin
    _ = 45 * (2 * (((2 ^ k : ℕ) : ℝ))) ^ 2 -
        40 * (2 * (((2 ^ k : ℕ) : ℝ))) := by ring

end ArkLib.ProximityGap.Frontier.R330Depth3WickLargeChar

#print axioms
  ArkLib.ProximityGap.Frontier.R330Depth3WickLargeChar.gaussianEnergyBound_three_of_characteristic_above_height
