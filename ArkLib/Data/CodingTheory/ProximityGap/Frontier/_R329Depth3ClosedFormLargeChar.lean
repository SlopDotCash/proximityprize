/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FS5TrivialCountClosedForm
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R327Depth3ExcessVanishing

/-!
# R329: explicit depth-3 energy in the large-characteristic regime

FS5 identifies the characteristic-zero contribution exactly, while R327
eliminates every nonzero pattern above the explicit resultant height.  Their
composition gives the closed polynomial value of the depth-3 energy.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.R329Depth3ClosedFormLargeChar

open ArkLib.ProximityGap.Frontier.FS5TrivialCountClosedForm
open ArkLib.ProximityGap.Frontier.R327Depth3ExcessVanishing
open ArkLib.ProximityGap.SubgroupGaussSumSixthMoment

theorem addEnergy3_eq_closedForm_of_characteristic_above_height
    {k prime : ℕ} {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {ζ : F} (hm : 0 < 2 ^ k) (hprim : IsPrimitiveRoot ζ (2 * 2 ^ k))
    (hhalfTurn : ζ ^ (2 ^ k) = -1)
    (hprime : 2 ^ ((k + 1 + 3) * 2 ^ (k + 1)) < prime)
    [CharP F prime] :
    (addEnergy3 (Gset ζ (2 ^ k)) : ℤ) =
      15 * ((2 * 2 ^ k : ℕ) : ℤ) ^ 3 -
        45 * ((2 * 2 ^ k : ℕ) : ℤ) ^ 2 +
        40 * ((2 * 2 ^ k : ℕ) : ℤ) := by
  rw [addEnergy3_eq_closedForm_add_excess hm hprim]
  rw [wraparoundExcess_eq_zero_of_characteristic_above_height
    (k := k) (prime := prime) (ζ := ζ) hhalfTurn hprime]
  simp

end ArkLib.ProximityGap.Frontier.R329Depth3ClosedFormLargeChar

#print axioms ArkLib.ProximityGap.Frontier.R329Depth3ClosedFormLargeChar.addEnergy3_eq_closedForm_of_characteristic_above_height
