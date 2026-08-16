/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R327Depth3ExcessVanishing

/-!
# R328: exact depth-3 energy identity above the annihilator height

The FS4 decomposition and R327's arbitrary-pattern excess vanishing give a
field-independent depth-3 energy value in the large-characteristic regime.
-/

set_option autoImplicit false

open Finset

namespace ArkLib.ProximityGap.Frontier.R328Depth3EnergyCharIndependent

open ArkLib.ProximityGap.Frontier.FS4Depth3PatternDecomposition
open ArkLib.ProximityGap.Frontier.R327Depth3ExcessVanishing
open ArkLib.ProximityGap.SubgroupGaussSumSixthMoment

theorem addEnergy3_eq_trivialCount_of_characteristic_above_height
    {k prime : ℕ} {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {ζ : F} (hm : 0 < 2 ^ k) (hprim : IsPrimitiveRoot ζ (2 * 2 ^ k))
    (hhalfTurn : ζ ^ (2 ^ k) = -1)
    (hprime : 2 ^ ((k + 1 + 3) * 2 ^ (k + 1)) < prime)
    [CharP F prime] :
    addEnergy3 ((range (2 * 2 ^ k)).image (ζ ^ ·)) = trivialCount (2 ^ k) := by
  rw [addEnergy3_eq_trivial_add_excess hm hprim]
  rw [wraparoundExcess_eq_zero_of_characteristic_above_height
    (k := k) (prime := prime) (ζ := ζ) hhalfTurn hprime]
  simp

end ArkLib.ProximityGap.Frontier.R328Depth3EnergyCharIndependent

#print axioms ArkLib.ProximityGap.Frontier.R328Depth3EnergyCharIndependent.addEnergy3_eq_trivialCount_of_characteristic_above_height
