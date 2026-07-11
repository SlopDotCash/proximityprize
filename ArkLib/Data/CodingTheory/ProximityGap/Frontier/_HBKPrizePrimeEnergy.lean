/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HBKSpecialAuxiliaryAssembly
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._PrizeShapePrimeP30
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._PrizeShapePrimeP30Second

/-!
# Effective HBK energy at both certified prize primes

The generic special-auxiliary assembly only needs prime characteristic at least `2^52`, a
primitive `2^30`-th root, and enough field elements for at least `2^30` multiplicative cosets.
Both certified prize-shaped prime fields satisfy these hypotheses by literal arithmetic.

This file records the two concrete additive-energy endpoints. Issue #466.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.Frontier.HBKPrizePrimeEnergy

open Polynomial
open ArkLib.ProximityGap.AdditiveEnergyRepBound
open HBKSpecialAuxiliaryAssembly

namespace First

open ArkLib.ProximityGap.PrizeShapePrimeP30

local instance fact_prime : Fact (Nat.Prime P) := ⟨prime_P⟩

/-- The first certified prize prime satisfies the effective HBK squared-energy ceiling. -/
theorem energy_sq_le :
    additiveEnergy (nthRootsFinset (2 ^ 30) (1 : ZMod P)) ^ 2 ≤
      128 * (2 ^ 30) ^ 5 := by
  have hprim : IsPrimitiveRoot g (2 ^ 30) := by
    have hg := IsPrimitiveRoot.orderOf g
    rw [orderOf_g] at hg
    exact hg
  apply production_energy_sq_le_of_card prime_P (F := ZMod P)
  · norm_num [P]
  · exact hprim
  · rw [ZMod.card]
    norm_num [P]

end First

namespace Second

open ArkLib.ProximityGap.PrizeShapePrimeP30Second

local instance fact_prime : Fact (Nat.Prime P) := ⟨prime_P⟩

/-- The second certified prize prime satisfies the same effective HBK squared-energy ceiling. -/
theorem energy_sq_le :
    additiveEnergy (nthRootsFinset (2 ^ 30) (1 : ZMod P)) ^ 2 ≤
      128 * (2 ^ 30) ^ 5 := by
  have hprim : IsPrimitiveRoot g (2 ^ 30) := by
    have hg := IsPrimitiveRoot.orderOf g
    rw [orderOf_g] at hg
    exact hg
  apply production_energy_sq_le_of_card prime_P (F := ZMod P)
  · norm_num [P]
  · exact hprim
  · rw [ZMod.card]
    norm_num [P]

end Second

end ArkLib.ProximityGap.Frontier.HBKPrizePrimeEnergy

#print axioms ArkLib.ProximityGap.Frontier.HBKPrizePrimeEnergy.First.energy_sq_le
#print axioms ArkLib.ProximityGap.Frontier.HBKPrizePrimeEnergy.Second.energy_sq_le
