/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.SidonDepthFourNonSharp

/-!
# The two-point Sidon non-sharp witness at depth five (#444)

`SidonDepthThreeNonSharp` and `SidonDepthFourNonSharp` pin exact finite witnesses showing that
swap-floor sharpness for Sidon sets is a depth-`2` phenomenon, not a general higher-energy law.
This file extends that concrete boundary sequence one further rung.

For the same Sidon set `G = {0,1} ⊂ ZMod 5`, `rEnergy G 5 = 254`.  The extra `+2` beyond the
central binomial count `C(10,5)=252` is the first wraparound contribution modulo `5`: all-zero
versus all-one five-tuples have sums congruent modulo `5`.  The naive swap floor
`2*|G|^5 - |G|^2` is only `60`.

This is deliberately a small exact Sidon/incidence brick: no CORE upper bound, no char-`p`
transfer, no capacity or growth-law claim.
-/

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumMoment (rEnergy)

namespace ArkLib.ProximityGap.Frontier.SidonDepthFiveNonSharp

open ArkLib.ProximityGap.Frontier.SidonDepthThreeNonSharp

local instance localInstance_SidonDepthFiveNonSharp_1 : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- The depth-five relation energy of `{0,1} ⊂ ZMod 5` is `254`. -/
theorem rEnergy_five_twoPoint : rEnergy twoPoint 5 = 254 := by decide

/-- At depth five, the universal swap floor for the two-point Sidon set is only `60`. -/
theorem swap_floor_five_twoPoint : 2 * twoPoint.card ^ 5 - twoPoint.card ^ 2 = 60 := by decide

/-- **Sidon swap-floor sharpness still fails at depth five.**
The Sidon set `{0,1} ⊂ ZMod 5` has `rEnergy = 254`, strictly above the swap floor `60`. -/
theorem sidon_depth_five_not_swap_sharp :
    2 * twoPoint.card ^ 5 - twoPoint.card ^ 2 < rEnergy twoPoint 5 := by
  rw [swap_floor_five_twoPoint, rEnergy_five_twoPoint]
  norm_num

end ArkLib.ProximityGap.Frontier.SidonDepthFiveNonSharp

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.SidonDepthFiveNonSharp.rEnergy_five_twoPoint
#print axioms ArkLib.ProximityGap.Frontier.SidonDepthFiveNonSharp.sidon_depth_five_not_swap_sharp
