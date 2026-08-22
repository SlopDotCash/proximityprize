/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.SidonDepthThreeNonSharp

/-!
# The two-point Sidon non-sharp witness one rung higher (#444)

`SidonDepthThreeNonSharp` pins the first failure of swap-floor sharpness for a Sidon set:
`G = {0,1} ⊂ ZMod 5` has depth-three relation energy strictly above the universal swap floor.
This file extends that concrete Sidon boundary witness one rung higher, at depth four.

For the same Sidon set, `rEnergy G 4 = 70 = C(8,4)`, while the naive swap floor
`2*|G|^4 - |G|^2` is only `28`. This is deliberately a small exact Sidon/incidence brick:
no CORE upper bound, no char-`p` transfer, no capacity or growth-law claim.
-/

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumMoment (rEnergy)

namespace ArkLib.ProximityGap.Frontier.SidonDepthFourNonSharp

open ArkLib.ProximityGap.Frontier.SidonDepthThreeNonSharp

local instance localInstance_SidonDepthFourNonSharp_1 : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- The depth-four relation energy of `{0,1} ⊂ ZMod 5` is the central binomial value `70`. -/
theorem rEnergy_four_twoPoint : rEnergy twoPoint 4 = 70 := by decide

/-- At depth four, the universal swap floor for the two-point Sidon set is only `28`. -/
theorem swap_floor_four_twoPoint : 2 * twoPoint.card ^ 4 - twoPoint.card ^ 2 = 28 := by decide

/-- **Sidon swap-floor sharpness still fails at depth four.**
The Sidon set `{0,1} ⊂ ZMod 5` has `rEnergy = 70`, strictly above the swap floor `28`. -/
theorem sidon_depth_four_not_swap_sharp :
    2 * twoPoint.card ^ 4 - twoPoint.card ^ 2 < rEnergy twoPoint 4 := by
  rw [swap_floor_four_twoPoint, rEnergy_four_twoPoint]
  norm_num

end ArkLib.ProximityGap.Frontier.SidonDepthFourNonSharp

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.SidonDepthFourNonSharp.rEnergy_four_twoPoint
#print axioms ArkLib.ProximityGap.Frontier.SidonDepthFourNonSharp.sidon_depth_four_not_swap_sharp
