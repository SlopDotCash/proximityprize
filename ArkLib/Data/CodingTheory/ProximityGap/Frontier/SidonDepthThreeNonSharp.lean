/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.REnergySwapFloorSidonSharp

/-!
# A concrete Sidon set where the swap floor stops being sharp at depth three (#444)

`REnergySwapFloorSidonSharp` proves the universal swap floor is exact at `r = 2` for
plain Sidon sets. Its docstring records, probe-backed, that the same sharpness is false at
`r ≥ 3`: even a two-point Sidon set has extra higher-order coincidences.

This file pins the first non-sharp case axiom-clean. In `ZMod 5`, the two-point set
`G = {0, 1}` is Sidon, but

* `rEnergy G 3 = 20`, the binomial-square count `∑_{s=0}^3 C(3,s)^2`, while
* the depth-three swap floor is `2*|G|^3 - |G|^2 = 12`.

So Sidon sharpness is genuinely a depth-2 phenomenon. This is a small incidence/Sidon
boundary brick only: no CORE upper bound, no char-`p` transfer, no capacity or growth-law claim.
-/

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumMoment (rEnergy IsSidonSet)

namespace ArkLib.ProximityGap.Frontier.SidonDepthThreeNonSharp

local instance localInstance_SidonDepthThreeNonSharp_1 : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- The concrete two-point Sidon witness in `ZMod 5`. -/
def twoPoint : Finset (ZMod 5) := {0, 1}

@[simp] theorem twoPoint_card : twoPoint.card = 2 := by decide

/-- `{0,1}` is a plain Sidon set in `ZMod 5`. -/
theorem twoPoint_sidon : IsSidonSet twoPoint := by
  unfold IsSidonSet twoPoint
  decide

/-- The depth-three relation energy of `{0,1}` is the central binomial value `20`. -/
theorem rEnergy_three_twoPoint : rEnergy twoPoint 3 = 20 := by decide

/-- At depth three, the universal swap floor for the two-point Sidon set is only `12`. -/
theorem swap_floor_three_twoPoint : 2 * twoPoint.card ^ 3 - twoPoint.card ^ 2 = 12 := by decide

/-- **Sidon sharpness fails already at depth three.**
The Sidon set `{0,1} ⊂ ZMod 5` has `rEnergy = 20`, strictly above the swap floor `12`. -/
theorem sidon_depth_three_not_swap_sharp :
    2 * twoPoint.card ^ 3 - twoPoint.card ^ 2 < rEnergy twoPoint 3 := by
  rw [swap_floor_three_twoPoint, rEnergy_three_twoPoint]
  norm_num

end ArkLib.ProximityGap.Frontier.SidonDepthThreeNonSharp

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.SidonDepthThreeNonSharp.twoPoint_sidon
#print axioms ArkLib.ProximityGap.Frontier.SidonDepthThreeNonSharp.rEnergy_three_twoPoint
#print axioms ArkLib.ProximityGap.Frontier.SidonDepthThreeNonSharp.sidon_depth_three_not_swap_sharp
