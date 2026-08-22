/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.REnergySwapFloorSidonSharp

/-!
# A depth-five two-point Sidon witness without modular wraparound (#444)

`SidonDepthFiveNonSharp` records the depth-five witness `{0,1} ⊂ ZMod 5`, where the exact
energy is `254`: the ordinary central-binomial contribution plus two wraparound pairs.
This file pins the matching no-wrap control case in `ZMod 7`.

For `G = {0,1} ⊂ ZMod 7`, five-fold sums of zeros and ones range from `0` to `5`, so no two
distinct integer sums become equal modulo `7`.  The exact relation energy is therefore the
central binomial value `C(10,5)=252`, still far above the naive swap floor
`2*|G|^5 - |G|^2 = 60`.

This is a small exact incidence/Sidon boundary brick only.  It makes no CORE upper-bound,
char-`p` transfer, capacity, or growth-law claim.
-/

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumMoment (rEnergy IsSidonSet)

namespace ArkLib.ProximityGap.Frontier.SidonDepthFiveNoWrapNonSharp

local instance localInstance_SidonDepthFiveNoWrapNonSharp_1 : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- The no-wrap two-point Sidon witness in `ZMod 7`. -/
def twoPoint7 : Finset (ZMod 7) := {0, 1}

@[simp] theorem twoPoint7_card : twoPoint7.card = 2 := by decide

/-- `{0,1}` is a plain Sidon set in `ZMod 7`. -/
theorem twoPoint7_sidon : IsSidonSet twoPoint7 := by
  unfold IsSidonSet twoPoint7
  decide

/-- The depth-five relation energy of `{0,1} ⊂ ZMod 7` is the no-wrap
central-binomial value `252`. -/
theorem rEnergy_five_twoPoint7 : rEnergy twoPoint7 5 = 252 := by decide

/-- At depth five, the universal swap floor for the no-wrap two-point Sidon set is only `60`. -/
theorem swap_floor_five_twoPoint7 : 2 * twoPoint7.card ^ 5 - twoPoint7.card ^ 2 = 60 := by decide

/-- **Sidon swap-floor sharpness fails at depth five even before modular wraparound.**
The Sidon set `{0,1} ⊂ ZMod 7` has `rEnergy = 252`, strictly above the swap floor `60`. -/
theorem sidon_depth_five_noWrap_not_swap_sharp :
    2 * twoPoint7.card ^ 5 - twoPoint7.card ^ 2 < rEnergy twoPoint7 5 := by
  rw [swap_floor_five_twoPoint7, rEnergy_five_twoPoint7]
  norm_num

/-! ## Axiom audit -/
#print axioms twoPoint7_sidon
#print axioms rEnergy_five_twoPoint7
#print axioms sidon_depth_five_noWrap_not_swap_sharp

end ArkLib.ProximityGap.Frontier.SidonDepthFiveNoWrapNonSharp
