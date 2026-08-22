/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.SidonDepthFiveNoWrapNonSharp

/-!
# A depth-six no-wrap two-point Sidon witness (#444)

`SidonDepthFiveNoWrapNonSharp` pins the no-wrap depth-five control case for the two-point
Sidon set `{0,1} ⊂ ZMod 7`: the relation energy is the central-binomial value `C(10,5)`
rather than the much smaller swap floor.

This file extends that exact incidence boundary by one rung.  For `G = {0,1} ⊂ ZMod 7`,
six-fold sums of zeros and ones range from `0` to `6`, so no two distinct integer sums
wrap modulo `7`.  The depth-six relation energy is therefore the no-wrap central-binomial
value `C(12,6)=924`, while the universal swap floor is only `2*|G|^6 - |G|^2 = 124`.

This is a small Sidon/incidence calibration brick only.  It makes no CORE upper-bound,
char-`p` transfer, capacity, or growth-law claim.
-/

set_option maxRecDepth 100000


open Finset
open ArkLib.ProximityGap.SubgroupGaussSumMoment (rEnergy IsSidonSet)

namespace ArkLib.ProximityGap.Frontier.SidonDepthSixNoWrapNonSharp

local instance localInstance_SidonDepthSixNoWrapNonSharp_1 : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- The same no-wrap two-point witness used at depth five. -/
def twoPoint7 : Finset (ZMod 7) := {0, 1}

@[simp] theorem twoPoint7_card : twoPoint7.card = 2 := by decide

/-- `{0,1}` is a plain Sidon set in `ZMod 7`. -/
theorem twoPoint7_sidon : IsSidonSet twoPoint7 := by
  unfold IsSidonSet twoPoint7
  decide

/-- The depth-six relation energy of `{0,1} ⊂ ZMod 7` is the no-wrap
central-binomial value `C(12,6)=924`. -/
theorem rEnergy_six_twoPoint7 : rEnergy twoPoint7 6 = 924 := by decide

/-- At depth six, the universal swap floor for the no-wrap two-point Sidon set is only `124`. -/
theorem swap_floor_six_twoPoint7 : 2 * twoPoint7.card ^ 6 - twoPoint7.card ^ 2 = 124 := by decide

/-- **Sidon swap-floor sharpness fails at depth six even before modular wraparound.**
The Sidon set `{0,1} ⊂ ZMod 7` has `rEnergy = 924`, strictly above the swap floor `124`. -/
theorem sidon_depth_six_noWrap_not_swap_sharp :
    2 * twoPoint7.card ^ 6 - twoPoint7.card ^ 2 < rEnergy twoPoint7 6 := by
  rw [swap_floor_six_twoPoint7, rEnergy_six_twoPoint7]
  norm_num

/-! ## Axiom audit -/
#print axioms twoPoint7_sidon
#print axioms rEnergy_six_twoPoint7
#print axioms sidon_depth_six_noWrap_not_swap_sharp

end ArkLib.ProximityGap.Frontier.SidonDepthSixNoWrapNonSharp
