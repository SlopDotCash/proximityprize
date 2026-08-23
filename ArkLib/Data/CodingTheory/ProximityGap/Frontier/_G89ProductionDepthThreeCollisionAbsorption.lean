/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G88EqualSumCorrectedDecoder
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G82DepthTwoEnergySaddleBridge

/-!
# G89: unconditional production absorption of the depth-three collision sector

G88 gives the genuine maximal-cancellation collision sector the elementary equal-sum corrected
padding bound. G82 proves that exact numerical envelope fits inside the full production Wick
budget at `(n,r)=(2^30,110)`. This file composes them. Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G89ProductionDepthThreeCollisionAbsorption

open G88EqualSumCorrectedDecoder
open G81FactorialPaddingWickAbsorption
open G82DepthTwoEnergySaddleBridge

/-- **Depth three is fully discharged at production scale.** This theorem includes canonical
maximal cancellation, occurrence-correct decoder extraction, the equal-sum fiber saving, the
missing relative padding factorial, and the exact final Wick comparison. -/
theorem production_depth_three_collision_sector_absorbed
    (A B : Type*) [AddCancelCommMonoid B] [Fintype A] [DecidableEq A]
    (ι : A → B) (hι : Function.Injective ι)
    (hcard : Fintype.card A = 2 ^ 30) :
    Fintype.card (MaxCancellationCollisionSector A B ι 110 3) ≤
      Nat.doubleFactorial (2 * 110 - 1) * (2 ^ 30) ^ 110 := by
  calc
    Fintype.card (MaxCancellationCollisionSector A B ι 110 3) ≤
        (Fintype.card A) ^ (2 * 3 - 1) * ((110 : ℕ).descFactorial 3) ^ 2 *
          (110 - 3).factorial * (Fintype.card A) ^ (110 - 3) :=
      card_collisionSector_le_factorialCorrected A B ι hι 110 3
        (by norm_num) (by norm_num)
    _ = (2 ^ 30) ^ 5 * correctedPadEnvelope (2 ^ 30) 110 1 3 := by
      rw [hcard]
      norm_num [correctedPadEnvelope]
    _ ≤ Nat.doubleFactorial (2 * 110 - 1) * (2 ^ 30) ^ 110 :=
      production_all_equal_sum_depth_three_core_pairs_le_fullWick

/-- Finset-facing specialization used by the subgroup moment problem: the alphabet is the subtype
of elements of `G`, and its value map into the ambient additive field is `Subtype.val`. -/
theorem production_depth_three_finset_collision_sector_absorbed
    (F : Type*) [AddCommGroup F] [Fintype F] [DecidableEq F]
    (G : Finset F) (hcard : G.card = 2 ^ 30) :
    Fintype.card (MaxCancellationCollisionSector {x // x ∈ G} F
      (fun x => x.1) 110 3) ≤
      Nat.doubleFactorial (2 * 110 - 1) * (2 ^ 30) ^ 110 := by
  apply production_depth_three_collision_sector_absorbed
      {x // x ∈ G} F (fun x => x.1) Subtype.val_injective
  simpa using hcard

end ArkLib.ProximityGap.Frontier.G89ProductionDepthThreeCollisionAbsorption

#print axioms
  ArkLib.ProximityGap.Frontier.G89ProductionDepthThreeCollisionAbsorption.production_depth_three_collision_sector_absorbed
#print axioms
  ArkLib.ProximityGap.Frontier.G89ProductionDepthThreeCollisionAbsorption.production_depth_three_finset_collision_sector_absorbed
