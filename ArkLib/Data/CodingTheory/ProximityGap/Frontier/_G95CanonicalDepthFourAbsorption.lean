/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G94CanonicalSlotDecoder
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G84CanonicalSlotsDepthFive

/-!
# G95: actual depth-four sector absorption from the shallow core-energy bound

G94 supplies the genuine canonical-slot decoder. G84 supplies the exact production arithmetic.
This file composes them: no decoder, occurrence, padding-order, or slot-enumeration hypothesis
remains. The sole input is the square bound on the actual equal-sum depth-four core type.
Issue #466/#505.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G95CanonicalDepthFourAbsorption

open G84CanonicalSlotsDepthFive
open G88EqualSumCorrectedDecoder
open G94CanonicalSlotDecoder

/-- **Actual depth-four sector consumer.** -/
theorem production_depth_four_actual_sector_absorbed
    (A B : Type*) [AddCancelCommMonoid B] [Fintype A] [DecidableEq A]
    (ι : A → B) (hcard : Fintype.card A = productionN)
    (hcore : Fintype.card (EqualSumCorePair A B ι 4) ^ 2 ≤
      7600 ^ 2 * productionN ^ 13) :
    Fintype.card (MaxCancellationCollisionSector A B ι 110 4) ≤
      productionWickBudget := by
  apply production_depth_four_canonical_absorbed
      (K := Fintype.card (EqualSumCorePair A B ι 4))
  · calc
      Fintype.card (MaxCancellationCollisionSector A B ι 110 4) ≤
          Fintype.card (EqualSumCorePair A B ι 4) * ((110 : ℕ).choose 4) ^ 2 *
            (110 - 4).factorial * (Fintype.card A) ^ (110 - 4) :=
        card_collisionSector_le_canonical A B ι 110 4 (by norm_num)
      _ = canonicalPadEnvelope productionN 110
          (Fintype.card (EqualSumCorePair A B ι 4)) 4 := by
        rw [hcard]
        unfold canonicalPadEnvelope
        rfl
  · exact hcore

end ArkLib.ProximityGap.Frontier.G95CanonicalDepthFourAbsorption

#print axioms
  ArkLib.ProximityGap.Frontier.G95CanonicalDepthFourAbsorption.production_depth_four_actual_sector_absorbed
