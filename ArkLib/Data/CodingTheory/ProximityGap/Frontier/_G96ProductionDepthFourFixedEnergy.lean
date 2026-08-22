/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G88EqualSumCorrectedDecoder
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G81FactorialPaddingWickAbsorption

/-!
# G96: production depth four from a fixed-energy estimate

The corrected mapped-alphabet decoder identifies the depth-four core count with the finite type of
ordered equal-sum four-tuples.  At `(n,r)=(2^30,110)`, a squared core-count estimate

`J₄² ≤ 128 * n¹³`

is sufficient to absorb the entire actual depth-four maximal-cancellation sector into the full
Wick budget.  The exponent is the one obtained from `E₄ ≤ n⁴ E₂` and
`E₂² ≤ 128 n⁵`; only the fixed-depth subgroup energy constant remains to be supplied. Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G96ProductionDepthFourFixedEnergy

open G88EqualSumCorrectedDecoder
open G81FactorialPaddingWickAbsorption

/-- Exact production arithmetic for the mapped equal-sum core type at depth four. -/
theorem production_depth_four_of_core_sq
    (A B : Type*) [AddCancelCommMonoid B] [Fintype A] [DecidableEq A]
    (ι : A → B) (hcard : Fintype.card A = 2 ^ 30)
    (hcore : (Fintype.card (EqualSumCorePair A B ι 4)) ^ 2 ≤
      128 * (2 ^ 30) ^ 13) :
    Fintype.card (MaxCancellationCollisionSector A B ι 110 4) ≤
      Nat.doubleFactorial (2 * 110 - 1) * (2 ^ 30) ^ 110 := by
  let J := Fintype.card (EqualSumCorePair A B ι 4)
  let P := correctedPadEnvelope (2 ^ 30) 110 1 4
  let T := Nat.doubleFactorial (2 * 110 - 1) * (2 ^ 30) ^ 110
  have hsector :
      Fintype.card (MaxCancellationCollisionSector A B ι 110 4) ≤ J * P := by
    calc
      Fintype.card (MaxCancellationCollisionSector A B ι 110 4) ≤
          J * ((110 : ℕ).descFactorial 4) ^ 2 * (110 - 4).factorial *
            (Fintype.card A) ^ (110 - 4) :=
        card_collisionSector_le_correctedCoreCount A B ι 110 4 (by norm_num)
      _ = J * P := by
        rw [hcard]
        simp only [P, correctedPadEnvelope]
        ring
  have hnumeric :
      (128 * (2 ^ 30) ^ 13) * P ^ 2 ≤ T ^ 2 := by
    norm_num [P, T, correctedPadEnvelope, Nat.doubleFactorial, Nat.descFactorial]
  have hsq : (J * P) ^ 2 ≤ T ^ 2 := by
    calc
      (J * P) ^ 2 = J ^ 2 * P ^ 2 := by ring
      _ ≤ (128 * (2 ^ 30) ^ 13) * P ^ 2 := Nat.mul_le_mul_right _ hcore
      _ ≤ T ^ 2 := hnumeric
  have hJP : J * P ≤ T :=
    (Nat.pow_le_pow_iff_left (by norm_num : (2 : ℕ) ≠ 0)).mp hsq
  exact hsector.trans hJP

/-- Finset-facing specialization for a subgroup alphabet embedded in its ambient field. -/
theorem production_depth_four_finset_of_core_sq
    (F : Type*) [AddCancelCommMonoid F] [Fintype F] [DecidableEq F]
    (G : Finset F) (hcard : G.card = 2 ^ 30)
    (hcore : (Fintype.card
      (EqualSumCorePair {x // x ∈ G} F (fun x => x.1) 4)) ^ 2 ≤
        128 * (2 ^ 30) ^ 13) :
    Fintype.card (MaxCancellationCollisionSector {x // x ∈ G} F
      (fun x => x.1) 110 4) ≤
      Nat.doubleFactorial (2 * 110 - 1) * (2 ^ 30) ^ 110 := by
  apply production_depth_four_of_core_sq {x // x ∈ G} F (fun x => x.1)
  · simpa using hcard
  · exact hcore

/-- Arithmetic transport from a second-energy bound.  In the intended application `E₂` is the
ordinary additive energy of the subgroup and `htransport` is Young's
`E₄ ≤ n⁴ E₂` convolution inequality. -/
theorem production_depth_four_of_secondEnergy
    (A B : Type*) [AddCancelCommMonoid B] [Fintype A] [DecidableEq A]
    (ι : A → B) (hcard : Fintype.card A = 2 ^ 30) (E₂ : ℕ)
    (htransport : Fintype.card (EqualSumCorePair A B ι 4) ≤ (2 ^ 30) ^ 4 * E₂)
    (hsecond : E₂ ^ 2 ≤ 128 * (2 ^ 30) ^ 5) :
    Fintype.card (MaxCancellationCollisionSector A B ι 110 4) ≤
      Nat.doubleFactorial (2 * 110 - 1) * (2 ^ 30) ^ 110 := by
  apply production_depth_four_of_core_sq A B ι hcard
  calc
    (Fintype.card (EqualSumCorePair A B ι 4)) ^ 2 ≤
        ((2 ^ 30) ^ 4 * E₂) ^ 2 := Nat.pow_le_pow_left htransport 2
    _ = (2 ^ 30) ^ 8 * E₂ ^ 2 := by ring
    _ ≤ (2 ^ 30) ^ 8 * (128 * (2 ^ 30) ^ 5) :=
      Nat.mul_le_mul_left _ hsecond
    _ = 128 * (2 ^ 30) ^ 13 := by ring

end ArkLib.ProximityGap.Frontier.G96ProductionDepthFourFixedEnergy

#print axioms
  ArkLib.ProximityGap.Frontier.G96ProductionDepthFourFixedEnergy.production_depth_four_of_core_sq
#print axioms
  ArkLib.ProximityGap.Frontier.G96ProductionDepthFourFixedEnergy.production_depth_four_finset_of_core_sq
#print axioms
  ArkLib.ProximityGap.Frontier.G96ProductionDepthFourFixedEnergy.production_depth_four_of_secondEnergy
