/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R332NoJohnsonLargeChar

/-!
# R333: clean dyadic field-size criterion for the Johnson-scale exclusion

The subgroup cardinality is exactly `2^(k+1)`.  This corollary removes the
abstract `G.card` side condition from R332 and exposes the criterion in the
parameters used by the proximity-prize regime.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.R333NoJohnsonDyadicCriterion

open ArkLib.ProximityGap.Frontier.FS5TrivialCountClosedForm
open ArkLib.ProximityGap.Frontier.R330Depth3WickLargeChar
open ArkLib.ProximityGap.Frontier.R332NoJohnsonLargeChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

theorem no_johnson_scale_frequency_of_dyadic_field_size
    {k prime : ℕ} {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {ζ : F} {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (hm : 0 < 2 ^ k) (hprim : IsPrimitiveRoot ζ (2 * 2 ^ k))
    (hhalfTurn : ζ ^ (2 ^ k) = -1)
    (hprime : 2 ^ ((k + 1 + 3) * 2 ^ (k + 1)) < prime)
    (hscale : 15 * ((2 * 2 ^ k : ℕ) : ℝ) ^ 3 <
      (Fintype.card F : ℝ) ^ 2) [CharP F prime] :
    (Finset.univ.filter (fun b : F => (Fintype.card F : ℝ) ≤
      ‖eta ψ (Gset ζ (2 ^ k)) b‖ ^ 2)) = ∅ := by
  apply no_johnson_scale_frequency_of_large_characteristic
    hψ hm hprim hhalfTurn hprime
  rw [Gset_card hm hprim]
  exact hscale

end ArkLib.ProximityGap.Frontier.R333NoJohnsonDyadicCriterion

#print axioms ArkLib.ProximityGap.Frontier.R333NoJohnsonDyadicCriterion.no_johnson_scale_frequency_of_dyadic_field_size
