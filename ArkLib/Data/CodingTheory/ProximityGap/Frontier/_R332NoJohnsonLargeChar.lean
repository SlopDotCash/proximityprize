/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R330Depth3WickLargeChar
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSixthMarkovWick

/-!
# R332: no Johnson-scale frequencies in the large-characteristic rung

The explicit depth-3 Wick theorem immediately discharges the existing
sixth-moment Markov consumer whenever `15 |G|^3 < |F|^2`.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.R332NoJohnsonLargeChar

open ArkLib.ProximityGap.Frontier.FS5TrivialCountClosedForm
open ArkLib.ProximityGap.Frontier.R330Depth3WickLargeChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumSixthMoment

theorem no_johnson_scale_frequency_of_large_characteristic
    {k prime : ℕ} {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {ζ : F} {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (hm : 0 < 2 ^ k) (hprim : IsPrimitiveRoot ζ (2 * 2 ^ k))
    (hhalfTurn : ζ ^ (2 ^ k) = -1)
    (hprime : 2 ^ ((k + 1 + 3) * 2 ^ (k + 1)) < prime)
    (hscale : 15 * ((Gset ζ (2 ^ k)).card : ℝ) ^ 3 <
      (Fintype.card F : ℝ) ^ 2) [CharP F prime] :
    (Finset.univ.filter (fun b : F => (Fintype.card F : ℝ) ≤
      ‖eta ψ (Gset ζ (2 ^ k)) b‖ ^ 2)) = ∅ := by
  exact no_johnson_scale_frequency_of_wick_lt hψ (Gset ζ (2 ^ k))
    Fintype.card_pos
    (gaussianEnergyBound_three_of_characteristic_above_height
      hψ hm hprim hhalfTurn hprime)
    hscale

end ArkLib.ProximityGap.Frontier.R332NoJohnsonLargeChar

#print axioms ArkLib.ProximityGap.Frontier.R332NoJohnsonLargeChar.no_johnson_scale_frequency_of_large_characteristic
