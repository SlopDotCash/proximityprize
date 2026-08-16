/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R330Depth3WickLargeChar
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodMomentBound

/-!
# R338: depth-3 incomplete-sum bound in large characteristic

The depth-3 Wick theorem is threaded through the existing moment-method
consumer.  The output is the honest finite-rung scale, not the logarithmic-
depth prize bound.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.R338Depth3IncompleteSumLargeChar

open ArkLib.ProximityGap.Frontier.FS5TrivialCountClosedForm
open ArkLib.ProximityGap.Frontier.R330Depth3WickLargeChar
open ArkLib.ProximityGap.GaussPeriodMomentBound
open ArkLib.ProximityGap.InteriorWorstCaseIncompleteSum

theorem worstCaseIncompleteSumBound_of_large_characteristic_depth3
    {k prime : ℕ} {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {ζ : F} {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (hm : 0 < 2 ^ k) (hprim : IsPrimitiveRoot ζ (2 * 2 ^ k))
    (hhalfTurn : ζ ^ (2 ^ k) = -1)
    (hprime : 2 ^ ((k + 1 + 3) * 2 ^ (k + 1)) < prime)
    [CharP F prime] :
    WorstCaseIncompleteSumBound ψ (Gset ζ (2 ^ k))
      (((Fintype.card F : ℝ) * 15 * (Gset ζ (2 ^ k)).card ^ 3) ^ ((3 : ℝ)⁻¹)) := by
  apply worstCaseIncompleteSumBound_of_energyBound hψ (r := 3) (by norm_num)
  simpa [Nat.doubleFactorial] using
    (gaussianEnergyBound_three_of_characteristic_above_height
      hψ hm hprim hhalfTurn hprime)

end ArkLib.ProximityGap.Frontier.R338Depth3IncompleteSumLargeChar

#print axioms ArkLib.ProximityGap.Frontier.R338Depth3IncompleteSumLargeChar.worstCaseIncompleteSumBound_of_large_characteristic_depth3
