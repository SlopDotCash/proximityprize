import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R330Depth3WickLargeChar
import ArkLib.Data.CodingTheory.ProximityGap.DCMomentSupBound

/-!
# R331: explicit non-DC sixth-moment bound for each period

The large-characteristic depth-3 Wick rung feeds the DC-subtracted moment
consumer.  This records the resulting per-frequency inequality, retaining the
principal-character subtraction that is essential near the prize scale.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.R331Depth3PeriodMomentLargeChar

open ArkLib.ProximityGap.Frontier.FS5TrivialCountClosedForm
open ArkLib.ProximityGap.Frontier.R330Depth3WickLargeChar
open ArkLib.ProximityGap.DCMomentSupBound
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

theorem period_sixth_power_le_of_characteristic_above_height
    {k prime : ℕ} {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {ζ : F} {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (hm : 0 < 2 ^ k) (hprim : IsPrimitiveRoot ζ (2 * 2 ^ k))
    (hhalfTurn : ζ ^ (2 ^ k) = -1)
    (hprime : 2 ^ ((k + 1 + 3) * 2 ^ (k + 1)) < prime)
    {b : F} (hb : b ≠ 0) [CharP F prime] :
    ‖eta ψ (Gset ζ (2 ^ k)) b‖ ^ 6 ≤
      (Fintype.card F : ℝ) *
          ((Nat.doubleFactorial 5 : ℝ) * (Gset ζ (2 ^ k)).card ^ 3) -
        (Gset ζ (2 ^ k)).card ^ 6 := by
  have henergy := gaussianEnergyBound_three_of_characteristic_above_height
    hψ hm hprim hhalfTurn hprime
  simpa [show 2 * 3 = 6 by norm_num] using
    (eta_pow_le_dc_of_energyBound hψ (G := Gset ζ (2 ^ k)) (r := 3) henergy hb)

end ArkLib.ProximityGap.Frontier.R331Depth3PeriodMomentLargeChar

#print axioms ArkLib.ProximityGap.Frontier.R331Depth3PeriodMomentLargeChar.period_sixth_power_le_of_characteristic_above_height
