import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FS5TrivialCountClosedForm
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R327Depth3ExcessVanishing

/-!
# R330: large-characteristic depth-3 Wick bound

The exact closed-form depth-3 energy from R329 is below the Gaussian Wick
target, so the FS5 headroom consumer yields `GaussianEnergyBound` outright.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.R330Depth3WickLargeChar

open ArkLib.ProximityGap.Frontier.FS5TrivialCountClosedForm
open ArkLib.ProximityGap.Frontier.R327Depth3ExcessVanishing
open ArkLib.ProximityGap.GaussPeriodMomentBound

theorem gaussianEnergyBound_three_of_characteristic_above_height
    {k prime : ℕ} {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {ζ : F} {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (hm : 0 < 2 ^ k) (hprim : IsPrimitiveRoot ζ (2 * 2 ^ k))
    (hhalfTurn : ζ ^ (2 ^ k) = -1)
    (hprime : 2 ^ ((k + 1 + 3) * 2 ^ (k + 1)) < prime)
    [CharP F prime] :
    GaussianEnergyBound (Gset ζ (2 ^ k)) 3 := by
  apply gaussianEnergyBound_three_of_wraparound_headroom hψ hm hprim
  rw [wraparoundExcess_eq_zero_of_characteristic_above_height
    (k := k) (prime := prime) (ζ := ζ) hhalfTurn hprime]
  have hcard : ((Gset ζ (2 ^ k)).card : ℝ) = (2 * (2 ^ k : ℕ) : ℝ) := by
    exact_mod_cast Gset_card hm hprim
  rw [hcard]
  have hx : 0 ≤ (2 * (2 ^ k : ℝ)) := by positivity
  have hx2 : 2 ≤ (2 * (2 ^ k : ℝ)) := by
    have hk : (1 : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by
      exact_mod_cast (Nat.one_le_two_pow : 1 ≤ 2 ^ k)
    norm_num [Nat.cast_pow] at hk
    nlinarith
  nlinarith

end ArkLib.ProximityGap.Frontier.R330Depth3WickLargeChar

#print axioms
  ArkLib.ProximityGap.Frontier.R330Depth3WickLargeChar.gaussianEnergyBound_three_of_characteristic_above_height
