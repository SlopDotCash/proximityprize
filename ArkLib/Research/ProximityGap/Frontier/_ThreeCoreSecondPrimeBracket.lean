/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier._ThreeCoreSecondPrimeArithmetic
import ArkLib.Research.ProximityGap.Frontier._ThreeCoreTwoThirdsFloor
import ArkLib.Research.ProximityGap.Frontier._TwoCorePackingThreshold

/-!
# A two-sided bracket for the second production prime

Three explicit affine heads and the extra site at the domain identity give more than
the scalar budget at 715827882 errors. The incidence estimate supplies the other
endpoint at rate one sixteenth.
-/

open ProximityGap ProximityGap.MCAThresholdLedger ArkLib.ProximityGap.KKH26
open ArkLib.ProximityGap.PrizeShapePrimeP30Second
open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.Frontier.ThreeCoreSecondPrimeBracket

local instance : Fact P.Prime := ⟨prime_P⟩

/-- At every dimension in this range the explicit three-head construction exceeds the
second field's security budget. -/
theorem secondPrime_ceiling {k : ℕ} (hk : 2 ≤ k) (hkr : k ≤ 357913941) :
    mcaDeltaStar (F := ZMod P) (A := ZMod P) (evalCode PrizeShapePrimeP30Second.g (2 ^ 30) (k - 1))
      (ProximityGap.epsStar : ℝ≥0∞) ≤ (715827882 / 1073741824 : ℝ≥0) := by
  have hg0 := KKH26RegimeSplit.ne_zero_of_orderOf_eq orderOf_g
  let dom := KKH26RegimeSplit.powDomain PrizeShapePrimeP30Second.g orderOf_g hg0
  have hzero : dom 0 = 1 := by
    change PrizeShapePrimeP30Second.g ^ (0 : ℕ) = 1
    exact pow_zero _
  have hroot (z : Fin (2 ^ 30)) : (dom z) ^ (2 ^ 30 : ℕ) = 1 := by
    change (PrizeShapePrimeP30Second.g ^ z.val) ^ (2 ^ 30 : ℕ) = 1
    have hpow : PrizeShapePrimeP30Second.g ^ (2 ^ 30 : ℕ) = 1 := by
      simpa only [orderOf_g] using pow_orderOf_eq_one PrizeShapePrimeP30Second.g
    rw [← pow_mul, Nat.mul_comm, pow_mul, hpow, one_pow]
  have hpack := ThreeCoreTwoThirdsFloor.epsMCA_lower_bound dom
    (r := 357913941) (by decide) (by decide) hk hkr hzero hroot
    ThreeCoreSecondPrimeArithmetic.scale_injective
    ThreeCoreSecondPrimeArithmetic.exceptional_injective
    ThreeCoreSecondPrimeArithmetic.exceptional_separation
  have hcode : evalCode PrizeShapePrimeP30Second.g (2 ^ 30) (k - 1) =
      (ReedSolomon.code dom k : Set (Fin (2 ^ 30) → ZMod P)) := by
    simpa only [dom, show k - 1 + 1 = k by omega] using
      KKH26RegimeSplit.evalCode_eq_reedSolomon PrizeShapePrimeP30Second.g orderOf_g hg0 (k - 1)
  apply mcaDeltaStar_le_of_bad
  rw [hcode, PrizeShapeRateHalfBracket.epsStar_coe_eq_natCast_inv]
  apply lt_of_lt_of_le _ hpack
  have hp0 : (P : ℝ≥0∞) ≠ 0 := by exact_mod_cast prime_P.ne_zero
  have hq0 : ((2 ^ 128 : ℕ) : ℝ≥0∞) ≠ 0 := by norm_num
  rw [ENNReal.lt_div_iff_mul_lt (Or.inl hp0) (Or.inl (ENNReal.natCast_ne_top P)),
    ← ENNReal.div_eq_inv_mul,
    ENNReal.div_lt_iff (Or.inl hq0) (Or.inl (ENNReal.natCast_ne_top _))]
  exact_mod_cast (by decide : P < (6 * 357913941 + 3) * 2 ^ 128)

/-- At rate one sixteenth both endpoints refer to the same field, code and error target. -/
theorem secondPrime_rateSixteenth_bracket :
    let δ := mcaDeltaStar (F := ZMod P) (A := ZMod P) (evalCode PrizeShapePrimeP30Second.g (2 ^ 30) (2 ^ 26 - 1))
        (ProximityGap.epsStar : ℝ≥0∞)
    (647626308 / 1073741824 : ℝ≥0) ≤ δ ∧ δ ≤ (715827882 / 1073741824 : ℝ≥0) :=
  ⟨TwoCorePackingThreshold.secondPrime_rateSixteenth_floor, secondPrime_ceiling (by decide) (by decide)⟩

end ArkLib.ProximityGap.Frontier.ThreeCoreSecondPrimeBracket

#print axioms ArkLib.ProximityGap.Frontier.ThreeCoreSecondPrimeBracket.secondPrime_ceiling
#print axioms ArkLib.ProximityGap.Frontier.ThreeCoreSecondPrimeBracket.secondPrime_rateSixteenth_bracket
