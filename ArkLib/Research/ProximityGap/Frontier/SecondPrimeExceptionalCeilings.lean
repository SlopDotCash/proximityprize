/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.ExceptionalHeadLayout
import ArkLib.Research.ProximityGap.KKH26RegimeSplit
import ArkLib.Research.ProximityGap.Frontier._PrizeShapePrimeP30Second
import ArkLib.Research.ProximityGap.Frontier._PrizeShapeRateHalfBracket

/-! # Second-prime upper bounds from exceptional sites

Each head omits one root from a block of size equal to the code dimension.
Four or five such heads on the entire production domain exceed the second
prime's challenge budget at rates one half, one quarter, and one eighth.
-/

open ProximityGap ProximityGap.MCAThresholdLedger ArkLib.ProximityGap.KKH26
open ArkLib.ProximityGap.PrizeShapePrimeP30Second
open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.Frontier.SecondPrimeExceptionalCeilings

local instance : Fact P.Prime := ⟨prime_P⟩

private theorem ceiling {r k e m : ℕ}
    (hm : m ≤ k) (hn : k + m * r ≤ 2 ^ 30) (hk : k ≤ k - 1 + r) (hkpos : 0 < k)
    (hsize : (1 - (e : ℝ≥0) / 1073741824) * 1073741824 ≤ ((k - 1 + r + 1 : ℕ) : ℝ≥0))
    (hfield : (m * (2 ^ 30 - (k - 1 + r))).choose 2 ≤ P)
    (hbudget : P < (m * (2 ^ 30 - (k - 1 + r))) * 2 ^ 128) :
    mcaDeltaStar (F := ZMod P) (A := ZMod P)
      (evalCode PrizeShapePrimeP30Second.g (2 ^ 30) (k - 1))
      (ProximityGap.epsStar : ℝ≥0∞) ≤ (e : ℝ≥0) / 1073741824 := by
  have hg0 := KKH26RegimeSplit.ne_zero_of_orderOf_eq orderOf_g
  let dom := KKH26RegimeSplit.powDomain PrizeShapePrimeP30Second.g orderOf_g hg0
  have hmass := ExceptionalHeadLayout.mass dom ((e : ℝ≥0) / 1073741824) hm hn hk
    (by rw [ZMod.card]; decide) (by norm_num at hsize ⊢; exact hsize)
    (by simpa only [Nat.card_eq_fintype_card, ZMod.card] using hfield)
  rw [ZMod.card] at hmass
  have hcode : evalCode PrizeShapePrimeP30Second.g (2 ^ 30) (k - 1) =
      (ReedSolomon.code dom k : Set (Fin (2 ^ 30) → ZMod P)) := by
    simpa only [dom, show k - 1 + 1 = k by omega] using
      KKH26RegimeSplit.evalCode_eq_reedSolomon PrizeShapePrimeP30Second.g orderOf_g hg0 (k - 1)
  apply mcaDeltaStar_le_of_bad
  rw [hcode, PrizeShapeRateHalfBracket.epsStar_coe_eq_natCast_inv]
  apply lt_of_lt_of_le _ hmass
  have hp0 : (P : ℝ≥0∞) ≠ 0 := by exact_mod_cast prime_P.ne_zero
  have hq0 : ((2 ^ 128 : ℕ) : ℝ≥0∞) ≠ 0 := by norm_num
  rw [ENNReal.lt_div_iff_mul_lt (Or.inl hp0) (Or.inl (ENNReal.natCast_ne_top P)),
    ← ENNReal.div_eq_inv_mul,
    ENNReal.div_lt_iff (Or.inl hq0) (Or.inl (ENNReal.natCast_ne_top _))]
  exact_mod_cast hbudget

/-- At rate one half the second-prime threshold is at most 429496730 errors. -/
theorem rateHalf_ceiling :
    mcaDeltaStar (F := ZMod P) (A := ZMod P)
      (evalCode PrizeShapePrimeP30Second.g (2 ^ 30) (2 ^ 29 - 1))
      (ProximityGap.epsStar : ℝ≥0∞) ≤ (429496730 / 1073741824 : ℝ≥0) :=
  ceiling (m := 5) (r := 107374182) (e := 429496730)
    (by decide) (by decide) (by decide) (by decide) (by norm_num [tsub_mul, div_mul_cancel₀])
    (by rw [Nat.choose_two_right]; decide) (by decide)

/-- At rate one quarter the second-prime threshold is at most 603979776 errors. -/
theorem rateQuarter_ceiling :
    mcaDeltaStar (F := ZMod P) (A := ZMod P)
      (evalCode PrizeShapePrimeP30Second.g (2 ^ 30) (2 ^ 28 - 1))
      (ProximityGap.epsStar : ℝ≥0∞) ≤ (603979776 / 1073741824 : ℝ≥0) :=
  ceiling (m := 4) (r := 201326592) (e := 603979776)
    (by decide) (by decide) (by decide) (by decide) (by norm_num [tsub_mul, div_mul_cancel₀])
    (by rw [Nat.choose_two_right]; decide) (by decide)

/-- At rate one eighth the second-prime threshold is at most 704643072 errors. -/
theorem rateEighth_ceiling :
    mcaDeltaStar (F := ZMod P) (A := ZMod P)
      (evalCode PrizeShapePrimeP30Second.g (2 ^ 30) (2 ^ 27 - 1))
      (ProximityGap.epsStar : ℝ≥0∞) ≤ (704643072 / 1073741824 : ℝ≥0) :=
  ceiling (m := 4) (r := 234881024) (e := 704643072)
    (by decide) (by decide) (by decide) (by decide) (by norm_num [tsub_mul, div_mul_cancel₀])
    (by rw [Nat.choose_two_right]; decide) (by decide)

end ArkLib.ProximityGap.Frontier.SecondPrimeExceptionalCeilings

#print axioms ArkLib.ProximityGap.Frontier.SecondPrimeExceptionalCeilings.rateHalf_ceiling
#print axioms ArkLib.ProximityGap.Frontier.SecondPrimeExceptionalCeilings.rateQuarter_ceiling
#print axioms ArkLib.ProximityGap.Frontier.SecondPrimeExceptionalCeilings.rateEighth_ceiling
