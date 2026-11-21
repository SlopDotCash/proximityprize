/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.ExceptionalHeadLocatorMass
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeManyHeadCeilings

/-! # Exceptional-site locator ceilings on the second production prime -/

open ProximityGap ProximityGap.MCAThresholdLedger ArkLib.ProximityGap.KKH26
open ArkLib.ProximityGap.PrizeShapePrimeP30Second
open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.Frontier.SecondPrimeExceptionalHeadCeilings

local instance : Fact P.Prime := ⟨prime_P⟩

private theorem ceiling {k e m : ℕ}
    (hm : 0 < m) (hk : m ≤ k) (ht : k < 2^30-e)
    (hlayout : m*(2^30-e-k) ≤ 2^30-k)
    (hsize : (1-(e:ℝ≥0)/1073741824)*1073741824 ≤ ((2^30-e:ℕ):ℝ≥0))
    (hbudget : P/2^128 < m*(2^30-(2^30-e)+1)) :
    mcaDeltaStar (F:=ZMod P) (A:=ZMod P) (evalCode PrizeShapePrimeP30Second.g (2^30) (k-1))
      (ProximityGap.epsStar : ℝ≥0∞) ≤ (e:ℝ≥0)/1073741824 := by
  have hg0 := KKH26RegimeSplit.ne_zero_of_orderOf_eq orderOf_g
  let dom := KKH26RegimeSplit.powDomain PrizeShapePrimeP30Second.g orderOf_g hg0
  have bad := ExceptionalHeadLocatorMass.over_budget_128 dom ((e:ℝ≥0)/1073741824)
    hm hk ht (Nat.sub_le ..) hlayout (by norm_num at hsize ⊢; exact hsize)
    (by rw [ZMod.card]; decide) (by simpa only [ZMod.card] using hbudget)
  have eq : evalCode PrizeShapePrimeP30Second.g (2^30) (k-1) =
      (ReedSolomon.code dom k : Set (Fin (2^30) → ZMod P)) := by
    simpa only [dom,show k-1+1=k by omega] using
      KKH26RegimeSplit.evalCode_eq_reedSolomon PrizeShapePrimeP30Second.g orderOf_g hg0 (k-1)
  apply mcaDeltaStar_le_of_bad
  rw [eq,PrizeShapeRateHalfBracket.epsStar_coe_eq_natCast_inv]
  simpa only [one_div,Nat.cast_pow,Nat.cast_ofNat] using bad

/-- Five heads exceed budget at 429496730 errors on the second prime. -/
theorem rateHalf_ceiling :
    mcaDeltaStar (F:=ZMod P) (A:=ZMod P) (evalCode PrizeShapePrimeP30Second.g (2^30) (2^29-1))
      (ProximityGap.epsStar : ℝ≥0∞) ≤ (429496730/1073741824 : ℝ≥0) :=
  ceiling (m:=5) (e:=429496730) (by decide) (by decide) (by decide) (by decide)
    (by norm_num [tsub_mul,div_mul_cancel₀]) (by decide)

/-- Four heads exceed budget at 603979776 errors on the second prime. -/
theorem rateQuarter_ceiling :
    mcaDeltaStar (F:=ZMod P) (A:=ZMod P) (evalCode PrizeShapePrimeP30Second.g (2^30) (2^28-1))
      (ProximityGap.epsStar : ℝ≥0∞) ≤ (603979776/1073741824 : ℝ≥0) :=
  ceiling (m:=4) (e:=603979776) (by decide) (by decide) (by decide) (by decide)
    (by norm_num [tsub_mul,div_mul_cancel₀]) (by decide)

/-- Four heads exceed budget at 704643072 errors on the second prime. -/
theorem rateEighth_ceiling :
    mcaDeltaStar (F:=ZMod P) (A:=ZMod P) (evalCode PrizeShapePrimeP30Second.g (2^30) (2^27-1))
      (ProximityGap.epsStar : ℝ≥0∞) ≤ (704643072/1073741824 : ℝ≥0) :=
  ceiling (m:=4) (e:=704643072) (by decide) (by decide) (by decide) (by decide)
    (by norm_num [tsub_mul,div_mul_cancel₀]) (by decide)

#print axioms rateHalf_ceiling
#print axioms rateQuarter_ceiling
#print axioms rateEighth_ceiling

end ArkLib.ProximityGap.Frontier.SecondPrimeExceptionalHeadCeilings
