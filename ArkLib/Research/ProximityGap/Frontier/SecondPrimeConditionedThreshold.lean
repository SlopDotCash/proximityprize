/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeConditionedIncidence
import ArkLib.Research.ProximityGap.Frontier._ThreeCoreSecondPrimeBracket

/-! # Second-prime MCA floor from conditioned cubic incidences -/

open ProximityGap ProximityGap.MCAThresholdLedger ArkLib.ProximityGap.KKH26
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.PrizeShapePrimeP30Second
open ArkLib.ProximityGap.Frontier.PrizeShapeRateHalfBracket
open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.Frontier.SecondPrimeConditionedThreshold

set_option maxRecDepth 4096

local instance : Fact P.Prime := ⟨prime_P⟩

private theorem predecessor_good {p k e : ℕ} [Fact p.Prime] {g : ZMod p}
    (hg : orderOf g = TwoCorePackingThreshold.domainLength) (hk : 1 ≤ k) (hkm : k ≤ 67108864)
    (he : e ≤ TwoCorePackingThreshold.domainLength)
    (ht : TwoCorePackingThreshold.domainLength - e = 426114723) :
    epsMCA (F := ZMod p) (A := ZMod p) (evalCode g TwoCorePackingThreshold.domainLength (k-1))
       ((e : ℝ≥0) / (TwoCorePackingThreshold.domainLength : ℝ≥0)) ≤
         ((2147483648 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) := by
  let n := TwoCorePackingThreshold.domainLength
  let δ : ℝ≥0 := (e : ℝ≥0) / (n : ℝ≥0)
  have hg0 := KKH26RegimeSplit.ne_zero_of_orderOf_eq hg
  let dom := KKH26RegimeSplit.powDomain g hg hg0
  have hcode : evalCode g n (k - 1) =
      (ReedSolomon.code dom k : Set (Fin n → ZMod p)) := by
    simpa only [dom, show k - 1 + 1 = k by omega] using
      KKH26RegimeSplit.evalCode_eq_reedSolomon g hg hg0 (k - 1)
  rw [hcode]
  refine (epsMCA_le_of_badCount_le _ _ 2147483648 ?_).trans (by rw [ZMod.card])
  intro u
  have hf := SecondPrimeConditionedIncidence.family_card_le
    (canonicalBadScalarRichPointFamily dom (k := k) δ u hk)
    (Fintype.card_fin _) hk hkm ((TwoCorePackingThreshold.agreement_ceiling e he).trans ht)
  simpa only [canonicalBadScalarRichPointFamily, badScalars, δ] using hf

/-- At one sixteenth rate, a good predecessor and the three-head attack give this bracket. -/
theorem secondPrime_rateSixteenth_bracket :
    let δ := mcaDeltaStar (F := ZMod P) (A := ZMod P)
      (evalCode PrizeShapePrimeP30Second.g (2 ^ 30) (2 ^ 26 - 1)) (ProximityGap.epsStar : ℝ≥0∞)
    (647627102 / 1073741824 : ℝ≥0) ≤ δ ∧ δ ≤ (715827882 / 1073741824 : ℝ≥0) := by
  refine ⟨?_, ThreeCoreSecondPrimeBracket.secondPrime_ceiling (by decide) (by decide)⟩
  let n := TwoCorePackingThreshold.domainLength
  let e := 647627101
  let k := 67108864
  let g := PrizeShapePrimeP30Second.g
  change ((e+1 : ℕ) : ℝ≥0) / (n : ℝ≥0) ≤
    mcaDeltaStar (F := ZMod P) (A := ZMod P) (evalCode g n (k-1)) (ProximityGap.epsStar : ℝ≥0∞)
  rw [PrizeShapeRateHalfBracket.epsStar_coe_eq_natCast_inv]
  apply latticeBoundary_le_mcaDeltaStar_of_predecessor_good (by decide) (by decide)
  simp only [predecessorRadius, Nat.add_sub_cancel]
  have hgood := predecessor_good (e := e) (k := k) orderOf_g (by decide) (by decide) (by decide) (by decide)
  exact hgood.trans (natCast_div_le_inv_of_mul_le (E := 2147483648) (by norm_num) prime_P.pos (by decide))

#print axioms secondPrime_rateSixteenth_bracket

end ArkLib.ProximityGap.Frontier.SecondPrimeConditionedThreshold
