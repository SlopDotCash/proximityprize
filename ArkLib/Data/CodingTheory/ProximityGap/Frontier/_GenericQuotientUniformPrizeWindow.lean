/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._GenericQuotientInterpolationSpread
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SecondMomentUniformFieldWindow

/-!
# Uniform prize-field consumer for generic quotient interpolation spread

This file combines the arbitrary quotient-word second-moment construction with the
integer field-window arithmetic at security parameter `2^-128`.

If `2^128 <= p < 2^256`, `g` has order `s*m`, and the exact-rate quotient family has
at least `2^128+2` members, then the rounded choice

`M = p / 2^128 + 3`

makes the second-moment lower bound strictly exceed the prize error.  Consequently the
operational threshold is at most the bad radius `1-r/s`.  This is only a bad-side ceiling:
it gives neither a matching good radius nor an equality for `mcaDeltaStar`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped NNReal ENNReal
open ProximityGap

namespace ArkLib.ProximityGap.Frontier.GenericQuotientUniformPrizeWindow

open ArkLib.ProximityGap.KKH26
open ArkLib.ProximityGap.Frontier.GenericQuotientInterpolationSpread
open ArkLib.ProximityGap.Frontier.SecondMomentUniformFieldWindow

variable {p s m r : Nat} [Fact p.Prime] [NeZero s] [NeZero m]

/-- **Strict prize-error crossing in the full field window.**  The family-size hypothesis is
uniform in `p`; the rounded subfamily size is selected internally. -/
theorem epsStar_lt_epsMCA_of_uniform_quotient_supply
    (hpLo : 2 ^ 128 <= p) (hpHi : p < 2 ^ 256)
    (hs : 1 <= s) (hm : 1 <= m) (hr2 : 2 <= r) (hr : r <= s)
    {g : ZMod p} (hg : orderOf g = s * m)
    (hSupply : 2 ^ 128 + 2 <= Nat.choose s r) :
    (ProximityGap.epsStar : ENNReal) <
      epsMCA (F := ZMod p) (KKH26.evalCode g (s * m) ((r - 1) * m - 1))
        (1 - (r : NNReal) / (s : NNReal)) := by
  let M : Nat := p / 2 ^ 128 + 3
  have hMWindow : M <= 2 ^ 128 + 2 := by
    simpa only [M] using prize_rounded_family_le hpHi
  have hMChoose : M <= Nat.choose s r := hMWindow.trans hSupply
  have hMle : M * M <= M * p := by
    simpa only [M, pow_two] using
      (rounded_family_sq_le_mul_field (Q := 2 ^ 128) (p := p) (by norm_num) hpLo)
  have hNum : p * p < 2 ^ 128 * (M * p - M * M) := by
    simpa only [M, pow_two] using prize_field_sq_lt_secondMoment_numerator hpLo hpHi
  have hStrict : (ProximityGap.epsStar : ENNReal) <
      (((M : ENNReal) - (M * M : ENNReal) / (p : ENNReal)) / (p : ENNReal)) :=
    ProximityGap.epsStar_lt_second_moment_value (by omega) hMle hNum
  exact hStrict.trans_le
    (genericQuotient_epsMCA_lower_bound_secondMoment hs hm hr2 hr hg M hMChoose)

/-- **Operational bad-side ceiling.**  Under uniform quotient supply throughout
`2^128 <= p < 2^256`, the operational MCA threshold is at most `1-r/s`. -/
theorem mcaDeltaStar_le_of_uniform_quotient_supply
    (hpLo : 2 ^ 128 <= p) (hpHi : p < 2 ^ 256)
    (hs : 1 <= s) (hm : 1 <= m) (hr2 : 2 <= r) (hr : r <= s)
    {g : ZMod p} (hg : orderOf g = s * m)
    (hSupply : 2 ^ 128 + 2 <= Nat.choose s r) :
    ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p)
        (KKH26.evalCode g (s * m) ((r - 1) * m - 1))
        (ProximityGap.epsStar : ENNReal) <=
      1 - (r : NNReal) / (s : NNReal) :=
  ProximityGap.MCAThresholdLedger.mcaDeltaStar_le_of_bad _ _
    (epsStar_lt_epsMCA_of_uniform_quotient_supply
      hpLo hpHi hs hm hr2 hr hg hSupply)

/-! ## Four exact-rate deployed rungs

The code dimensions are respectively `128m`, `64m`, `32m`, and `32m` on domains
`256m`, `256m`, `256m`, and `512m`.  Thus their rates are exactly
`1/2`, `1/4`, `1/8`, and `1/16`; the conclusions remain bad-side ceilings only. -/

/-- Exact rate `1/2`: operational threshold at most `127/256`. -/
theorem rateHalf_s256_mcaDeltaStar_le
    {p m : Nat} [Fact p.Prime] [NeZero m]
    (hpLo : 2 ^ 128 <= p) (hpHi : p < 2 ^ 256)
    (hm : 1 <= m) {g : ZMod p} (hg : orderOf g = 256 * m) :
    ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p)
        (KKH26.evalCode g (256 * m) (128 * m - 1))
        (ProximityGap.epsStar : ENNReal) <= (127 : NNReal) / 256 := by
  have h := mcaDeltaStar_le_of_uniform_quotient_supply
    (p := p) (s := 256) (m := m) (r := 129)
    hpLo hpHi (by norm_num) hm (by norm_num) (by norm_num) hg rateHalf_s256_supply
  convert h using 1 <;> norm_num

/-- Exact rate `1/4`: operational threshold at most `191/256`. -/
theorem rateQuarter_s256_mcaDeltaStar_le
    {p m : Nat} [Fact p.Prime] [NeZero m]
    (hpLo : 2 ^ 128 <= p) (hpHi : p < 2 ^ 256)
    (hm : 1 <= m) {g : ZMod p} (hg : orderOf g = 256 * m) :
    ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p)
        (KKH26.evalCode g (256 * m) (64 * m - 1))
        (ProximityGap.epsStar : ENNReal) <= (191 : NNReal) / 256 := by
  have h := mcaDeltaStar_le_of_uniform_quotient_supply
    (p := p) (s := 256) (m := m) (r := 65)
    hpLo hpHi (by norm_num) hm (by norm_num) (by norm_num) hg rateQuarter_s256_supply
  convert h using 1 <;> norm_num

/-- Exact rate `1/8`: operational threshold at most `223/256`. -/
theorem rateEighth_s256_mcaDeltaStar_le
    {p m : Nat} [Fact p.Prime] [NeZero m]
    (hpLo : 2 ^ 128 <= p) (hpHi : p < 2 ^ 256)
    (hm : 1 <= m) {g : ZMod p} (hg : orderOf g = 256 * m) :
    ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p)
        (KKH26.evalCode g (256 * m) (32 * m - 1))
        (ProximityGap.epsStar : ENNReal) <= (223 : NNReal) / 256 := by
  have h := mcaDeltaStar_le_of_uniform_quotient_supply
    (p := p) (s := 256) (m := m) (r := 33)
    hpLo hpHi (by norm_num) hm (by norm_num) (by norm_num) hg rateEighth_s256_supply
  convert h using 1 <;> norm_num

/-- Exact rate `1/16`: operational threshold at most `479/512`. -/
theorem rateSixteenth_s512_mcaDeltaStar_le
    {p m : Nat} [Fact p.Prime] [NeZero m]
    (hpLo : 2 ^ 128 <= p) (hpHi : p < 2 ^ 256)
    (hm : 1 <= m) {g : ZMod p} (hg : orderOf g = 512 * m) :
    ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p)
        (KKH26.evalCode g (512 * m) (32 * m - 1))
        (ProximityGap.epsStar : ENNReal) <= (479 : NNReal) / 512 := by
  have h := mcaDeltaStar_le_of_uniform_quotient_supply
    (p := p) (s := 512) (m := m) (r := 33)
    hpLo hpHi (by norm_num) hm (by norm_num) (by norm_num) hg rateSixteenth_s512_supply
  convert h using 1 <;> norm_num

end ArkLib.ProximityGap.Frontier.GenericQuotientUniformPrizeWindow

#print axioms ArkLib.ProximityGap.Frontier.GenericQuotientUniformPrizeWindow.epsStar_lt_epsMCA_of_uniform_quotient_supply
#print axioms ArkLib.ProximityGap.Frontier.GenericQuotientUniformPrizeWindow.mcaDeltaStar_le_of_uniform_quotient_supply
#print axioms ArkLib.ProximityGap.Frontier.GenericQuotientUniformPrizeWindow.rateHalf_s256_mcaDeltaStar_le
#print axioms ArkLib.ProximityGap.Frontier.GenericQuotientUniformPrizeWindow.rateQuarter_s256_mcaDeltaStar_le
#print axioms ArkLib.ProximityGap.Frontier.GenericQuotientUniformPrizeWindow.rateEighth_s256_mcaDeltaStar_le
#print axioms ArkLib.ProximityGap.Frontier.GenericQuotientUniformPrizeWindow.rateSixteenth_s512_mcaDeltaStar_le
