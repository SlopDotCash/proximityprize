/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mikhail Izhutkin (mashingaan, @mashingaan)
-/
import Research.ProximityPrize.Frontier._PrizeShapePrimeP30
import Research.ProximityPrize.Frontier._PrizeShapePrimeP30Second

/-!
# BCHKS subgroup-scale mismatch at the sponsor fields

The BCHKS25 subgroup-sumset interface requires a subgroup of cardinality
`b ≤ 10 · log₂ q`.  The exact sponsor Reed–Solomon instance instead uses the
smooth multiplicative subgroup of order `n = 2^30`.  Both certified sponsor
fields are below `2^160`, so their BCHKS25 logarithmic scale is below `1600`.
Consequently the BCHKS25 admissibility interface cannot be instantiated with
the sponsor subgroup itself.  This is a parameter mismatch for that interface,
not a refutation of the sponsor incidence statement.
-/

namespace ArkLib.ProximityGap.Frontier.BchksSponsorLogScaleNoGo

abbrev sponsorN : ℕ := 2 ^ 30

theorem first_field_log_lt_159 :
    Nat.log 2 ArkLib.ProximityGap.PrizeShapePrimeP30.P < 159 := by
  apply Nat.log_lt_of_lt_pow'
  · norm_num
  · norm_num [ArkLib.ProximityGap.PrizeShapePrimeP30.P]

theorem second_field_log_lt_160 :
    Nat.log 2 ArkLib.ProximityGap.PrizeShapePrimeP30Second.P < 160 := by
  apply Nat.log_lt_of_lt_pow'
  · norm_num
  · norm_num [ArkLib.ProximityGap.PrizeShapePrimeP30Second.P]

theorem first_sponsor_order_exceeds_bchks_log_scale :
    ¬ sponsorN ≤
      10 * Nat.log 2 ArkLib.ProximityGap.PrizeShapePrimeP30.P := by
  have hlog := first_field_log_lt_159
  have hscale :
      10 * Nat.log 2 ArkLib.ProximityGap.PrizeShapePrimeP30.P ≤ 1580 := by
    omega
  have hsponsor : 1580 < sponsorN := by
    norm_num [sponsorN]
  omega

theorem second_sponsor_order_exceeds_bchks_log_scale :
    ¬ sponsorN ≤
      10 * Nat.log 2 ArkLib.ProximityGap.PrizeShapePrimeP30Second.P := by
  have hlog := second_field_log_lt_160
  have hscale :
      10 * Nat.log 2 ArkLib.ProximityGap.PrizeShapePrimeP30Second.P ≤ 1590 := by
    omega
  have hsponsor : 1590 < sponsorN := by
    norm_num [sponsorN]
  omega

theorem first_bchks_scale_is_strictly_below_sponsor_order
    {b : ℕ}
    (hb : b ≤ 10 * Nat.log 2 ArkLib.ProximityGap.PrizeShapePrimeP30.P) :
    b < sponsorN := by
  have hlog := first_field_log_lt_159
  norm_num [sponsorN]
  omega

theorem second_bchks_scale_is_strictly_below_sponsor_order
    {b : ℕ}
    (hb : b ≤ 10 * Nat.log 2 ArkLib.ProximityGap.PrizeShapePrimeP30Second.P) :
    b < sponsorN := by
  have hlog := second_field_log_lt_160
  norm_num [sponsorN]
  omega

end ArkLib.ProximityGap.Frontier.BchksSponsorLogScaleNoGo

#print axioms ArkLib.ProximityGap.Frontier.BchksSponsorLogScaleNoGo.first_sponsor_order_exceeds_bchks_log_scale
#print axioms ArkLib.ProximityGap.Frontier.BchksSponsorLogScaleNoGo.second_sponsor_order_exceeds_bchks_log_scale
#print axioms ArkLib.ProximityGap.Frontier.BchksSponsorLogScaleNoGo.first_bchks_scale_is_strictly_below_sponsor_order
#print axioms ArkLib.ProximityGap.Frontier.BchksSponsorLogScaleNoGo.second_bchks_scale_is_strictly_below_sponsor_order
