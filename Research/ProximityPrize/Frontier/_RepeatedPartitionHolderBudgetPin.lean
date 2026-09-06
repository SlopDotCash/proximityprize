/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Production Hölder budget pin for the depth-seven repeated equality partitions

Möbius inversion over equality partitions of two ordered seven-tuples groups the
`full - injective` terms by their total number `k` of blocks.  The absolute coefficient masses
are recorded below.  Their sum is `(7!)^2 - 1`; the missing unit is the cancelled
singleton/singleton term.

At the production target, the depth-seven Wick constant and wraparound allowance satisfy

`135135 + 127009 = 262144 = 2^18`.

Generalized Hölder applied to the corresponding `k`-factor weighted period moments gives a
normalized repeated-sector envelope strictly below `138`.  The tight term is the `k=13` mass
`42`; the `k=12` mass is `791`, and every lower stratum is negligible at `n=2^30`.  This file
certifies the finite coefficient and rational arithmetic and isolates the exact bootstrap algebra:
an injective allocation `126871` plus the repeated Hölder tangent forces the desired total
allocation `127009`.

This is an arithmetic/interface pin.  The analytic consumer must separately prove that its
repeated-sector defect satisfies the stated tangent inequality.

Issue #466.
-/

set_option autoImplicit false

open Finset

namespace ArkLib.ProximityGap.Frontier.RepeatedPartitionHolderBudgetPin

open scoped BigOperators

/-- Absolute repeated Möbius coefficient mass grouped by total block count. -/
def repeatedMobiusMass : ℕ → ℕ
  | 2 => 518400
  | 3 => 2540160
  | 4 => 5450256
  | 5 => 6787872
  | 6 => 5482456
  | 7 => 3034920
  | 8 => 1184153
  | 9 => 328986
  | 10 => 64743
  | 11 => 8820
  | 12 => 791
  | 13 => 42
  | _ => 0

theorem repeatedMobiusMass_table :
    repeatedMobiusMass 2 = 518400 ∧
    repeatedMobiusMass 3 = 2540160 ∧
    repeatedMobiusMass 4 = 5450256 ∧
    repeatedMobiusMass 5 = 6787872 ∧
    repeatedMobiusMass 6 = 5482456 ∧
    repeatedMobiusMass 7 = 3034920 ∧
    repeatedMobiusMass 8 = 1184153 ∧
    repeatedMobiusMass 9 = 328986 ∧
    repeatedMobiusMass 10 = 64743 ∧
    repeatedMobiusMass 11 = 8820 ∧
    repeatedMobiusMass 12 = 791 ∧
    repeatedMobiusMass 13 = 42 := by
  norm_num [repeatedMobiusMass]

/-- Total absolute coefficient mass: `(7!)^2 - 1`. -/
theorem repeatedMobiusMass_total :
    ∑ k ∈ Finset.Icc 2 13, repeatedMobiusMass k = 25401599 := by
  norm_num [Finset.sum_Icc_succ_top, repeatedMobiusMass]

/-- All terms with at most eleven weighted factors have combined coefficient mass below `2^25`. -/
theorem repeatedMobiusMass_two_through_eleven :
    (∑ k ∈ Finset.Icc 2 11, repeatedMobiusMass k) = 25400766 ∧
      25400766 < 2 ^ 25 := by
  norm_num [Finset.sum_Icc_succ_top, repeatedMobiusMass]

/-- Seventh-power certificate for `2^(12/7) < 1641/500`, used on the leading `k=13` term. -/
theorem leading_root_seventhPower_certificate :
    2 ^ 12 * 500 ^ 7 < (1641 : ℕ) ^ 7 := by
  norm_num

/-- Rational upper ledger: the `k=13` term, `k=12` term, and all `k ≤ 11` terms total less
than `138`. -/
theorem repeated_holder_rational_majorant_lt_138 :
    (42 : ℚ) * (1641 / 500) + 791 / 2 ^ 14 + 1 / 32 < 138 := by
  norm_num

/-- Wick plus target wraparound constants exactly fill the binary moment envelope. -/
theorem production_fullMoment_constant :
    Nat.doubleFactorial 13 + 127009 = 2 ^ 18 := by
  norm_num [Nat.doubleFactorial]

/-- Conservative repeated allocation and the resulting injective allocation. -/
theorem production_budget_split :
    126871 + 138 = 127009 := by
  norm_num

/-- The concave Hölder envelope's tangent slope is below `1/1024` at the target point. -/
theorem production_tangent_slope_certificate :
    (13 / 14 : ℚ) * 138 / 2 ^ 18 < 1 / 1024 := by
  norm_num

/-- Normalized bootstrap: the injective allocation and repeated tangent force the target. -/
theorem normalized_holder_bootstrap
    {total injective repeated : ℝ}
    (hinjective : injective ≤ 126871)
    (hsplit : total ≤ injective + repeated)
    (hrepeated : repeated ≤ 138 + (total - 127009) / 1024) :
    total ≤ 127009 := by
  linarith

/-- Unnormalized bootstrap, with `scale` intended to be `q*n^7`. -/
theorem production_holder_bootstrap
    {total injective repeated scale : ℝ}
    (hinjective : injective ≤ 126871 * scale)
    (hsplit : total ≤ injective + repeated)
    (hrepeated :
      repeated ≤ 138 * scale + (total - 127009 * scale) / 1024) :
    total ≤ 127009 * scale := by
  linarith

#print axioms repeatedMobiusMass_total
#print axioms repeatedMobiusMass_two_through_eleven
#print axioms leading_root_seventhPower_certificate
#print axioms repeated_holder_rational_majorant_lt_138
#print axioms production_fullMoment_constant
#print axioms production_tangent_slope_certificate
#print axioms normalized_holder_bootstrap
#print axioms production_holder_bootstrap

end ArkLib.ProximityGap.Frontier.RepeatedPartitionHolderBudgetPin
