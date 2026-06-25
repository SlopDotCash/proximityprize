/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Prime-supply depth gate for the off-BGK floor route

The floor-localization route is sometimes phrased not just at the base modulus `2^a`, but at
nearby deeper moduli `2^k`, `k >= a`: a floor-bad obstruction may be the least prime in one of the
progressions `1 mod 2^k`.

This file records the elementary scale gate.  A prime supplied at exponent `e` for level `k`
fits below the original prize scale `(2^a)^4` only when

`k * e <= 4 * a`.

Consequences:

* classical fifth-power Linnik scale cannot close any deeper-level route with `k >= a`;
* a cubic Thorner-Zaman-style supply at level `a + d` fits exactly while `3d <= a`;
* if `a < 3d`, even a cubic level-`a+d` supply overshoots the base prize scale.

No prime theorem is proved here.  These are the arithmetic guardrails for using any least-prime
input across multiple 2-power levels.
-/

namespace ArkLib.ProximityGap.Frontier.FloorLevelDepthPrimeScaleGate

/-- Power-of-two level/exponent comparison: a level-`k`, exponent-`e` supply fits below the
base prize scale at level `a` whenever `k * e <= a * 4`. -/
theorem dyadic_level_power_le_prize_of_mul_le {a k e : ℕ}
    (hscale : k * e <= a * 4) :
    (2 ^ k) ^ e <= (2 ^ a) ^ 4 := by
  rw [← pow_mul, ← pow_mul]
  exact Nat.pow_le_pow_right (by norm_num : 1 <= (2 : ℕ)) hscale

/-- If the level/exponent product is larger than the base prize exponent, the supplied scale is
strictly above prize scale. -/
theorem dyadic_prize_lt_level_power_of_mul_lt {a k e : ℕ}
    (hscale : a * 4 < k * e) :
    (2 ^ a) ^ 4 < (2 ^ k) ^ e := by
  rw [← pow_mul, ← pow_mul]
  exact Nat.pow_lt_pow_right (by norm_num : 1 < (2 : ℕ)) hscale

/-- Fifth-power least-prime scale is above the prize scale at every nontrivial deeper level
`k >= a`.  Thus an `O((2^k)^5)` theorem cannot close a base-level `(2^a)^4` prize window. -/
theorem fifth_power_deeper_level_above_prize
    {a k : ℕ} (ha : 1 <= a) (hak : a <= k) :
    (2 ^ a) ^ 4 < (2 ^ k) ^ 5 := by
  apply dyadic_prize_lt_level_power_of_mul_lt
  omega

/-- A cubic supply at level `a + d` fits below the base prize scale exactly in the shallow-depth
regime `3d <= a`. -/
theorem cubic_deeper_level_le_prize_of_depth
    {a d : ℕ} (hdepth : 3 * d <= a) :
    (2 ^ (a + d)) ^ 3 <= (2 ^ a) ^ 4 := by
  apply dyadic_level_power_le_prize_of_mul_le
  omega

/-- If the extra depth is too large (`a < 3d`), even a cubic supply at level `a + d` overshoots the
base prize scale. -/
theorem prize_lt_cubic_deeper_level_of_depth_too_large
    {a d : ℕ} (hdepth : a < 3 * d) :
    (2 ^ a) ^ 4 < (2 ^ (a + d)) ^ 3 := by
  apply dyadic_prize_lt_level_power_of_mul_lt
  omega

/-- Any cubic level-`a+d` prime witness lies below prize scale when `3d <= a`. -/
theorem cubic_level_witness_le_prize
    {a d q : ℕ}
    (hq : q <= (2 ^ (a + d)) ^ 3)
    (hdepth : 3 * d <= a) :
    q <= (2 ^ a) ^ 4 :=
  le_trans hq (cubic_deeper_level_le_prize_of_depth hdepth)

/-- Same-level cubic supply is always sub-prize. -/
theorem cubic_same_level_le_prize (a : ℕ) :
    (2 ^ a) ^ 3 <= (2 ^ a) ^ 4 := by
  apply dyadic_level_power_le_prize_of_mul_le
  omega

/-- Bundled verdict for a base level `a` and extra depth `d`: cubic supply works up to
`3d <= a`, too-deep cubic supply fails when `a < 3d`, and fifth-power supply fails for every
deeper nontrivial level. -/
theorem level_depth_prime_scale_summary
    {a d : ℕ} (ha : 1 <= a) :
    (3 * d <= a -> (2 ^ (a + d)) ^ 3 <= (2 ^ a) ^ 4)
      ∧ (a < 3 * d -> (2 ^ a) ^ 4 < (2 ^ (a + d)) ^ 3)
      ∧ (2 ^ a) ^ 4 < (2 ^ (a + d)) ^ 5 := by
  refine ⟨fun hdepth => cubic_deeper_level_le_prize_of_depth hdepth,
    fun hdepth => prize_lt_cubic_deeper_level_of_depth_too_large hdepth,
    ?_⟩
  exact fifth_power_deeper_level_above_prize ha (by omega)

#print axioms dyadic_level_power_le_prize_of_mul_le
#print axioms dyadic_prize_lt_level_power_of_mul_lt
#print axioms fifth_power_deeper_level_above_prize
#print axioms cubic_deeper_level_le_prize_of_depth
#print axioms prize_lt_cubic_deeper_level_of_depth_too_large
#print axioms cubic_level_witness_le_prize
#print axioms cubic_same_level_le_prize
#print axioms level_depth_prime_scale_summary

end ArkLib.ProximityGap.Frontier.FloorLevelDepthPrimeScaleGate
