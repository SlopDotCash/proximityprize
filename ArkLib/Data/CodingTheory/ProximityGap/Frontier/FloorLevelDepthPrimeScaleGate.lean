/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic.Linarith

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

set_option autoImplicit false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.FloorLevelDepthPrimeScaleGate

/-- Power-of-two level/exponent comparison: a level-`k`, exponent-`e` supply fits below the
base prize scale at level `a` whenever `k * e <= a * 4`. -/
theorem dyadic_level_power_le_prize_of_mul_le {a k e : ℕ}
    (hscale : k * e <= a * 4) :
    (2 ^ k) ^ e <= (2 ^ a) ^ 4 := by
  rw [← pow_mul, ← pow_mul]
  exact Nat.pow_le_pow_right (by decide : 1 <= (2 : ℕ)) hscale

/-- If the level/exponent product is larger than the base prize exponent, the supplied scale is
strictly above prize scale. -/
theorem dyadic_prize_lt_level_power_of_mul_lt {a k e : ℕ}
    (hscale : a * 4 < k * e) :
    (2 ^ a) ^ 4 < (2 ^ k) ^ e := by
  rw [← pow_mul, ← pow_mul]
  exact Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) hscale

/-- Exact scale gate: a level-`k`, exponent-`e` supply fits below the base prize scale if and only
if the exponent product fits below `4a`. -/
theorem dyadic_level_power_le_prize_iff_mul_le {a k e : ℕ} :
    (2 ^ k) ^ e <= (2 ^ a) ^ 4 ↔ k * e <= a * 4 := by
  constructor
  · intro hle
    by_contra hnot
    have hlt : a * 4 < k * e := Nat.lt_of_not_ge hnot
    exact (not_lt_of_ge hle) (dyadic_prize_lt_level_power_of_mul_lt hlt)
  · exact dyadic_level_power_le_prize_of_mul_le

/-- Strict exact scale gate: the level-`k`, exponent-`e` scale overshoots the prize scale if and
only if its exponent product is larger than `4a`. -/
theorem dyadic_prize_lt_level_power_iff_mul_lt {a k e : ℕ} :
    (2 ^ a) ^ 4 < (2 ^ k) ^ e ↔ a * 4 < k * e := by
  constructor
  · intro hlt
    by_contra hnot
    have hle : k * e <= a * 4 := le_of_not_gt hnot
    exact (not_lt_of_ge (dyadic_level_power_le_prize_of_mul_le hle)) hlt
  · exact dyadic_prize_lt_level_power_of_mul_lt

/-- Any level-`k`, exponent-`e` witness lies below prize scale when the exponent-product gate
holds. -/
theorem level_witness_le_prize_of_mul_le
    {a k e q : ℕ}
    (hq : q <= (2 ^ k) ^ e)
    (hscale : k * e <= a * 4) :
    q <= (2 ^ a) ^ 4 :=
  le_trans hq (dyadic_level_power_le_prize_of_mul_le hscale)

/-- If a supplied level/exponent witness is above the base prize scale, then the
level/exponent product gate has failed. -/
theorem mul_lt_of_prize_lt_level_witness
    {a k e q : ℕ}
    (hq : q <= (2 ^ k) ^ e)
    (hprize : (2 ^ a) ^ 4 < q) :
    a * 4 < k * e := by
  by_contra hnot
  have hscale : k * e <= a * 4 := le_of_not_gt hnot
  exact (not_lt_of_ge (level_witness_le_prize_of_mul_le hq hscale)) hprize

/-- Under the exponent-product gate, no level/exponent witness below the supplied scale can sit
above the base prize scale. -/
theorem not_prize_lt_level_witness_of_mul_le
    {a k e q : ℕ}
    (hq : q <= (2 ^ k) ^ e)
    (hscale : k * e <= a * 4) :
    ¬ (2 ^ a) ^ 4 < q := by
  intro hprize
  exact (not_lt_of_ge (level_witness_le_prize_of_mul_le hq hscale)) hprize

/-- Fifth-power least-prime scale is above the prize scale at every nontrivial deeper level
`k >= a`.  Thus an `O((2^k)^5)` theorem cannot close a base-level `(2^a)^4` prize window. -/
theorem fifth_power_deeper_level_above_prize
    {a k : ℕ} (ha : 1 <= a) (hak : a <= k) :
    (2 ^ a) ^ 4 < (2 ^ k) ^ 5 := by
  apply dyadic_prize_lt_level_power_of_mul_lt
  nlinarith

/-- A cubic supply at level `a + d` fits below the base prize scale exactly in the shallow-depth
regime `3d <= a`. -/
theorem cubic_deeper_level_le_prize_of_depth
    {a d : ℕ} (hdepth : 3 * d <= a) :
    (2 ^ (a + d)) ^ 3 <= (2 ^ a) ^ 4 := by
  apply dyadic_level_power_le_prize_of_mul_le
  nlinarith

/-- Exact cubic depth gate: cubic supply at level `a+d` fits below base prize scale exactly when
the extra depth satisfies `3d <= a`. -/
theorem cubic_deeper_level_le_prize_iff_depth {a d : ℕ} :
    (2 ^ (a + d)) ^ 3 <= (2 ^ a) ^ 4 ↔ 3 * d <= a := by
  rw [dyadic_level_power_le_prize_iff_mul_le]
  constructor <;> intro h <;> nlinarith

/-- If the extra depth is too large (`a < 3d`), even a cubic supply at level `a + d` overshoots the
base prize scale. -/
theorem prize_lt_cubic_deeper_level_of_depth_too_large
    {a d : ℕ} (hdepth : a < 3 * d) :
    (2 ^ a) ^ 4 < (2 ^ (a + d)) ^ 3 := by
  apply dyadic_prize_lt_level_power_of_mul_lt
  nlinarith

/-- Strict exact cubic depth gate: cubic supply overshoots base prize scale exactly when
`a < 3d`. -/
theorem prize_lt_cubic_deeper_level_iff_depth_too_large {a d : ℕ} :
    (2 ^ a) ^ 4 < (2 ^ (a + d)) ^ 3 ↔ a < 3 * d := by
  rw [dyadic_prize_lt_level_power_iff_mul_lt]
  constructor <;> intro h <;> nlinarith

/-- Any cubic level-`a+d` prime witness lies below prize scale when `3d <= a`. -/
theorem cubic_level_witness_le_prize
    {a d q : ℕ}
    (hq : q <= (2 ^ (a + d)) ^ 3)
    (hdepth : 3 * d <= a) :
    q <= (2 ^ a) ^ 4 :=
  level_witness_le_prize_of_mul_le hq (by nlinarith)

/-- If a cubic level-`a+d` witness is above base prize scale, then the depth is too large. -/
theorem depth_too_large_of_prize_lt_cubic_level_witness
    {a d q : ℕ}
    (hq : q <= (2 ^ (a + d)) ^ 3)
    (hprize : (2 ^ a) ^ 4 < q) :
    a < 3 * d := by
  have hmul : a * 4 < (a + d) * 3 :=
    mul_lt_of_prize_lt_level_witness hq hprize
  nlinarith

/-- In the allowed cubic-depth range, no cubic level witness can exceed base prize scale. -/
theorem not_prize_lt_cubic_level_witness_of_depth
    {a d q : ℕ}
    (hq : q <= (2 ^ (a + d)) ^ 3)
    (hdepth : 3 * d <= a) :
    ¬ (2 ^ a) ^ 4 < q :=
  not_prize_lt_level_witness_of_mul_le hq (by nlinarith)

/-- Same-level cubic supply is always sub-prize. -/
theorem cubic_same_level_le_prize (a : ℕ) :
    (2 ^ a) ^ 3 <= (2 ^ a) ^ 4 := by
  apply dyadic_level_power_le_prize_of_mul_le
  nlinarith

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
  exact fifth_power_deeper_level_above_prize ha (Nat.le_add_right a d)

#print axioms dyadic_level_power_le_prize_of_mul_le
#print axioms dyadic_prize_lt_level_power_of_mul_lt
#print axioms dyadic_level_power_le_prize_iff_mul_le
#print axioms dyadic_prize_lt_level_power_iff_mul_lt
#print axioms level_witness_le_prize_of_mul_le
#print axioms mul_lt_of_prize_lt_level_witness
#print axioms not_prize_lt_level_witness_of_mul_le
#print axioms fifth_power_deeper_level_above_prize
#print axioms cubic_deeper_level_le_prize_of_depth
#print axioms cubic_deeper_level_le_prize_iff_depth
#print axioms prize_lt_cubic_deeper_level_of_depth_too_large
#print axioms prize_lt_cubic_deeper_level_iff_depth_too_large
#print axioms cubic_level_witness_le_prize
#print axioms depth_too_large_of_prize_lt_cubic_level_witness
#print axioms not_prize_lt_cubic_level_witness_of_depth
#print axioms cubic_same_level_le_prize
#print axioms level_depth_prime_scale_summary

end ArkLib.ProximityGap.Frontier.FloorLevelDepthPrimeScaleGate
