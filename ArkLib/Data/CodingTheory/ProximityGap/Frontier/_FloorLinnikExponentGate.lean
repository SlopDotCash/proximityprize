/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Floor route sanity check: a Linnik exponent `5` is not a prize-scale bound

The #464 bad-prime-localization route reduces the off-BGK floor to two named inputs:

* `FloorLocalizationUniform`: floor-bad primes are exactly the least prime in the
  progression `1 mod 2^a`;
* `LinnikLeastPrimeBelowPrize`: that least prime is below prize scale `(2^a)^4`.

This file records the elementary exponent gate behind the second input. A classical
least-prime theorem of the shape `P(n) <= C n^5` does not, by itself, imply
`P(n) < n^4`; the exponent goes in the wrong direction. What the floor route actually
needs is an exponent strictly below `4` (or a theorem specialized to dyadic moduli),
which is why the later TZ bridge uses a `TZPrimeSupply` witness in a window
`[n^beta, 2 n^beta]` with `beta <= 3`.

No analytic number theory is proved here. These are just the arithmetic guardrails that
keep the route's proof obligations honest.
-/

namespace ArkLib.ProximityGap.Frontier.FloorLinnikExponentGate

/-- For every nontrivial dyadic modulus, prize scale `(2^a)^4` is strictly below the
`n^5` scale. Thus an `O(n^5)` least-prime bound is not a sub-prize-scale statement. -/
theorem dyadic_prize_scale_lt_fifth_power (a : ℕ) (ha : 1 ≤ a) :
    (2 ^ a) ^ 4 < (2 ^ a) ^ 5 := by
  have hbase : 1 < 2 ^ a := by
    calc
      (1 : ℕ) = 2 ^ 0 := by norm_num
      _ < 2 ^ a := Nat.pow_lt_pow_right (by norm_num) ha
  have hbasepos : 0 < 2 ^ a := by positivity
  have hpos : 0 < (2 ^ a) ^ 4 := by positivity
  have hmul : (2 ^ a) ^ 4 * 1 < (2 ^ a) ^ 4 * (2 ^ a) :=
    Nat.mul_lt_mul_of_pos_left hbase hpos
  simpa [pow_succ] using hmul

/-- The impossible comparison isolated: for `a >= 1`, `(2^a)^5 <= (2^a)^4` is false. -/
theorem not_fifth_power_le_prize_scale (a : ℕ) (ha : 1 ≤ a) :
    ¬ (2 ^ a) ^ 5 ≤ (2 ^ a) ^ 4 :=
  not_le_of_gt (dyadic_prize_scale_lt_fifth_power a ha)

/-- A window of size `2 * n^3` is below prize scale `n^4` once `n >= 2`.
This is the elementary inequality consumed by the Thorner-Zaman floor bridge. -/
theorem two_mul_cube_le_fourth {n : ℕ} (hn : 2 ≤ n) :
    2 * n ^ 3 ≤ n ^ 4 := by
  have h : 2 * n ^ 3 ≤ n * n ^ 3 := Nat.mul_le_mul_right (n ^ 3) hn
  have hpow : n * n ^ 3 = n ^ 4 := by ring
  simpa [hpow] using h

/-- Exponent `3` is safely sub-prize for dyadic moduli `2^a`, `a >= 1`. -/
theorem dyadic_two_mul_cube_le_prize_scale (a : ℕ) (ha : 1 ≤ a) :
    2 * (2 ^ a) ^ 3 ≤ (2 ^ a) ^ 4 := by
  have hn : 2 ≤ 2 ^ a := by
    calc
      (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  exact two_mul_cube_le_fourth hn

/-- Bundled verdict: a fifth-power least-prime theorem is above the prize scale, while a
`2 * n^3` supply witness is below it. -/
theorem exponent_gate_summary (a : ℕ) (ha : 1 ≤ a) :
    (2 ^ a) ^ 4 < (2 ^ a) ^ 5 ∧
      ¬ (2 ^ a) ^ 5 ≤ (2 ^ a) ^ 4 ∧
      2 * (2 ^ a) ^ 3 ≤ (2 ^ a) ^ 4 :=
  ⟨dyadic_prize_scale_lt_fifth_power a ha,
   not_fifth_power_le_prize_scale a ha,
   dyadic_two_mul_cube_le_prize_scale a ha⟩

end ArkLib.ProximityGap.Frontier.FloorLinnikExponentGate

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.FloorLinnikExponentGate.dyadic_prize_scale_lt_fifth_power
#print axioms ArkLib.ProximityGap.Frontier.FloorLinnikExponentGate.not_fifth_power_le_prize_scale
#print axioms ArkLib.ProximityGap.Frontier.FloorLinnikExponentGate.two_mul_cube_le_fourth
#print axioms ArkLib.ProximityGap.Frontier.FloorLinnikExponentGate.exponent_gate_summary
