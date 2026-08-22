/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#464)
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# The exponent gate behind the powerful-modulus Thorner-Zaman line

This scratch frontier file records the elementary arithmetic behind the off-BGK floor's
least-prime-in-AP input.

The powerful-modulus PNT-in-AP discussion in Thorner-Zaman has a threshold of the form

`h / phi(q) >= x^tau`.

For the dyadic floor application one takes the long interval `h = x`, modulus `q = n = 2^a`, and
`phi(n) = n / 2`.  If `x = n^beta`, the main-term side has size `2 * n^(beta - 1)`.  Thus the
pure exponent condition is

`n^(beta * tau) <= 2 * n^(beta - 1)`,

which follows from `1 <= beta * (1 - tau)`.  In particular:

* `tau = 7/12` gives the exact threshold `beta = 12/5`;
* `beta = 3` safely covers every `tau <= 2/3`, hence covers `7/12 + epsilon` for
  `epsilon <= 1/12`.

This file proves only that exponent bookkeeping.  It does not prove a Thorner-Zaman prime-counting
theorem, does not assert that the paper supplies the fixed-polynomial-window count needed by the
coding-theory consumer, and does not prove any floor or delta-star result.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.PowerfulTZThetaGate

/-- **Abstract PNT exponent gate.**  If `1 <= beta * (1 - tau)` and `n >= 1`, then
`n^(beta*tau) <= n^(beta-1)`.  This is the algebra behind the condition
`x^tau <= x/n` after substituting `x = n^beta`. -/
theorem rpow_theta_le_main_term
    {n β τ : ℝ} (hn : 1 ≤ n) (hgate : 1 ≤ β * (1 - τ)) :
    n ^ (β * τ) ≤ n ^ (β - 1) := by
  have hexp : β * τ ≤ β - 1 := by
    have h : 1 ≤ β - β * τ := by
      calc
        1 ≤ β * (1 - τ) := hgate
        _ = β - β * τ := by ring
    linarith
  exact Real.rpow_le_rpow_of_exponent_le hn hexp

/-- **Dyadic main-term form.**  The dyadic `phi(2^a) = 2^a / 2` factor contributes the harmless
constant `2`: under the same exponent gate, `n^(beta*tau) <= 2 * n^(beta-1)`. -/
theorem rpow_theta_le_two_mul_main_term
    {n β τ : ℝ} (hn : 1 ≤ n) (hgate : 1 ≤ β * (1 - τ)) :
    n ^ (β * τ) ≤ 2 * n ^ (β - 1) := by
  have hbase_nonneg : 0 ≤ n := by linarith
  have hpow_nonneg : 0 ≤ n ^ (β - 1) := Real.rpow_nonneg hbase_nonneg (β - 1)
  exact le_trans (rpow_theta_le_main_term hn hgate) (by nlinarith)

/-- `theta = 7/12` has exact critical exponent `beta = 12/5`:
`(12/5) * (1 - 7/12) = 1`. -/
theorem twelve_fifths_times_one_sub_seven_twelfths :
    ((12 : ℝ) / 5) * (1 - (7 : ℝ) / 12) = 1 := by
  norm_num

/-- Any `beta >= 12/5` satisfies the exponent gate for `tau = 7/12`. -/
theorem beta_ge_twelve_fifths_gate {β : ℝ} (hβ : (12 : ℝ) / 5 ≤ β) :
    1 ≤ β * (1 - (7 : ℝ) / 12) := by
  nlinarith

/-- `beta = 3` handles every threshold `tau <= 2/3`. -/
theorem beta_three_gate_of_tau_le_two_thirds {τ : ℝ} (hτ : τ ≤ (2 : ℝ) / 3) :
    1 ≤ (3 : ℝ) * (1 - τ) := by
  nlinarith

/-- The paper's `7/12 + epsilon` threshold is at most `2/3` when `epsilon <= 1/12`. -/
theorem seven_twelfths_plus_eps_le_two_thirds {ε : ℝ} (hε : ε ≤ (1 : ℝ) / 12) :
    (7 : ℝ) / 12 + ε ≤ (2 : ℝ) / 3 := by
  nlinarith

/-- Therefore `beta = 3` satisfies the exponent gate for `tau = 7/12 + epsilon` whenever
`epsilon <= 1/12`. -/
theorem beta_three_gate_for_seven_twelfths_plus_eps {ε : ℝ} (hε : ε ≤ (1 : ℝ) / 12) :
    1 ≤ (3 : ℝ) * (1 - ((7 : ℝ) / 12 + ε)) :=
  beta_three_gate_of_tau_le_two_thirds (seven_twelfths_plus_eps_le_two_thirds hε)

/-- **Concrete beta-three gate.**  For `n >= 1` and `epsilon <= 1/12`,
`n^(3*(7/12+epsilon)) <= 2*n^2`.  This is the exact arithmetic needed for the dyadic
`h = x = n^3`, `phi(n) = n/2` main term to dominate a `7/12+epsilon` threshold. -/
theorem beta_three_seven_twelfths_plus_eps_main_term
    {n ε : ℝ} (hn : 1 ≤ n) (hε : ε ≤ (1 : ℝ) / 12) :
    n ^ ((3 : ℝ) * ((7 : ℝ) / 12 + ε)) ≤ 2 * n ^ ((3 : ℝ) - 1) :=
  rpow_theta_le_two_mul_main_term hn (beta_three_gate_for_seven_twelfths_plus_eps hε)

end ArkLib.ProximityGap.Frontier.PowerfulTZThetaGate

#print axioms ArkLib.ProximityGap.Frontier.PowerfulTZThetaGate.rpow_theta_le_main_term
#print axioms ArkLib.ProximityGap.Frontier.PowerfulTZThetaGate.rpow_theta_le_two_mul_main_term
#print axioms ArkLib.ProximityGap.Frontier.PowerfulTZThetaGate.twelve_fifths_times_one_sub_seven_twelfths
#print axioms ArkLib.ProximityGap.Frontier.PowerfulTZThetaGate.beta_ge_twelve_fifths_gate
#print axioms ArkLib.ProximityGap.Frontier.PowerfulTZThetaGate.beta_three_gate_of_tau_le_two_thirds
#print axioms ArkLib.ProximityGap.Frontier.PowerfulTZThetaGate.seven_twelfths_plus_eps_le_two_thirds
#print axioms ArkLib.ProximityGap.Frontier.PowerfulTZThetaGate.beta_three_gate_for_seven_twelfths_plus_eps
#print axioms ArkLib.ProximityGap.Frontier.PowerfulTZThetaGate.beta_three_seven_twelfths_plus_eps_main_term
