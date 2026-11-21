/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.NormNum.Prime
import ArkLib.Research.ProximityGap.Support.BinaryPower

/-!
# A prime field in the shortening window

The modulus is one more than `2^144 * 7^5`. The two prime divisors of this
product give a Lucas certificate with witness `3`. The field has a subgroup
of order `2^30` and its error budget at security `2^-128` is an even integer
strictly between `2^30` and `2^30 + ⌊2^30 / 14⌋`.
-/

namespace ArkLib.ProximityGap.Frontier.ShorteningWindowPrime

set_option autoImplicit false
set_option maxRecDepth 100000

open ArkLib.ProximityGap.BinaryPower (binaryPow_eq_pow)

/-- A 159-bit modulus with a smooth multiplicative group. -/
abbrev P : ℕ := 374808624551704183139790817008401011831012851713

/-- Complete factorization of the group order. -/
theorem P_sub_one : P - 1 = 2 ^ 144 * 7 ^ 5 := by norm_num [P]

/-- Primality by the Lucas criterion with full-order witness `3`. -/
theorem prime_P : Nat.Prime P := by
  have hmain : (3 : ZMod P) ^ (P - 1) = 1 := by
    rw [← binaryPow_eq_pow]
    decide
  refine lucas_primality P 3 hmain ?_
  intro q hq hdvd
  rw [P_sub_one] at hdvd
  rcases (Nat.Prime.dvd_mul hq).mp hdvd with htwo | hseven
  · have heq : q = 2 :=
      (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow htwo)
    subst q
    rw [← binaryPow_eq_pow]
    decide
  · have heq : q = 7 :=
      (Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 7)).mp
        (hq.dvd_of_dvd_pow hseven)
    subst q
    rw [← binaryPow_eq_pow]
    decide

instance fact_prime_P : Fact (Nat.Prime P) := ⟨prime_P⟩

/-- The order-`2^30` element obtained by raising the Lucas witness to its cofactor. -/
abbrev g : ZMod P := 287207082126316176040739287625456263882736992611

/-- The two dyadic powers certify the exact order of the domain generator. -/
theorem orderOf_g : orderOf g = 2 ^ 30 := by
  have hhalf : g ^ (2 : ℕ) ^ 29 ≠ 1 := by
    rw [← binaryPow_eq_pow]
    decide
  have hfull : g ^ (2 : ℕ) ^ 30 = 1 := by
    rw [← binaryPow_eq_pow]
    decide
  have h := orderOf_eq_prime_pow (x := g) hhalf hfull
  norm_num at h ⊢
  exact h

/-- The integer number of bad challenges allowed by the target error. -/
theorem P_div_two_pow_128 : P / 2 ^ 128 = 1101463552 := by norm_num [P]

/-- The even part of the error budget lies in the specified shortening window. -/
theorem even_budget_window :
    2 ^ 30 < 2 * ((P / 2 ^ 128) / 2) ∧
      2 * ((P / 2 ^ 128) / 2) ≤ 2 ^ 30 + 2 ^ 30 / 14 := by
  rw [P_div_two_pow_128]
  norm_num

#print axioms prime_P
#print axioms orderOf_g
#print axioms even_budget_window

end ArkLib.ProximityGap.Frontier.ShorteningWindowPrime
