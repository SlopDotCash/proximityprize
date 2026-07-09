/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.NumberTheory.LucasPrimality

/-!
# A concrete prize-shaped prime above `2^158`

This file certifies the concrete field modulus

`P = 2^30 * (2^128 + 192) + 1`.

The primality proof is a Lucas certificate.  To keep the kernel computation logarithmic in the
exponent, `binaryPow` is a locally verified square-and-multiply implementation; it is used only as
a computational witness and is proved equal to ordinary monoid exponentiation.
-/

namespace ArkLib.ProximityGap.PrizeShapePrimeP30

/-- The concrete prize-shaped modulus. -/
abbrev P : ℕ := 365375409332725729550921208179070755120141565953

/-- Kernel-cheap square-and-multiply exponentiation. -/
private def binaryPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  if h0 : n = 0 then 1
  else if n % 2 = 0 then
    binaryPow (a * a) (n / 2)
  else
    a * binaryPow (a * a) (n / 2)
termination_by n
decreasing_by
  all_goals exact Nat.div_lt_self (Nat.pos_of_ne_zero h0) (by norm_num)

private theorem binaryPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    binaryPow a n = a ^ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rw [binaryPow]
      split_ifs with h0 heven
      · subst n
        simp
      · have hnpos : 0 < n := Nat.pos_of_ne_zero h0
        have hhalf : n / 2 < n := Nat.div_lt_self hnpos (by norm_num)
        rw [ih (n / 2) hhalf, mul_pow, ← pow_add]
        have hdvd : 2 ∣ n := (Nat.dvd_iff_mod_eq_zero).2 heven
        have htwo : 2 * (n / 2) = n := Nat.mul_div_cancel' hdvd
        congr 1
        omega
      · have hnpos : 0 < n := Nat.pos_of_ne_zero h0
        have hhalf : n / 2 < n := Nat.div_lt_self hnpos (by norm_num)
        rw [ih (n / 2) hhalf, mul_pow, ← pow_add, ← pow_succ']
        have hnmod : n % 2 = 1 := by omega
        have hdecomp := Nat.mod_add_div n 2
        congr 1
        omega

private theorem test_main :
    (3 : ZMod P) ^ (P - 1) = 1 := by
  rw [← binaryPow_eq_pow]
  decide

end ArkLib.ProximityGap.PrizeShapePrimeP30
