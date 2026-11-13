/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic.SplitIfs

/-!
# Binary powers for arithmetic certificates

The square-and-multiply implementation from `_PrizeShapePrimeP30Second.lean` makes large
modular exponentiation checks feasible by kernel reduction. The correctness theorem lets
arithmetic certificates compute with it while stating their results using ordinary powers.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.BinaryPower

private def binaryPowAux {M : Type*} [Monoid M] (a : M) (n : ℕ) : ℕ → M
  | 0 => 1
  | fuel + 1 =>
      if n = 0 then 1
      else if n % 2 = 0 then
        binaryPowAux (a * a) (n / 2) fuel
      else
        a * binaryPowAux (a * a) (n / 2) fuel

/-- Square-and-multiply exponentiation for kernel-checked computations. -/
def binaryPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  binaryPowAux a n (n + 1)

private theorem binaryPowAux_eq_pow {M : Type*} [Monoid M] (a : M) (n fuel : ℕ)
    (hnfuel : n < fuel) : binaryPowAux a n fuel = a ^ n := by
  induction fuel generalizing a n with
  | zero => omega
  | succ fuel ih =>
      rw [binaryPowAux]
      split_ifs with h0 heven
      · subst n
        simp
      · have hdiv := Nat.div_lt_self (Nat.pos_of_ne_zero h0) (by decide : 1 < 2)
        have hhalf : n / 2 < fuel := by omega
        rw [ih (a * a) (n / 2) hhalf, ← pow_two, ← pow_mul]
        have hdvd : 2 ∣ n := (Nat.dvd_iff_mod_eq_zero).2 heven
        have htwo : 2 * (n / 2) = n := Nat.mul_div_cancel' hdvd
        congr 1
      · have hdiv := Nat.div_lt_self (Nat.pos_of_ne_zero h0) (by decide : 1 < 2)
        have hhalf : n / 2 < fuel := by omega
        rw [ih (a * a) (n / 2) hhalf, ← pow_two, ← pow_mul, ← pow_succ']
        have hnmod : n % 2 = 1 := by omega
        have hdecomp := Nat.mod_add_div n 2
        congr 1
        omega

/-- Binary exponentiation agrees with the monoid power operation. -/
theorem binaryPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    binaryPow a n = a ^ n :=
  binaryPowAux_eq_pow a n (n + 1) (by omega)

end ArkLib.ProximityGap.BinaryPower
