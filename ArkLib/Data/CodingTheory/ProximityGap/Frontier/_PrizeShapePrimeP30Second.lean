/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.NormNum.Prime

/-!
# A second concrete prize-shaped prime with a smooth subgroup of order `2^30`

This file certifies

`P = 2^30 * (2 * 2^128 + 13) + 1`

and the explicit element obtained from the Lucas witness `37`.  The primality proof uses the
complete factorization of `P - 1`.  As in `_PrizeShapePrimeP30.lean`, `binaryPow` is a locally
verified square-and-multiply implementation used only to make the certificate computations
kernel-cheap.
-/

namespace ArkLib.ProximityGap.PrizeShapePrimeP30Second

set_option autoImplicit false
set_option maxRecDepth 100000

/-- The second concrete prize-shaped modulus. -/
abbrev P : ℕ := 730750818665451459101842416358141509841924915201

/-- Structurally recursive fuel wrapper for kernel-cheap square-and-multiply exponentiation. -/
private def binaryPowAux {M : Type*} [Monoid M] (a : M) (n : ℕ) : ℕ → M
  | 0 => 1
  | fuel + 1 =>
      if n = 0 then 1
      else if n % 2 = 0 then
        binaryPowAux (a * a) (n / 2) fuel
      else
        a * binaryPowAux (a * a) (n / 2) fuel

/-- Kernel-cheap square-and-multiply exponentiation. -/
private def binaryPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
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
      · have hnpos : 0 < n := Nat.pos_of_ne_zero h0
        have hhalf : n / 2 < fuel :=
          (Nat.div_lt_self hnpos (by norm_num)).trans_le (by omega)
        rw [ih (a * a) (n / 2) hhalf, ← pow_two, ← pow_mul]
        have hdvd : 2 ∣ n := (Nat.dvd_iff_mod_eq_zero).2 heven
        have htwo : 2 * (n / 2) = n := Nat.mul_div_cancel' hdvd
        congr 1
      · have hnpos : 0 < n := Nat.pos_of_ne_zero h0
        have hhalf : n / 2 < fuel :=
          (Nat.div_lt_self hnpos (by norm_num)).trans_le (by omega)
        rw [ih (a * a) (n / 2) hhalf, ← pow_two, ← pow_mul, ← pow_succ']
        have hnmod : n % 2 = 1 := by omega
        have hdecomp := Nat.mod_add_div n 2
        congr 1
        omega

private theorem binaryPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    binaryPow a n = a ^ n := by
  exact binaryPowAux_eq_pow a n (n + 1) (by omega)

/-! ## Prime factors below the two large factors of `P - 1` -/

private theorem prime_462983 : Nat.Prime 462983 := by norm_num
private theorem prime_2599243 : Nat.Prime 2599243 := by norm_num
private theorem prime_59494517 : Nat.Prime 59494517 := by norm_num
private theorem prime_379484152867 : Nat.Prime 379484152867 := by norm_num

/-- The 48-bit prime factor in `P - 1`. -/
theorem prime_202172094073993 : Nat.Prime 202172094073993 := by
  let Q : ℕ := 202172094073993
  have cert_main : (11 : ZMod Q) ^ (Q - 1) = 1 := by
    rw [← binaryPow_eq_pow]
    decide
  have cert_q2 : (11 : ZMod Q) ^ ((Q - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow]
    decide
  have cert_q3 : (11 : ZMod Q) ^ ((Q - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow]
    decide
  have cert_q7 : (11 : ZMod Q) ^ ((Q - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow]
    decide
  have cert_q462983 : (11 : ZMod Q) ^ ((Q - 1) / 462983) ≠ 1 := by
    rw [← binaryPow_eq_pow]
    decide
  have cert_q2599243 : (11 : ZMod Q) ^ ((Q - 1) / 2599243) ≠ 1 := by
    rw [← binaryPow_eq_pow]
    decide
  refine lucas_primality Q 11 cert_main ?_
  intro q hq hdvd
  rw [show Q - 1 = 2 ^ 3 * (3 * (7 * (462983 * 2599243))) from by norm_num] at hdvd
  rcases (Nat.Prime.dvd_mul hq).mp hdvd with h2 | hrest
  · have hq2 : q = 2 :=
      (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h2)
    subst q
    exact cert_q2
  · rcases (Nat.Prime.dvd_mul hq).mp hrest with h3 | hrest
    · have hq3 : q = 3 :=
        (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp h3
      subst q
      exact cert_q3
    · rcases (Nat.Prime.dvd_mul hq).mp hrest with h7 | hrest
      · have hq7 : q = 7 :=
          (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h7
        subst q
        exact cert_q7
      · rcases (Nat.Prime.dvd_mul hq).mp hrest with h462983 | h2599243
        · have hq462983 : q = 462983 :=
            (Nat.prime_dvd_prime_iff_eq hq prime_462983).mp h462983
          subst q
          exact cert_q462983
        · have hq2599243 : q = 2599243 :=
            (Nat.prime_dvd_prime_iff_eq hq prime_2599243).mp h2599243
          subst q
          exact cert_q2599243

/-- The prime half-factor below the 67-bit factor in `P - 1`. -/
theorem prime_45154452767952660479 : Nat.Prime 45154452767952660479 := by
  let Q : ℕ := 45154452767952660479
  have cert_main : (7 : ZMod Q) ^ (Q - 1) = 1 := by
    rw [← binaryPow_eq_pow]
    decide
  have cert_q2 : (7 : ZMod Q) ^ ((Q - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow]
    decide
  have cert_q59494517 : (7 : ZMod Q) ^ ((Q - 1) / 59494517) ≠ 1 := by
    rw [← binaryPow_eq_pow]
    decide
  have cert_q379484152867 : (7 : ZMod Q) ^ ((Q - 1) / 379484152867) ≠ 1 := by
    rw [← binaryPow_eq_pow]
    decide
  refine lucas_primality Q 7 cert_main ?_
  intro q hq hdvd
  rw [show Q - 1 = 2 * (59494517 * 379484152867) from by norm_num] at hdvd
  rcases (Nat.Prime.dvd_mul hq).mp hdvd with h2 | hrest
  · have hq2 : q = 2 :=
      (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h2
    subst q
    exact cert_q2
  · rcases (Nat.Prime.dvd_mul hq).mp hrest with h59494517 | h379484152867
    · have hq59494517 : q = 59494517 :=
        (Nat.prime_dvd_prime_iff_eq hq prime_59494517).mp h59494517
      subst q
      exact cert_q59494517
    · have hq379484152867 : q = 379484152867 :=
        (Nat.prime_dvd_prime_iff_eq hq prime_379484152867).mp h379484152867
      subst q
      exact cert_q379484152867

/-- The 67-bit prime factor in `P - 1`. -/
theorem prime_90308905535905320959 : Nat.Prime 90308905535905320959 := by
  let Q : ℕ := 90308905535905320959
  have cert_main : (7 : ZMod Q) ^ (Q - 1) = 1 := by
    rw [← binaryPow_eq_pow]
    decide
  have cert_q2 : (7 : ZMod Q) ^ ((Q - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow]
    decide
  have cert_q45154452767952660479 :
      (7 : ZMod Q) ^ ((Q - 1) / 45154452767952660479) ≠ 1 := by
    rw [← binaryPow_eq_pow]
    decide
  refine lucas_primality Q 7 cert_main ?_
  intro q hq hdvd
  rw [show Q - 1 = 2 * 45154452767952660479 from by norm_num] at hdvd
  rcases (Nat.Prime.dvd_mul hq).mp hdvd with h2 | hlarge
  · have hq2 : q = 2 :=
      (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h2
    subst q
    exact cert_q2
  · have hqlarge : q = 45154452767952660479 :=
      (Nat.prime_dvd_prime_iff_eq hq prime_45154452767952660479).mp hlarge
    subst q
    exact cert_q45154452767952660479

/-! ## The advertised factorization and the Lucas certificate for `P` -/

/-- Complete factorization used by the outer Lucas certificate. -/
theorem P_sub_one_factorization :
    P - 1 = 2 ^ 30 * 3 * 5 ^ 2 * 7 * 71 * 202172094073993 * 90308905535905320959 := by
  norm_num

/-- Every distinct prime base in the displayed factorization of `P - 1` is prime. -/
theorem P_factor_primes :
    Nat.Prime 2 ∧ Nat.Prime 3 ∧ Nat.Prime 5 ∧ Nat.Prime 7 ∧ Nat.Prime 71 ∧
      Nat.Prime 202172094073993 ∧ Nat.Prime 90308905535905320959 := by
  exact ⟨Nat.prime_two, Nat.prime_three, by norm_num, by norm_num, by norm_num,
    prime_202172094073993, prime_90308905535905320959⟩

private theorem P_cert_main : (37 : ZMod P) ^ (P - 1) = 1 := by
  rw [← binaryPow_eq_pow]
  decide

private theorem P_cert_q2 : (37 : ZMod P) ^ ((P - 1) / 2) ≠ 1 := by
  rw [← binaryPow_eq_pow]
  decide

private theorem P_cert_q3 : (37 : ZMod P) ^ ((P - 1) / 3) ≠ 1 := by
  rw [← binaryPow_eq_pow]
  decide

private theorem P_cert_q5 : (37 : ZMod P) ^ ((P - 1) / 5) ≠ 1 := by
  rw [← binaryPow_eq_pow]
  decide

private theorem P_cert_q7 : (37 : ZMod P) ^ ((P - 1) / 7) ≠ 1 := by
  rw [← binaryPow_eq_pow]
  decide

private theorem P_cert_q71 : (37 : ZMod P) ^ ((P - 1) / 71) ≠ 1 := by
  rw [← binaryPow_eq_pow]
  decide

private theorem P_cert_q202172094073993 :
    (37 : ZMod P) ^ ((P - 1) / 202172094073993) ≠ 1 := by
  rw [← binaryPow_eq_pow]
  decide

private theorem P_cert_q90308905535905320959 :
    (37 : ZMod P) ^ ((P - 1) / 90308905535905320959) ≠ 1 := by
  rw [← binaryPow_eq_pow]
  decide

/-- **The second concrete prize-shaped modulus `P` is prime.**

The witness `37` has full order `P - 1`; the seven branches are exactly the seven distinct prime
factors in `P_sub_one_factorization`.
-/
theorem prime_P : Nat.Prime P := by
  refine lucas_primality P 37 P_cert_main ?_
  intro q hq hdvd
  rw [show P - 1 =
      2 ^ 30 * (3 * (5 ^ 2 * (7 * (71 * (202172094073993 * 90308905535905320959)))))
      from by norm_num] at hdvd
  rcases (Nat.Prime.dvd_mul hq).mp hdvd with h2 | hrest
  · have hq2 : q = 2 :=
      (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h2)
    subst q
    exact P_cert_q2
  · rcases (Nat.Prime.dvd_mul hq).mp hrest with h3 | hrest
    · have hq3 : q = 3 :=
        (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp h3
      subst q
      exact P_cert_q3
    · rcases (Nat.Prime.dvd_mul hq).mp hrest with h5 | hrest
      · have hq5 : q = 5 :=
          (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h5)
        subst q
        exact P_cert_q5
      · rcases (Nat.Prime.dvd_mul hq).mp hrest with h7 | hrest
        · have hq7 : q = 7 :=
            (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h7
          subst q
          exact P_cert_q7
        · rcases (Nat.Prime.dvd_mul hq).mp hrest with h71 | hrest
          · have hq71 : q = 71 :=
              (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h71
            subst q
            exact P_cert_q71
          · rcases (Nat.Prime.dvd_mul hq).mp hrest with h202172094073993 | hlarge
            · have hq202172094073993 : q = 202172094073993 :=
                (Nat.prime_dvd_prime_iff_eq hq prime_202172094073993).mp h202172094073993
              subst q
              exact P_cert_q202172094073993
            · have hqlarge : q = 90308905535905320959 :=
                (Nat.prime_dvd_prime_iff_eq hq prime_90308905535905320959).mp hlarge
              subst q
              exact P_cert_q90308905535905320959

/-! ## Prize normalization and an explicit smooth subgroup generator -/

/-- The defining prize shape of `P`. -/
theorem P_eq_prize_shape : P = 2 ^ 30 * (2 * 2 ^ 128 + 13) + 1 := by norm_num

/-- Dividing by the security scale has exactly the advertised quotient. -/
theorem P_div_two_pow_128 : P / 2 ^ 128 = 2 ^ 31 := by norm_num

/-- The field modulus is one modulo the smooth domain size. -/
theorem P_modEq_one_two_pow_30 : P ≡ 1 [MOD 2 ^ 30] := by
  norm_num [Nat.ModEq]

local instance fact_prime_P : Fact (Nat.Prime P) := ⟨prime_P⟩

/-- An explicit element of order `2^30` in `ZMod P`. -/
abbrev g : ZMod P := 192152681249815148642741928588691886362054863855

/-- The explicit element is the expected cofactor power of the Lucas witness. -/
theorem g_eq_pow_thirtyseven :
    g = (37 : ZMod P) ^ ((P - 1) / 2 ^ 30) := by
  rw [← binaryPow_eq_pow]
  decide

private theorem g_pow_29_ne_one : g ^ (2 : ℕ) ^ 29 ≠ 1 := by
  rw [← binaryPow_eq_pow]
  decide

private theorem g_pow_30_eq_one : g ^ (2 : ℕ) ^ 30 = 1 := by
  rw [← binaryPow_eq_pow]
  decide

/-- The explicit element `g` has exact smooth order `2^30`. -/
theorem orderOf_g : orderOf g = 2 ^ 30 := by
  have h := orderOf_eq_prime_pow (x := g) g_pow_29_ne_one g_pow_30_eq_one
  norm_num at h ⊢
  exact h

/-- A smooth order-`2^30` element exists in the certified prime field. -/
theorem exists_orderOf_two_pow_30 : ∃ x : ZMod P, orderOf x = 2 ^ 30 :=
  ⟨g, orderOf_g⟩

#print axioms prime_P
#print axioms orderOf_g
#print axioms exists_orderOf_two_pow_30

end ArkLib.ProximityGap.PrizeShapePrimeP30Second
