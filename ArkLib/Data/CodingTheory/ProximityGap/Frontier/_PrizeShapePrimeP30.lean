/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.NormNum.Prime

/-!
# A concrete prize-shaped prime above `2^158`

This file certifies the concrete field modulus

`P = 2^30 * (2^128 + 192) + 1`.

The primality proof is a Lucas certificate.  To keep the kernel computation logarithmic in the
exponent, `binaryPow` is a locally verified square-and-multiply implementation; it is used only as
a computational witness and is proved equal to ordinary monoid exponentiation.
-/

namespace ArkLib.ProximityGap.PrizeShapePrimeP30

set_option autoImplicit false
set_option maxRecDepth 100000

/-- The concrete prize-shaped modulus. -/
abbrev P : ℕ := 365375409332725729550921208179070755120141565953

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

/-! ## The two nontrivial Pratt subcertificates -/

/-- The large prime factor occurring in `462478642316479903 - 1`. -/
private abbrev Q0 : ℕ := 10455338053

private theorem prime_223 : Nat.Prime 223 := by norm_num
private theorem prime_829 : Nat.Prime 829 := by norm_num
private theorem prime_1571 : Nat.Prime 1571 := by norm_num

private theorem Q0_cert_main : (5 : ZMod Q0) ^ (Q0 - 1) = 1 := by
  rw [← binaryPow_eq_pow]
  decide

private theorem Q0_cert_q2 : (5 : ZMod Q0) ^ ((Q0 - 1) / 2) ≠ 1 := by
  rw [← binaryPow_eq_pow]
  decide

private theorem Q0_cert_q3 : (5 : ZMod Q0) ^ ((Q0 - 1) / 3) ≠ 1 := by
  rw [← binaryPow_eq_pow]
  decide

private theorem Q0_cert_q223 : (5 : ZMod Q0) ^ ((Q0 - 1) / 223) ≠ 1 := by
  rw [← binaryPow_eq_pow]
  decide

private theorem Q0_cert_q829 : (5 : ZMod Q0) ^ ((Q0 - 1) / 829) ≠ 1 := by
  rw [← binaryPow_eq_pow]
  decide

private theorem Q0_cert_q1571 : (5 : ZMod Q0) ^ ((Q0 - 1) / 1571) ≠ 1 := by
  rw [← binaryPow_eq_pow]
  decide

private theorem prime_Q0 : Nat.Prime Q0 := by
  refine lucas_primality Q0 5 Q0_cert_main ?_
  intro q hq hdvd
  rw [show Q0 - 1 = 2 ^ 2 * (3 ^ 2 * (223 * (829 * 1571))) from by norm_num] at hdvd
  rcases (Nat.Prime.dvd_mul hq).mp hdvd with h2 | hrest
  · have hq2 : q = 2 :=
      (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h2)
    subst q
    exact Q0_cert_q2
  · rcases (Nat.Prime.dvd_mul hq).mp hrest with h3 | hrest
    · have hq3 : q = 3 :=
        (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp (hq.dvd_of_dvd_pow h3)
      subst q
      exact Q0_cert_q3
    · rcases (Nat.Prime.dvd_mul hq).mp hrest with h223 | hrest
      · have hq223 : q = 223 :=
          (Nat.prime_dvd_prime_iff_eq hq prime_223).mp h223
        subst q
        exact Q0_cert_q223
      · rcases (Nat.Prime.dvd_mul hq).mp hrest with h829 | h1571
        · have hq829 : q = 829 :=
            (Nat.prime_dvd_prime_iff_eq hq prime_829).mp h829
          subst q
          exact Q0_cert_q829
        · have hq1571 : q = 1571 :=
            (Nat.prime_dvd_prime_iff_eq hq prime_1571).mp h1571
          subst q
          exact Q0_cert_q1571

/-- The 59-bit prime factor in the factorization of `P - 1`. -/
theorem prime_462478642316479903 : Nat.Prime 462478642316479903 := by
  let Q : ℕ := 462478642316479903
  have cert_main : (3 : ZMod Q) ^ (Q - 1) = 1 := by
    rw [← binaryPow_eq_pow]
    decide
  have cert_q2 : (3 : ZMod Q) ^ ((Q - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow]
    decide
  have cert_q3 : (3 : ZMod Q) ^ ((Q - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow]
    decide
  have cert_q479 : (3 : ZMod Q) ^ ((Q - 1) / 479) ≠ 1 := by
    rw [← binaryPow_eq_pow]
    decide
  have cert_q15391 : (3 : ZMod Q) ^ ((Q - 1) / 15391) ≠ 1 := by
    rw [← binaryPow_eq_pow]
    decide
  have cert_qQ0 : (3 : ZMod Q) ^ ((Q - 1) / Q0) ≠ 1 := by
    rw [← binaryPow_eq_pow]
    decide
  have prime_479 : Nat.Prime 479 := by norm_num
  have prime_15391 : Nat.Prime 15391 := by norm_num
  refine lucas_primality Q 3 cert_main ?_
  intro q hq hdvd
  rw [show Q - 1 = 2 * (3 * (479 * (15391 * Q0))) from by norm_num] at hdvd
  rcases (Nat.Prime.dvd_mul hq).mp hdvd with h2 | hrest
  · have hq2 : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h2
    subst q
    exact cert_q2
  · rcases (Nat.Prime.dvd_mul hq).mp hrest with h3 | hrest
    · have hq3 : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp h3
      subst q
      exact cert_q3
    · rcases (Nat.Prime.dvd_mul hq).mp hrest with h479 | hrest
      · have hq479 : q = 479 := (Nat.prime_dvd_prime_iff_eq hq prime_479).mp h479
        subst q
        exact cert_q479
      · rcases (Nat.Prime.dvd_mul hq).mp hrest with h15391 | hQ0
        · have hq15391 : q = 15391 :=
            (Nat.prime_dvd_prime_iff_eq hq prime_15391).mp h15391
          subst q
          exact cert_q15391
        · have hqQ0 : q = Q0 := (Nat.prime_dvd_prime_iff_eq hq prime_Q0).mp hQ0
          subst q
          exact cert_qQ0

/-! ## The advertised factorization and the Lucas certificate for `P` -/

/-- The 15-bit factor in `P - 1` is prime. -/
theorem prime_26407 : Nat.Prime 26407 := by norm_num

/-- The 19-bit factor in `P - 1` is prime. -/
theorem prime_279991 : Nat.Prime 279991 := by norm_num

/-- The 23-bit factor in `P - 1` is prime. -/
theorem prime_4533259 : Nat.Prime 4533259 := by norm_num

/-- Complete factorization used by the outer Lucas certificate. -/
theorem P_sub_one_factorization :
    P - 1 = 2 ^ 36 * 7 ^ 3 * 26407 * 279991 * 4533259 * 462478642316479903 := by
  norm_num

/-- Every distinct prime base in the displayed factorization of `P - 1` is prime. -/
theorem P_factor_primes :
    Nat.Prime 2 ∧ Nat.Prime 7 ∧ Nat.Prime 26407 ∧ Nat.Prime 279991 ∧
      Nat.Prime 4533259 ∧ Nat.Prime 462478642316479903 := by
  exact ⟨Nat.prime_two, by norm_num, prime_26407, prime_279991, prime_4533259,
    prime_462478642316479903⟩

private theorem P_cert_main : (3 : ZMod P) ^ (P - 1) = 1 := by
  rw [← binaryPow_eq_pow]
  decide

private theorem P_cert_q2 : (3 : ZMod P) ^ ((P - 1) / 2) ≠ 1 := by
  rw [← binaryPow_eq_pow]
  decide

private theorem P_cert_q7 : (3 : ZMod P) ^ ((P - 1) / 7) ≠ 1 := by
  rw [← binaryPow_eq_pow]
  decide

private theorem P_cert_q26407 : (3 : ZMod P) ^ ((P - 1) / 26407) ≠ 1 := by
  rw [← binaryPow_eq_pow]
  decide

private theorem P_cert_q279991 : (3 : ZMod P) ^ ((P - 1) / 279991) ≠ 1 := by
  rw [← binaryPow_eq_pow]
  decide

private theorem P_cert_q4533259 : (3 : ZMod P) ^ ((P - 1) / 4533259) ≠ 1 := by
  rw [← binaryPow_eq_pow]
  decide

private theorem P_cert_q462478642316479903 :
    (3 : ZMod P) ^ ((P - 1) / 462478642316479903) ≠ 1 := by
  rw [← binaryPow_eq_pow]
  decide

/-- **The concrete prize-shaped modulus `P` is prime.**

The witness `3` has full order `P - 1`; the six branches are exactly the six distinct prime
factors in `P_sub_one_factorization`.
-/
theorem prime_P : Nat.Prime P := by
  refine lucas_primality P 3 P_cert_main ?_
  intro q hq hdvd
  rw [show P - 1 =
      2 ^ 36 * (7 ^ 3 * (26407 * (279991 * (4533259 * 462478642316479903)))) from by
        norm_num] at hdvd
  rcases (Nat.Prime.dvd_mul hq).mp hdvd with h2 | hrest
  · have hq2 : q = 2 :=
      (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h2)
    subst q
    exact P_cert_q2
  · rcases (Nat.Prime.dvd_mul hq).mp hrest with h7 | hrest
    · have hq7 : q = 7 :=
        (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h7)
      subst q
      exact P_cert_q7
    · rcases (Nat.Prime.dvd_mul hq).mp hrest with h26407 | hrest
      · have hq26407 : q = 26407 :=
          (Nat.prime_dvd_prime_iff_eq hq prime_26407).mp h26407
        subst q
        exact P_cert_q26407
      · rcases (Nat.Prime.dvd_mul hq).mp hrest with h279991 | hrest
        · have hq279991 : q = 279991 :=
            (Nat.prime_dvd_prime_iff_eq hq prime_279991).mp h279991
          subst q
          exact P_cert_q279991
        · rcases (Nat.Prime.dvd_mul hq).mp hrest with h4533259 | hlarge
          · have hq4533259 : q = 4533259 :=
              (Nat.prime_dvd_prime_iff_eq hq prime_4533259).mp h4533259
            subst q
            exact P_cert_q4533259
          · have hqlarge : q = 462478642316479903 :=
              (Nat.prime_dvd_prime_iff_eq hq prime_462478642316479903).mp hlarge
            subst q
            exact P_cert_q462478642316479903

/-! ## Prize normalization and an explicit smooth subgroup generator -/

/-- The defining prize shape of `P`. -/
theorem P_eq_prize_shape : P = 2 ^ 30 * (2 ^ 128 + 192) + 1 := by norm_num

/-- Dividing by the security scale has exactly the advertised quotient. -/
theorem P_div_two_pow_128 : P / 2 ^ 128 = 2 ^ 30 := by norm_num

/-- The field modulus is one modulo the smooth domain size. -/
theorem P_modEq_one_two_pow_30 : P ≡ 1 [MOD 2 ^ 30] := by
  norm_num [Nat.ModEq]

local instance fact_prime_P : Fact (Nat.Prime P) := ⟨prime_P⟩

/-- An explicit element of order `2^30` in `ZMod P`. -/
abbrev g : ZMod P := 303645430271030343624574566109998498685964493478

/-- The explicit element is the expected cofactor power of the Lucas witness. -/
theorem g_eq_pow_three :
    g = (3 : ZMod P) ^ ((P - 1) / 2 ^ 30) := by
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

end ArkLib.ProximityGap.PrizeShapePrimeP30
