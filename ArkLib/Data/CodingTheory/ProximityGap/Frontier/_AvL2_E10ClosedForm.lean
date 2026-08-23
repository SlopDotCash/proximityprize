/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# The char-0 additive energy `E_10(μ_n)`: exact closed form (#444, avenue L2)

This file extends the char-0 additive-energy closed-form ladder one further rung past
`_AvL2_E9ClosedForm.lean`.  It records the exact degree-10 polynomial for the cross-polytope /
Lam--Leung char-0 model at depth `r = 10`, proves its Wick-leading-term bound, and proves the
strict positive deficit by an explicit nonnegative shifted-coordinate certificate.

The polynomial was generated from
`(20)! · [z^10] (Σ_{k≥0} z^k/(k!)²)^(n/2)` and checked at the anchor points
`E_10(2)=C(20,10)=184756`, `E_10(4)=34134779536`; the leading coefficient is
`19‼ = 654729075` and the second coefficient is `-C(10,2)·19‼ = -29462808375`.

Honest scope: this is a char-0 rung only.  It does not assert the char-p transfer at prize depth;
that transfer is the BGK/Paley wall isolated in #444.
-/

namespace ProximityGap.Frontier.E10ClosedForm

/-- `E_10(ℂ)(n)`: the char-0 additive energy of `μ_n` at depth `r = 10`, in closed form. -/
def E10 (n : ℤ) : ℤ :=
  654729075 * n ^ 10 - 29462808375 * n ^ 9 + 621992621250 * n ^ 8
    - 7974600133500 * n ^ 7 + 67587638763645 * n ^ 6 - 388126232819325 * n ^ 5
    + 1492536213328875 * n ^ 4 - 3659637492418050 * n ^ 3
    + 5115749229952933 * n ^ 2 - 3048056301418128 * n

/-- The Wick leading term `(2r−1)‼·n^r`. -/
def wick (r : ℕ) (n : ℤ) : ℤ := (Nat.doubleFactorial (2 * r - 1) : ℤ) * n ^ r

@[simp] theorem wick_ten (n : ℤ) : wick 10 n = 654729075 * n ^ 10 := by
  simp [wick, Nat.doubleFactorial]

/-! ## Small-case exact values -/

/-- `E_10(2) = 184756 = C(20,10)`. -/
theorem E10_two : E10 2 = 184756 := by decide

/-- `E_10(4) = 34134779536`. -/
theorem E10_four : E10 4 = 34134779536 := by decide

/-! ## The exact char-0 deficit `D_10 = wick 10 n − E_10(ℂ)` -/

/-- The exact deficit `wick 10 n − E_10(ℂ)`.  Its leading nonzero coefficient is
`C(10,2)·19‼ = 29462808375`. -/
theorem deficit_ten (n : ℤ) :
    wick 10 n - E10 n =
      29462808375 * n ^ 9 - 621992621250 * n ^ 8 + 7974600133500 * n ^ 7
        - 67587638763645 * n ^ 6 + 388126232819325 * n ^ 5
        - 1492536213328875 * n ^ 4 + 3659637492418050 * n ^ 3
        - 5115749229952933 * n ^ 2 + 3048056301418128 * n := by
  simp only [wick_ten, E10]; ring

/-- `256·(wick 10 n − E_10) = n · (Σ_k c_k · u^k)` with `u = 2n − 7` and all `c_k ≥ 0`.
This is the positivity certificate for the depth-10 char-0 Wick cushion. -/
theorem deficit_ten_factored_u (n : ℤ) :
    256 * (wick 10 n - E10 n) =
      n * (12017417276419555 + 18693465128957476 * (2 * n - 7)
        + 9189049903090200 * (2 * n - 7) ^ 2
        + 3190736872880700 * (2 * n - 7) ^ 3
        + 748576631152350 * (2 * n - 7) ^ 4
        + 84892521053340 * (2 * n - 7) ^ 5
        + 11366096742000 * (2 * n - 7) ^ 6
        + 405932026500 * (2 * n - 7) ^ 7
        + 29462808375 * (2 * n - 7) ^ 8) := by
  rw [deficit_ten]; ring

/-- `0 ≤ 256·(wick 10 n − E10 n)` for `n ≥ 4`, from the nonnegative `u = 2n−7` certificate. -/
theorem deficit_ten_scaled_nonneg (n : ℤ) (hn : 4 ≤ n) :
    0 ≤ 256 * (wick 10 n - E10 n) := by
  have hu0 : (0 : ℤ) ≤ 2 * n - 7 := by linarith
  have hn0 : (0 : ℤ) ≤ n := by linarith
  rw [deficit_ten_factored_u]
  have h0 : (0 : ℤ) ≤ n * 12017417276419555 := by positivity
  have h1 : (0 : ℤ) ≤ n * (18693465128957476 * (2 * n - 7)) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) hu0)
  have h2 : (0 : ℤ) ≤ n * (9189049903090200 * (2 * n - 7) ^ 2) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 2))
  have h3 : (0 : ℤ) ≤ n * (3190736872880700 * (2 * n - 7) ^ 3) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 3))
  have h4 : (0 : ℤ) ≤ n * (748576631152350 * (2 * n - 7) ^ 4) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 4))
  have h5 : (0 : ℤ) ≤ n * (84892521053340 * (2 * n - 7) ^ 5) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 5))
  have h6 : (0 : ℤ) ≤ n * (11366096742000 * (2 * n - 7) ^ 6) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 6))
  have h7 : (0 : ℤ) ≤ n * (405932026500 * (2 * n - 7) ^ 7) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 7))
  have h8 : (0 : ℤ) ≤ n * (29462808375 * (2 * n - 7) ^ 8) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 8))
  nlinarith [h0, h1, h2, h3, h4, h5, h6, h7, h8]

/-! ## The char-0 Gaussian energy bound: `E_10(ℂ) ≤ 19‼·n^10` for `n ≥ 2` -/

/-- Base case `n=2`. -/
theorem E10_le_wick_base_two : E10 2 ≤ wick 10 2 := by rw [E10_two, wick_ten]; norm_num

/-- The depth-10 char-0 Wick/Gaussian bound on the dyadic support range: `n = 2` or
`n ≥ 4`.  (The integer `n = 3` is not a dyadic subgroup size and the polynomial bound is not
claimed there.) -/
theorem E10_le_wick (n : ℤ) (hn : n = 2 ∨ 4 ≤ n) : E10 n ≤ wick 10 n := by
  rcases hn with rfl | hge
  · exact E10_le_wick_base_two
  · have hpos := deficit_ten_scaled_nonneg n hge
    linarith

/-! ## The Wick cushion is strictly positive -/

/-- The depth-10 char-0 Wick deficit is strictly positive on the dyadic support range: `n = 2` or
`n ≥ 4`. -/
theorem deficit_ten_pos (n : ℤ) (hn : n = 2 ∨ 4 ≤ n) : 0 < wick 10 n - E10 n := by
  rcases hn with rfl | hge
  · rw [deficit_ten]; norm_num
  · have hu0 : (0 : ℤ) ≤ 2 * n - 7 := by linarith
    have hn0 : (0 : ℤ) ≤ n := by linarith
    have hcert := deficit_ten_factored_u n
    have hstrict : (0 : ℤ) < n * 12017417276419555 := by positivity
    have h1 : (0 : ℤ) ≤ n * (18693465128957476 * (2 * n - 7)) :=
      mul_nonneg hn0 (mul_nonneg (by norm_num) hu0)
    have h2 : (0 : ℤ) ≤ n * (9189049903090200 * (2 * n - 7) ^ 2) :=
      mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 2))
    have h3 : (0 : ℤ) ≤ n * (3190736872880700 * (2 * n - 7) ^ 3) :=
      mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 3))
    have h4 : (0 : ℤ) ≤ n * (748576631152350 * (2 * n - 7) ^ 4) :=
      mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 4))
    have h5 : (0 : ℤ) ≤ n * (84892521053340 * (2 * n - 7) ^ 5) :=
      mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 5))
    have h6 : (0 : ℤ) ≤ n * (11366096742000 * (2 * n - 7) ^ 6) :=
      mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 6))
    have h7 : (0 : ℤ) ≤ n * (405932026500 * (2 * n - 7) ^ 7) :=
      mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 7))
    have h8 : (0 : ℤ) ≤ n * (29462808375 * (2 * n - 7) ^ 8) :=
      mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 8))
    nlinarith [hcert, hstrict, h1, h2, h3, h4, h5, h6, h7, h8]

/-- The second coefficient law at depth 10: `29462808375 = C(10,2)·19‼`. -/
theorem deficit_ten_leading : (29462808375 : ℤ) = 45 * 654729075 := by norm_num

end ProximityGap.Frontier.E10ClosedForm

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.E10ClosedForm.E10_two
#print axioms ProximityGap.Frontier.E10ClosedForm.deficit_ten
#print axioms ProximityGap.Frontier.E10ClosedForm.E10_le_wick
#print axioms ProximityGap.Frontier.E10ClosedForm.deficit_ten_pos
