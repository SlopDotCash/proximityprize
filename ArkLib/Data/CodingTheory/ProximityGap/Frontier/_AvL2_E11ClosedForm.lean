/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# The char-0 additive energy `E_11(μ_n)`: exact closed form (#444, avenue L2)

This extends the verified char-0 closed-form ladder one rung beyond `E_10`.  It records the exact
cross-polytope / Lam--Leung polynomial at depth `r = 11`, plus the Wick bound and strict positive
cushion.  This is deliberately only a char-0 rung; it does not assert the char-p transfer that forms
the #444 BGK/Paley wall.
-/

namespace ProximityGap.Frontier.E11ClosedForm

/-- `E_11(ℂ)(n)`: the char-0 additive energy of `μ_n` at depth `r = 11`, in closed form. -/
def E11 (n : ℤ) : ℤ :=
  13749310575 * n ^ 11 - 756212081625 * n ^ 10 + 19661514122250 * n ^ 9
    - 314584225956000 * n ^ 8 + 3394676365725645 * n ^ 7
    - 25563648591055575 * n ^ 6 + 134741797483968675 * n ^ 5
    - 485904205885398300 * n ^ 4 + 1134491936485430523 * n ^ 3
    - 1527835493738642088 * n ^ 2 + 885452130981774720 * n

/-- The Wick leading term `(2r−1)‼·n^r`. -/
def wick (r : ℕ) (n : ℤ) : ℤ := (Nat.doubleFactorial (2 * r - 1) : ℤ) * n ^ r

@[simp] theorem wick_eleven (n : ℤ) : wick 11 n = 13749310575 * n ^ 11 := by
  simp [wick, Nat.doubleFactorial]

/-! ## Small-case exact values -/

/-- `E_11(2) = 705432 = C(22,11)`. -/
theorem E11_two : E11 2 = 705432 := by decide

/-- `E_11(4) = 497634306624`. -/
theorem E11_four : E11 4 = 497634306624 := by decide

/-! ## The exact char-0 deficit `D_11 = wick 11 n − E_11(ℂ)` -/

/-- The exact deficit `wick 11 n − E_11(ℂ)`.  Its leading nonzero coefficient is
`C(11,2)·21‼ = 756212081625`. -/
theorem deficit_eleven (n : ℤ) :
    wick 11 n - E11 n =
      756212081625 * n ^ 10 - 19661514122250 * n ^ 9 + 314584225956000 * n ^ 8
        - 3394676365725645 * n ^ 7 + 25563648591055575 * n ^ 6
        - 134741797483968675 * n ^ 5 + 485904205885398300 * n ^ 4
        - 1134491936485430523 * n ^ 3 + 1527835493738642088 * n ^ 2
        - 885452130981774720 * n := by
  simp only [wick_eleven, E11]; ring

/-- `512·(wick 11 n − E_11) = n · (Σ_k c_k · u^k)` with `u = 2n − 7` and all `c_k ≥ 0`. -/
theorem deficit_eleven_factored_u (n : ℤ) :
    512 * (wick 11 n - E11 n) =
      n * (2534264685779243235 + 1912838307499536417 * (2 * n - 7)
        + 2057584878805411956 * (2 * n - 7) ^ 2
        + 695484743286633300 * (2 * n - 7) ^ 3
        + 141938547831130050 * (2 * n - 7) ^ 4
        + 36692882293297230 * (2 * n - 7) ^ 5
        + 2337885105896340 * (2 * n - 7) ^ 6
        + 390205434118500 * (2 * n - 7) ^ 7
        + 8318332897875 * (2 * n - 7) ^ 8
        + 756212081625 * (2 * n - 7) ^ 9) := by
  rw [deficit_eleven]; ring

/-- `0 ≤ 512·(wick 11 n − E11 n)` for `n ≥ 4`, from the nonnegative `u = 2n−7` certificate. -/
theorem deficit_eleven_scaled_nonneg (n : ℤ) (hn : 4 ≤ n) :
    0 ≤ 512 * (wick 11 n - E11 n) := by
  have hu0 : (0 : ℤ) ≤ 2 * n - 7 := by linarith
  have hn0 : (0 : ℤ) ≤ n := by linarith
  rw [deficit_eleven_factored_u]
  have h0 : (0 : ℤ) ≤ n * 2534264685779243235 := by positivity
  have h1 : (0 : ℤ) ≤ n * (1912838307499536417 * (2 * n - 7)) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) hu0)
  have h2 : (0 : ℤ) ≤ n * (2057584878805411956 * (2 * n - 7) ^ 2) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 2))
  have h3 : (0 : ℤ) ≤ n * (695484743286633300 * (2 * n - 7) ^ 3) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 3))
  have h4 : (0 : ℤ) ≤ n * (141938547831130050 * (2 * n - 7) ^ 4) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 4))
  have h5 : (0 : ℤ) ≤ n * (36692882293297230 * (2 * n - 7) ^ 5) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 5))
  have h6 : (0 : ℤ) ≤ n * (2337885105896340 * (2 * n - 7) ^ 6) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 6))
  have h7 : (0 : ℤ) ≤ n * (390205434118500 * (2 * n - 7) ^ 7) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 7))
  have h8 : (0 : ℤ) ≤ n * (8318332897875 * (2 * n - 7) ^ 8) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 8))
  have h9 : (0 : ℤ) ≤ n * (756212081625 * (2 * n - 7) ^ 9) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 9))
  nlinarith [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]

/-! ## The char-0 Gaussian energy bound: `E_11(ℂ) ≤ 21‼·n^11` on the dyadic support range -/

/-- Base case `n=2`. -/
theorem E11_le_wick_base_two : E11 2 ≤ wick 11 2 := by rw [E11_two, wick_eleven]; norm_num

/-- The depth-11 char-0 Wick/Gaussian bound on the dyadic support range: `n = 2` or
`n ≥ 4`.  The interpolation polynomial is not an additive-energy value at odd `n=3`, so this API
keeps the same dyadic-domain guard as the `E10` rung. -/
theorem E11_le_wick (n : ℤ) (hn : n = 2 ∨ 4 ≤ n) : E11 n ≤ wick 11 n := by
  rcases hn with rfl | hge
  · exact E11_le_wick_base_two
  · have hpos := deficit_eleven_scaled_nonneg n hge
    linarith

/-! ## The Wick cushion is strictly positive -/

/-- The depth-11 char-0 Wick deficit is strictly positive on the dyadic support range: `n = 2` or
`n ≥ 4`. -/
theorem deficit_eleven_pos (n : ℤ) (hn : n = 2 ∨ 4 ≤ n) : 0 < wick 11 n - E11 n := by
  rcases hn with rfl | hge
  · rw [deficit_eleven]; norm_num
  · have hu0 : (0 : ℤ) ≤ 2 * n - 7 := by linarith
    have hn0 : (0 : ℤ) ≤ n := by linarith
    have hcert := deficit_eleven_factored_u n
    have hstrict : (0 : ℤ) < n * 2534264685779243235 := by positivity
    have h1 : (0 : ℤ) ≤ n * (1912838307499536417 * (2 * n - 7)) :=
      mul_nonneg hn0 (mul_nonneg (by norm_num) hu0)
    have h2 : (0 : ℤ) ≤ n * (2057584878805411956 * (2 * n - 7) ^ 2) :=
      mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 2))
    have h3 : (0 : ℤ) ≤ n * (695484743286633300 * (2 * n - 7) ^ 3) :=
      mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 3))
    have h4 : (0 : ℤ) ≤ n * (141938547831130050 * (2 * n - 7) ^ 4) :=
      mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 4))
    have h5 : (0 : ℤ) ≤ n * (36692882293297230 * (2 * n - 7) ^ 5) :=
      mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 5))
    have h6 : (0 : ℤ) ≤ n * (2337885105896340 * (2 * n - 7) ^ 6) :=
      mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 6))
    have h7 : (0 : ℤ) ≤ n * (390205434118500 * (2 * n - 7) ^ 7) :=
      mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 7))
    have h8 : (0 : ℤ) ≤ n * (8318332897875 * (2 * n - 7) ^ 8) :=
      mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 8))
    have h9 : (0 : ℤ) ≤ n * (756212081625 * (2 * n - 7) ^ 9) :=
      mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 9))
    nlinarith [hcert, hstrict, h1, h2, h3, h4, h5, h6, h7, h8, h9]

/-- The second coefficient law at depth 11: `756212081625 = C(11,2)·21‼`. -/
theorem deficit_eleven_leading : (756212081625 : ℤ) = 55 * 13749310575 := by norm_num

end ProximityGap.Frontier.E11ClosedForm

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.E11ClosedForm.E11_two
#print axioms ProximityGap.Frontier.E11ClosedForm.deficit_eleven
#print axioms ProximityGap.Frontier.E11ClosedForm.E11_le_wick
#print axioms ProximityGap.Frontier.E11ClosedForm.deficit_eleven_pos
