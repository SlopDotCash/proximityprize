/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# The char-0 additive energy `E_12(μ_n)`: exact closed form (#444, avenue L2)

This extends the verified char-0 closed-form ladder one rung beyond `E_11`. It records the exact
cross-polytope / Lam--Leung polynomial at depth `r = 12`, plus the Wick bound and strict positive
cushion. This is deliberately only a char-0 rung; it does not assert the char-p transfer that forms
the #444 BGK/Paley wall.
-/

namespace ProximityGap.Frontier.E12ClosedForm

/-- `E_12(ℂ)(n)`: the char-0 additive energy of `μ_n` at depth `r = 12`, in closed form. -/
def E12 (n : ℤ) : ℤ :=
  316234143225 * n ^ 12
    - 20871453452850 * n ^ 11
    + 655131733381125 * n ^ 10
    - 12783765239870625 * n ^ 9
    + 170783914548482235 * n ^ 8
    - 1626536485704590460 * n ^ 7
    + 11177506206789822900 * n ^ 6
    - 54962697790085085000 * n ^ 5
    + 187825280893260359349 * n ^ 4
    - 420483866127150253428 * n ^ 3
    + 548071370395459025479 * n ^ 2
    - 309890622206697331800 * n

/-- The Wick leading term `(2r−1)‼·n^r`. -/
def wick (r : ℕ) (n : ℤ) : ℤ := (Nat.doubleFactorial (2 * r - 1) : ℤ) * n ^ r

@[simp] theorem wick_twelve (n : ℤ) : wick 12 n = 316234143225 * n ^ 12 := by
  simp [wick, Nat.doubleFactorial]

/-! ## Small-case exact values -/

/-- `E_12(2) = 2704156 = C(24,12)`. -/
theorem E12_two : E12 2 = 2704156 := by decide

/-- `E_12(4) = 7312459672336`. -/
theorem E12_four : E12 4 = 7312459672336 := by decide

/-! ## The exact char-0 deficit `D_12 = wick 12 n − E_12(ℂ)` -/

/-- The exact deficit `wick 12 n − E_12(ℂ)`. Its leading nonzero coefficient is
`C(12,2)·23‼ = 20871453452850`. -/
theorem deficit_twelve (n : ℤ) :
    wick 12 n - E12 n =
      20871453452850 * n ^ 11
    - 655131733381125 * n ^ 10
    + 12783765239870625 * n ^ 9
    - 170783914548482235 * n ^ 8
    + 1626536485704590460 * n ^ 7
    - 11177506206789822900 * n ^ 6
    + 54962697790085085000 * n ^ 5
    - 187825280893260359349 * n ^ 4
    + 420483866127150253428 * n ^ 3
    - 548071370395459025479 * n ^ 2
    + 309890622206697331800 * n := by
  simp only [wick_twelve, E12]; ring

/-- `wick 12 n − E_12 = n · (Σ_k c_k · (n-4)^k)` with all `c_k ≥ 0`. -/
theorem deficit_twelve_factored_u (n : ℤ) :
    wick 12 n - E12 n =
      n * (1326380303750272316
        + 4047056500948337513 * (n - 4) ^ 1
        + 4042786693135390200 * (n - 4) ^ 2
        + 3619654414881355851 * (n - 4) ^ 3
        + 1735507367508915000 * (n - 4) ^ 4
        + 546896410186105980 * (n - 4) ^ 5
        + 171774844777415880 * (n - 4) ^ 6
        + 21233457217737765 * (n - 4) ^ 7
        + 4226469324202125 * (n - 4) ^ 8
        + 179726404732875 * (n - 4) ^ 9
        + 20871453452850 * (n - 4) ^ 10) := by
  rw [deficit_twelve]; ring

/-- `0 ≤ wick 12 n − E12 n` for `n ≥ 4`, from the nonnegative `u = n−4` certificate. -/
theorem deficit_twelve_nonneg (n : ℤ) (hn : 4 ≤ n) :
    0 ≤ wick 12 n - E12 n := by
  have hu0 : (0 : ℤ) ≤ n - 4 := by linarith
  have hn0 : (0 : ℤ) ≤ n := by linarith
  rw [deficit_twelve_factored_u]
  have h0 : (0 : ℤ) ≤ n * 1326380303750272316 :=
    by positivity
  have h1 : (0 : ℤ) ≤ n * (4047056500948337513 * (n - 4) ^ 1) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 1))
  have h2 : (0 : ℤ) ≤ n * (4042786693135390200 * (n - 4) ^ 2) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 2))
  have h3 : (0 : ℤ) ≤ n * (3619654414881355851 * (n - 4) ^ 3) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 3))
  have h4 : (0 : ℤ) ≤ n * (1735507367508915000 * (n - 4) ^ 4) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 4))
  have h5 : (0 : ℤ) ≤ n * (546896410186105980 * (n - 4) ^ 5) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 5))
  have h6 : (0 : ℤ) ≤ n * (171774844777415880 * (n - 4) ^ 6) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 6))
  have h7 : (0 : ℤ) ≤ n * (21233457217737765 * (n - 4) ^ 7) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 7))
  have h8 : (0 : ℤ) ≤ n * (4226469324202125 * (n - 4) ^ 8) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 8))
  have h9 : (0 : ℤ) ≤ n * (179726404732875 * (n - 4) ^ 9) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 9))
  have h10 : (0 : ℤ) ≤ n * (20871453452850 * (n - 4) ^ 10) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 10))
  nlinarith [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]

/-! ## The char-0 Gaussian energy bound: `E_12(ℂ) ≤ 23‼·n^12` on the dyadic support range -/

/-- Base case `n=2`. -/
theorem E12_le_wick_base_two : E12 2 ≤ wick 12 2 := by rw [E12_two, wick_twelve]; norm_num

/-- The depth-12 char-0 Wick/Gaussian bound on the dyadic support range: `n = 2` or
`n ≥ 4`. The interpolation polynomial is not an additive-energy value at odd `n=3`, so this API
keeps the same dyadic-domain guard as the `E10` and `E11` rungs. -/
theorem E12_le_wick (n : ℤ) (hn : n = 2 ∨ 4 ≤ n) : E12 n ≤ wick 12 n := by
  rcases hn with rfl | hge
  · exact E12_le_wick_base_two
  · have hpos := deficit_twelve_nonneg n hge
    linarith

/-! ## The Wick cushion is strictly positive -/

/-- The depth-12 char-0 Wick deficit is strictly positive on the dyadic support range: `n = 2` or
`n ≥ 4`. -/
theorem deficit_twelve_pos (n : ℤ) (hn : n = 2 ∨ 4 ≤ n) : 0 < wick 12 n - E12 n := by
  rcases hn with rfl | hge
  · rw [deficit_twelve]; norm_num
  · have hu0 : (0 : ℤ) ≤ n - 4 := by linarith
    have hn0 : (0 : ℤ) ≤ n := by linarith
    have hcert := deficit_twelve_factored_u n
    have hstrict : (0 : ℤ) < n * 1326380303750272316 := by positivity
    have h1 : (0 : ℤ) ≤ n * (4047056500948337513 * (n - 4) ^ 1) :=
      mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 1))
    have h2 : (0 : ℤ) ≤ n * (4042786693135390200 * (n - 4) ^ 2) :=
      mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 2))
    have h3 : (0 : ℤ) ≤ n * (3619654414881355851 * (n - 4) ^ 3) :=
      mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 3))
    have h4 : (0 : ℤ) ≤ n * (1735507367508915000 * (n - 4) ^ 4) :=
      mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 4))
    have h5 : (0 : ℤ) ≤ n * (546896410186105980 * (n - 4) ^ 5) :=
      mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 5))
    have h6 : (0 : ℤ) ≤ n * (171774844777415880 * (n - 4) ^ 6) :=
      mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 6))
    have h7 : (0 : ℤ) ≤ n * (21233457217737765 * (n - 4) ^ 7) :=
      mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 7))
    have h8 : (0 : ℤ) ≤ n * (4226469324202125 * (n - 4) ^ 8) :=
      mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 8))
    have h9 : (0 : ℤ) ≤ n * (179726404732875 * (n - 4) ^ 9) :=
      mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 9))
    have h10 : (0 : ℤ) ≤ n * (20871453452850 * (n - 4) ^ 10) :=
      mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 10))
    nlinarith [hcert, hstrict, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]

/-- The second coefficient law at depth 12: `20871453452850 = C(12,2)·23‼`. -/
theorem deficit_twelve_leading : (20871453452850 : ℤ) = 66 * 316234143225 := by norm_num

end ProximityGap.Frontier.E12ClosedForm

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.E12ClosedForm.E12_two
#print axioms ProximityGap.Frontier.E12ClosedForm.deficit_twelve
#print axioms ProximityGap.Frontier.E12ClosedForm.E12_le_wick
#print axioms ProximityGap.Frontier.E12ClosedForm.deficit_twelve_pos
