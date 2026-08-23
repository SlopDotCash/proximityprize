/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# The char-0 additive energy `E_13(μ_n)`: exact closed form (#444, avenue L2)

This extends the verified char-0 closed-form ladder one rung beyond `E_12`. It records the exact
cross-polytope / Lam--Leung polynomial at depth `r = 13`, plus the Wick bound and strict positive
cushion. This is deliberately only a char-0 rung; it does not assert the char-p transfer that forms
the #444 BGK/Paley wall.
-/

namespace ProximityGap.Frontier.E13ClosedForm

/-- `E_13(ℂ)(n)`: the char-0 additive energy of `μ_n` at depth `r = 13`, in closed form. -/
def E13 (n : ℤ) : ℤ :=
  7905853580625 * n ^ 13
    - 616656579288750 * n ^ 12
    + 22987586927930625 * n ^ 11
    - 537005104463953125 * n ^ 10
    + 8688780274795495875 * n ^ 9
    - 101846616937902837000 * n ^ 8
    + 880644996980437689000 * n ^ 7
    - 5620110338252149740000 * n ^ 6
    + 26078420548611176470725 * n ^ 5
    - 85107377322443444868900 * n ^ 4
    + 183664732482517536434275 * n ^ 3
    - 232555565902436274006600 * n ^ 2
    + 128603419766365298832000 * n

/-- The Wick leading term `(2r−1)‼·n^r`. -/
def wick (r : ℕ) (n : ℤ) : ℤ := (Nat.doubleFactorial (2 * r - 1) : ℤ) * n ^ r

@[simp] theorem wick_thirteen (n : ℤ) : wick 13 n = 7905853580625 * n ^ 13 := by
  simp [wick, Nat.doubleFactorial]

/-! ## Small-case exact values -/

/-- `E_13(2) = 10400600 = C(26,13)`. -/
theorem E13_two : E13 2 = 10400600 := by decide

/-- `E_13(4) = 108172480360000`. -/
theorem E13_four : E13 4 = 108172480360000 := by decide

/-! ## The exact char-0 deficit `D_13 = wick 13 n − E_13(ℂ)` -/

/-- The exact deficit `wick 13 n − E_13(ℂ)`. Its leading nonzero coefficient is
`C(13,2)·25‼ = 616656579288750`. -/
theorem deficit_thirteen (n : ℤ) :
    wick 13 n - E13 n =
      616656579288750 * n ^ 12
    - 22987586927930625 * n ^ 11
    + 537005104463953125 * n ^ 10
    - 8688780274795495875 * n ^ 9
    + 101846616937902837000 * n ^ 8
    - 880644996980437689000 * n ^ 7
    + 5620110338252149740000 * n ^ 6
    - 26078420548611176470725 * n ^ 5
    + 85107377322443444868900 * n ^ 4
    - 183664732482517536434275 * n ^ 3
    + 232555565902436274006600 * n ^ 2
    - 128603419766365298832000 * n := by
  simp only [wick_thirteen, E13]; ring

/-- `wick 13 n − E_13 = n · (Σ_k c_k · (n-4)^k)` with all `c_k ≥ 0`. -/
theorem deficit_thirteen_factored_u (n : ℤ) :
    wick 13 n - E13 n =
      n * (132638186143398950000
        + 255564296736886774000 * (n - 4) ^ 1
        + 736320875649522178925 * (n - 4) ^ 2
        + 377846491548707481300 * (n - 4) ^ 3
        + 250099644494193769275 * (n - 4) ^ 4
        + 121172326130795940000 * (n - 4) ^ 5
        + 21346310307677355000 * (n - 4) ^ 6
        + 8671068527490369000 * (n - 4) ^ 7
        + 604234375085966625 * (n - 4) ^ 8
        + 160159417120828125 * (n - 4) ^ 9
        + 4145302560774375 * (n - 4) ^ 10
        + 616656579288750 * (n - 4) ^ 11) := by
  rw [deficit_thirteen]; ring

/-- `0 ≤ wick 13 n − E13 n` for `n ≥ 4`, from the nonnegative `u = n−4` certificate. -/
theorem deficit_thirteen_nonneg (n : ℤ) (hn : 4 ≤ n) :
    0 ≤ wick 13 n - E13 n := by
  have hu0 : (0 : ℤ) ≤ n - 4 := by linarith
  have hn0 : (0 : ℤ) ≤ n := by linarith
  rw [deficit_thirteen_factored_u]
  have h0 : (0 : ℤ) ≤ n * 132638186143398950000 :=
    by positivity
  have h1 : (0 : ℤ) ≤ n * (255564296736886774000 * (n - 4) ^ 1) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 1))
  have h2 : (0 : ℤ) ≤ n * (736320875649522178925 * (n - 4) ^ 2) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 2))
  have h3 : (0 : ℤ) ≤ n * (377846491548707481300 * (n - 4) ^ 3) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 3))
  have h4 : (0 : ℤ) ≤ n * (250099644494193769275 * (n - 4) ^ 4) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 4))
  have h5 : (0 : ℤ) ≤ n * (121172326130795940000 * (n - 4) ^ 5) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 5))
  have h6 : (0 : ℤ) ≤ n * (21346310307677355000 * (n - 4) ^ 6) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 6))
  have h7 : (0 : ℤ) ≤ n * (8671068527490369000 * (n - 4) ^ 7) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 7))
  have h8 : (0 : ℤ) ≤ n * (604234375085966625 * (n - 4) ^ 8) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 8))
  have h9 : (0 : ℤ) ≤ n * (160159417120828125 * (n - 4) ^ 9) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 9))
  have h10 : (0 : ℤ) ≤ n * (4145302560774375 * (n - 4) ^ 10) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 10))
  have h11 : (0 : ℤ) ≤ n * (616656579288750 * (n - 4) ^ 11) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 11))
  nlinarith [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]

/-! ## The char-0 Gaussian energy bound: `E_13(ℂ) ≤ 25‼·n^13` on the dyadic support range -/

/-- Base case `n=2`. -/
theorem E13_le_wick_base_two : E13 2 ≤ wick 13 2 := by rw [E13_two, wick_thirteen]; norm_num

/-- The depth-13 char-0 Wick/Gaussian bound on the dyadic support range: `n = 2` or
`n ≥ 4`. The interpolation polynomial is not an additive-energy value at odd `n=3`, so this API
keeps the same dyadic-domain guard as the previous rungs. -/
theorem E13_le_wick (n : ℤ) (hn : n = 2 ∨ 4 ≤ n) : E13 n ≤ wick 13 n := by
  rcases hn with rfl | hge
  · exact E13_le_wick_base_two
  · have hpos := deficit_thirteen_nonneg n hge
    linarith

/-! ## The Wick cushion is strictly positive -/

/-- The depth-13 char-0 Wick deficit is strictly positive on the dyadic support range: `n = 2` or
`n ≥ 4`. -/
theorem deficit_thirteen_pos (n : ℤ) (hn : n = 2 ∨ 4 ≤ n) : 0 < wick 13 n - E13 n := by
  rcases hn with rfl | hge
  · rw [deficit_thirteen]; norm_num
  · have hu0 : (0 : ℤ) ≤ n - 4 := by linarith
    have hn0 : (0 : ℤ) ≤ n := by linarith
    have hcert := deficit_thirteen_factored_u n
    have hstrict : (0 : ℤ) < n * 132638186143398950000 := by positivity
    have h1 : (0 : ℤ) ≤ n * (255564296736886774000 * (n - 4) ^ 1) :=
      mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 1))
    have h2 : (0 : ℤ) ≤ n * (736320875649522178925 * (n - 4) ^ 2) :=
      mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 2))
    have h3 : (0 : ℤ) ≤ n * (377846491548707481300 * (n - 4) ^ 3) :=
      mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 3))
    have h4 : (0 : ℤ) ≤ n * (250099644494193769275 * (n - 4) ^ 4) :=
      mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 4))
    have h5 : (0 : ℤ) ≤ n * (121172326130795940000 * (n - 4) ^ 5) :=
      mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 5))
    have h6 : (0 : ℤ) ≤ n * (21346310307677355000 * (n - 4) ^ 6) :=
      mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 6))
    have h7 : (0 : ℤ) ≤ n * (8671068527490369000 * (n - 4) ^ 7) :=
      mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 7))
    have h8 : (0 : ℤ) ≤ n * (604234375085966625 * (n - 4) ^ 8) :=
      mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 8))
    have h9 : (0 : ℤ) ≤ n * (160159417120828125 * (n - 4) ^ 9) :=
      mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 9))
    have h10 : (0 : ℤ) ≤ n * (4145302560774375 * (n - 4) ^ 10) :=
      mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 10))
    have h11 : (0 : ℤ) ≤ n * (616656579288750 * (n - 4) ^ 11) :=
      mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 11))
    nlinarith [hcert, hstrict, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]

/-- The second coefficient law at depth 13: `616656579288750 = C(13,2)·25‼`. -/
theorem deficit_thirteen_leading : (616656579288750 : ℤ) = 78 * 7905853580625 := by norm_num

end ProximityGap.Frontier.E13ClosedForm

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.E13ClosedForm.E13_two
#print axioms ProximityGap.Frontier.E13ClosedForm.deficit_thirteen
#print axioms ProximityGap.Frontier.E13ClosedForm.E13_le_wick
#print axioms ProximityGap.Frontier.E13ClosedForm.deficit_thirteen_pos
