/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# The char-0 additive energy `E_14(μ_n)`: exact closed form (#444, avenue L2)

This extends the verified char-0 closed-form ladder one rung beyond `E_13`. It records the exact
cross-polytope / Lam--Leung polynomial at depth `r = 14`, plus the Wick bound and strict positive
cushion. This is deliberately only a char-0 rung; it does not assert the char-p transfer that forms
the #444 BGK/Paley wall.
-/

namespace ProximityGap.Frontier.E14ClosedForm

/-- `E_14(ℂ)(n)`: the char-0 additive energy of `μ_n` at depth `r = 14`, in closed form. -/
def E14 (n : ℤ) : ℤ :=
  213458046676875 * n ^ 14
    - 19424682247595625 * n ^ 13
    + 848211124811675625 * n ^ 12
    - 23361417849775005000 * n ^ 11
    + 449764272676095126750 * n ^ 10
    - 6351869799984952868625 * n ^ 9
    + 67290258079078833298500 * n ^ 8
    - 538154693788766643839250 * n ^ 7
    + 3228878336452074422441325 * n ^ 6
    - 14258326366170820436528025 * n ^ 5
    + 44702834263994543953086225 * n ^ 4
    - 93388658639338547683809975 * n ^ 3
    + 115215349274185348158559200 * n ^ 2
    - 62442813510816426879048000 * n ^ 1

/-- The Wick leading term `(2r−1)‼·n^r`. -/
def wick (r : ℕ) (n : ℤ) : ℤ := (Nat.doubleFactorial (2 * r - 1) : ℤ) * n ^ r

@[simp] theorem wick_fourteen (n : ℤ) : wick 14 n = 213458046676875 * n ^ 14 := by
  simp [wick, Nat.doubleFactorial]

/-! ## Small-case exact values -/

/-- `E_14(2) = 40116600 = C(28,14)`. -/
theorem E14_two : E14 2 = 40116600 := by decide

/-- `E_14(4) = 1609341595560000`. -/
theorem E14_four : E14 4 = 1609341595560000 := by decide

/-! ## The exact char-0 deficit `D_14 = wick 14 n − E_14(ℂ)` -/

/-- The exact deficit `wick 14 n − E_14(ℂ)`. Its leading nonzero coefficient is
`C(14,2)·27‼ = 19424682247595625`. -/
theorem deficit_fourteen (n : ℤ) :
    wick 14 n - E14 n =
      19424682247595625 * n ^ 13
        - 848211124811675625 * n ^ 12
        + 23361417849775005000 * n ^ 11
        - 449764272676095126750 * n ^ 10
        + 6351869799984952868625 * n ^ 9
        - 67290258079078833298500 * n ^ 8
        + 538154693788766643839250 * n ^ 7
        - 3228878336452074422441325 * n ^ 6
        + 14258326366170820436528025 * n ^ 5
        - 44702834263994543953086225 * n ^ 4
        + 93388658639338547683809975 * n ^ 3
        - 115215349274185348158559200 * n ^ 2
        + 62442813510816426879048000 * n ^ 1 := by
  simp only [wick_fourteen, E14]; ring

/-- `wick 14 n − E_14 = n · (Σ_k c_k · (n-5)^k)` with all `c_k ≥ 0`. -/
theorem deficit_fourteen_factored_v (n : ℤ) :
    wick 14 n - E14 n =
      n * (        271042563002800123551375
        + 664596705852183605992425 * (n - 5) ^ 1
        + 808575909331272545142225 * (n - 5) ^ 2
        + 608032889489174985189900 * (n - 5) ^ 3
        + 291774089807695730760525 * (n - 5) ^ 4
        + 108523825880228576242425 * (n - 5) ^ 5
        + 28804789197250214148000 * (n - 5) ^ 6
        + 5550500328849816590250 * (n - 5) ^ 7
        + 909229231666639508625 * (n - 5) ^ 8
        + 86195085005480826375 * (n - 5) ^ 9
        + 8760531693665626875 * (n - 5) ^ 10
        + 317269810044061875 * (n - 5) ^ 11
        + 19424682247595625 * (n - 5) ^ 12) := by
  rw [deficit_fourteen]; ring_nf

/-- `0 ≤ wick 14 n − E14 n` for `n ≥ 5`, from the nonnegative `v = n−5` certificate. -/
theorem deficit_fourteen_nonneg_from_five (n : ℤ) (hn : 5 ≤ n) :
    0 ≤ wick 14 n - E14 n := by
  have hu0 : (0 : ℤ) ≤ n - 5 := by linarith
  have hn0 : (0 : ℤ) ≤ n := by linarith
  rw [deficit_fourteen_factored_v]
  have h0 : (0 : ℤ) ≤ n * 271042563002800123551375 := by positivity
  have h1 : (0 : ℤ) ≤ n * (664596705852183605992425 * (n - 5) ^ 1) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 1))
  have h2 : (0 : ℤ) ≤ n * (808575909331272545142225 * (n - 5) ^ 2) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 2))
  have h3 : (0 : ℤ) ≤ n * (608032889489174985189900 * (n - 5) ^ 3) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 3))
  have h4 : (0 : ℤ) ≤ n * (291774089807695730760525 * (n - 5) ^ 4) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 4))
  have h5 : (0 : ℤ) ≤ n * (108523825880228576242425 * (n - 5) ^ 5) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 5))
  have h6 : (0 : ℤ) ≤ n * (28804789197250214148000 * (n - 5) ^ 6) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 6))
  have h7 : (0 : ℤ) ≤ n * (5550500328849816590250 * (n - 5) ^ 7) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 7))
  have h8 : (0 : ℤ) ≤ n * (909229231666639508625 * (n - 5) ^ 8) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 8))
  have h9 : (0 : ℤ) ≤ n * (86195085005480826375 * (n - 5) ^ 9) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 9))
  have h10 : (0 : ℤ) ≤ n * (8760531693665626875 * (n - 5) ^ 10) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 10))
  have h11 : (0 : ℤ) ≤ n * (317269810044061875 * (n - 5) ^ 11) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 11))
  have h12 : (0 : ℤ) ≤ n * (19424682247595625 * (n - 5) ^ 12) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 12))
  nlinarith [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]

/-- Base case `n=2`. -/
theorem E14_le_wick_base_two : E14 2 ≤ wick 14 2 := by rw [E14_two, wick_fourteen]; norm_num

/-- Base case `n=4`. -/
theorem E14_le_wick_base_four : E14 4 ≤ wick 14 4 := by rw [E14_four, wick_fourteen]; norm_num

/-- The depth-14 char-0 Wick/Gaussian bound on the dyadic support range: `n = 2` or
`n ≥ 4`. The shifted positivity certificate starts at `n = 5`, so `n = 4` is kept as an
explicit dyadic base case. -/
theorem E14_le_wick (n : ℤ) (hn : n = 2 ∨ 4 ≤ n) : E14 n ≤ wick 14 n := by
  rcases hn with rfl | hge
  · exact E14_le_wick_base_two
  · by_cases h4 : n = 4
    · subst n
      exact E14_le_wick_base_four
    · have h5 : 5 ≤ n := by omega
      have hpos := deficit_fourteen_nonneg_from_five n h5
      linarith

/-! ## The Wick cushion is strictly positive -/

/-- The depth-14 char-0 Wick deficit is strictly positive on the dyadic support range: `n = 2` or
`n ≥ 4`. -/
theorem deficit_fourteen_pos (n : ℤ) (hn : n = 2 ∨ 4 ≤ n) : 0 < wick 14 n - E14 n := by
  rcases hn with rfl | hge
  · rw [deficit_fourteen]; norm_num
  · by_cases hn4 : n = 4
    · subst n
      rw [deficit_fourteen]
      norm_num
    · have hn5 : 5 ≤ n := by omega
      have hu0 : (0 : ℤ) ≤ n - 5 := by linarith
      have hn0 : (0 : ℤ) ≤ n := by linarith
      have hcert := deficit_fourteen_factored_v n
      have hstrict : (0 : ℤ) < n * 271042563002800123551375 := by positivity
      have h1 : (0 : ℤ) ≤ n * (664596705852183605992425 * (n - 5) ^ 1) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 1))
      have h2 : (0 : ℤ) ≤ n * (808575909331272545142225 * (n - 5) ^ 2) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 2))
      have h3 : (0 : ℤ) ≤ n * (608032889489174985189900 * (n - 5) ^ 3) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 3))
      have h4 : (0 : ℤ) ≤ n * (291774089807695730760525 * (n - 5) ^ 4) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 4))
      have h5 : (0 : ℤ) ≤ n * (108523825880228576242425 * (n - 5) ^ 5) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 5))
      have h6 : (0 : ℤ) ≤ n * (28804789197250214148000 * (n - 5) ^ 6) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 6))
      have h7 : (0 : ℤ) ≤ n * (5550500328849816590250 * (n - 5) ^ 7) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 7))
      have h8 : (0 : ℤ) ≤ n * (909229231666639508625 * (n - 5) ^ 8) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 8))
      have h9 : (0 : ℤ) ≤ n * (86195085005480826375 * (n - 5) ^ 9) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 9))
      have h10 : (0 : ℤ) ≤ n * (8760531693665626875 * (n - 5) ^ 10) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 10))
      have h11 : (0 : ℤ) ≤ n * (317269810044061875 * (n - 5) ^ 11) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 11))
      have h12 : (0 : ℤ) ≤ n * (19424682247595625 * (n - 5) ^ 12) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 12))
      nlinarith [hcert, hstrict, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]

/-- The second coefficient law at depth 14: `19424682247595625 = C(14,2)·27‼`. -/
theorem deficit_fourteen_leading : (19424682247595625 : ℤ) = 91 * 213458046676875 := by norm_num

end ProximityGap.Frontier.E14ClosedForm

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.E14ClosedForm.E14_two
#print axioms ProximityGap.Frontier.E14ClosedForm.deficit_fourteen
#print axioms ProximityGap.Frontier.E14ClosedForm.E14_le_wick
#print axioms ProximityGap.Frontier.E14ClosedForm.deficit_fourteen_pos
