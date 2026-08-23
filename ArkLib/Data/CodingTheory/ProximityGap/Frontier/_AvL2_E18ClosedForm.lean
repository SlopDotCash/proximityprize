/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# The char-0 additive energy `E_18(μ_n)`: exact closed form (#444, avenue L2)

This extends the verified char-0 closed-form ladder one rung beyond `E_17`.  It records the
exact cross-polytope / Lam--Leung polynomial at depth `r = 18`, plus the Wick bound and a
strict positive cushion on the honest dyadic-support-covering range `n = 2`, `n = 4`, or
`n ≥ 6`.  This is deliberately only a char-0 rung; it does not assert the char-p transfer
that forms the #444 BGK/Paley wall.
-/

namespace ProximityGap.Frontier.E18ClosedForm

/-- `E_18(ℂ)(n)`: the char-0 additive energy of `μ_n` at depth `r = 18`, in closed form. -/
def E18 (n : ℤ) : ℤ :=
  221643095476699771875 * n ^ 18
    - 33911393607935065096875 * n ^ 17
    + 2516978992233402609412500 * n ^ 16
    - 119820257414703896675625000 * n ^ 15
    + 4080318854719013389166433750 * n ^ 14
    - 105066182230883577943753263750 * n ^ 13
    + 2110302039678903316931868933750 * n ^ 12
    - 33646729419782706169082352712500 * n ^ 11
    + 429546762267963023066251991747625 * n ^ 10
    - 4399416676109722105503821526244875 * n ^ 9
    + 36008125358542675157133286939716750 * n ^ 8
    - 233204633832551730367720756984429500 * n ^ 7
    + 1175051362815050818135088541230256825 * n ^ 6
    - 4486245856120552985354829414608877825 * n ^ 5
    + 12456491220398423563752229461189492075 * n ^ 4
    - 23524311150279980736656133081485565450 * n ^ 3
    + 26718944072474452549948898601405021825 * n ^ 2
    - 13561372812665358272531083952363556000 * n ^ 1

/-- The Wick leading term `(2r−1)‼·n^r`. -/
def wick (r : ℕ) (n : ℤ) : ℤ := (Nat.doubleFactorial (2 * r - 1) : ℤ) * n ^ r

@[simp] theorem wick_eighteen (n : ℤ) : wick 18 n = 221643095476699771875 * n ^ 18 := by
  simp [wick, Nat.doubleFactorial]

/-! ## Small-case exact values -/

/-- `E_18(2) = 9075135300 = C(36,18)`. -/
theorem E18_two : E18 2 = 9075135300 := by decide

/-- `E_18(4) = 82358080713306090000`. -/
theorem E18_four : E18 4 = 82358080713306090000 := by decide

/-! ## The exact char-0 deficit `D_18 = wick 18 n − E_18(ℂ)` -/

/-- The exact deficit `wick 18 n − E_18(ℂ)`. Its leading nonzero coefficient is
`C(18,2)·35‼ = 33911393607935065096875`. -/
theorem deficit_eighteen (n : ℤ) :
    wick 18 n - E18 n =
      33911393607935065096875 * n ^ 17
        - 2516978992233402609412500 * n ^ 16
        + 119820257414703896675625000 * n ^ 15
        - 4080318854719013389166433750 * n ^ 14
        + 105066182230883577943753263750 * n ^ 13
        - 2110302039678903316931868933750 * n ^ 12
        + 33646729419782706169082352712500 * n ^ 11
        - 429546762267963023066251991747625 * n ^ 10
        + 4399416676109722105503821526244875 * n ^ 9
        - 36008125358542675157133286939716750 * n ^ 8
        + 233204633832551730367720756984429500 * n ^ 7
        - 1175051362815050818135088541230256825 * n ^ 6
        + 4486245856120552985354829414608877825 * n ^ 5
        - 12456491220398423563752229461189492075 * n ^ 4
        + 23524311150279980736656133081485565450 * n ^ 3
        - 26718944072474452549948898601405021825 * n ^ 2
        + 13561372812665358272531083952363556000 * n ^ 1 := by
  simp only [wick_eighteen, E18]; ring

/-- `wick 18 n − E_18 = n · (Σ_k c_k · (n-6)^k)` with all `c_k ≥ 0`. -/
theorem deficit_eighteen_factored_v (n : ℤ) :
    wick 18 n - E18 n =
      n * (        3751677190267453451509612115443050
        + 10092584838014529671582672732866275 * (n - 6) ^ 1
        + 14839059093882366308429205574440300 * (n - 6) ^ 2
        + 11593719854413984142958030625498725 * (n - 6) ^ 3
        + 6819305060115898386953998954101075 * (n - 6) ^ 4
        + 3063239716817280080850154760858175 * (n - 6) ^ 5
        + 968750980296328884384801283212000 * (n - 6) ^ 6
        + 264447714087323300159681720915250 * (n - 6) ^ 7
        + 54597369336614405509891651093125 * (n - 6) ^ 8
        + 8777495657797558500555849477375 * (n - 6) ^ 9
        + 1275822059962688494501260015000 * (n - 6) ^ 10
        + 116858885011909111440605486250 * (n - 6) ^ 11
        + 11951261827580287390359431250 * (n - 6) ^ 12
        + 572324348289677542124816250 * (n - 6) ^ 13
        + 39789368499977143047000000 * (n - 6) ^ 14
        + 738514794128363639887500 * (n - 6) ^ 15
        + 33911393607935065096875 * (n - 6) ^ 16) := by
  rw [deficit_eighteen]; ring_nf

/-- `0 ≤ wick 18 n − E18 n` for `n ≥ 6`, from the nonnegative `v = n−6` certificate. -/
theorem deficit_eighteen_nonneg_from_six (n : ℤ) (hn : 6 ≤ n) :
    0 ≤ wick 18 n - E18 n := by
  have hu0 : (0 : ℤ) ≤ n - 6 := by linarith
  have hn0 : (0 : ℤ) ≤ n := by linarith
  have h0 : (0 : ℤ) ≤ n * 3751677190267453451509612115443050 := by positivity
  have h1 : (0 : ℤ) ≤ n * (10092584838014529671582672732866275 * (n - 6) ^ 1) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 1))
  have h2 : (0 : ℤ) ≤ n * (14839059093882366308429205574440300 * (n - 6) ^ 2) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 2))
  have h3 : (0 : ℤ) ≤ n * (11593719854413984142958030625498725 * (n - 6) ^ 3) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 3))
  have h4 : (0 : ℤ) ≤ n * (6819305060115898386953998954101075 * (n - 6) ^ 4) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 4))
  have h5 : (0 : ℤ) ≤ n * (3063239716817280080850154760858175 * (n - 6) ^ 5) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 5))
  have h6 : (0 : ℤ) ≤ n * (968750980296328884384801283212000 * (n - 6) ^ 6) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 6))
  have h7 : (0 : ℤ) ≤ n * (264447714087323300159681720915250 * (n - 6) ^ 7) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 7))
  have h8 : (0 : ℤ) ≤ n * (54597369336614405509891651093125 * (n - 6) ^ 8) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 8))
  have h9 : (0 : ℤ) ≤ n * (8777495657797558500555849477375 * (n - 6) ^ 9) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 9))
  have h10 : (0 : ℤ) ≤ n * (1275822059962688494501260015000 * (n - 6) ^ 10) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 10))
  have h11 : (0 : ℤ) ≤ n * (116858885011909111440605486250 * (n - 6) ^ 11) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 11))
  have h12 : (0 : ℤ) ≤ n * (11951261827580287390359431250 * (n - 6) ^ 12) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 12))
  have h13 : (0 : ℤ) ≤ n * (572324348289677542124816250 * (n - 6) ^ 13) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 13))
  have h14 : (0 : ℤ) ≤ n * (39789368499977143047000000 * (n - 6) ^ 14) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 14))
  have h15 : (0 : ℤ) ≤ n * (738514794128363639887500 * (n - 6) ^ 15) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 15))
  have h16 : (0 : ℤ) ≤ n * (33911393607935065096875 * (n - 6) ^ 16) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 16))
  rw [deficit_eighteen_factored_v]
  nlinarith [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]

/-- Base case `n=2`. -/
theorem E18_le_wick_base_two : E18 2 ≤ wick 18 2 := by rw [E18_two, wick_eighteen]; norm_num

/-- Base case `n=4`. -/
theorem E18_le_wick_base_four : E18 4 ≤ wick 18 4 := by rw [E18_four, wick_eighteen]; norm_num

/-- The depth-18 char-0 Wick/Gaussian bound on the dyadic support range: `n = 2`,
`n = 4`, or `n ≥ 6`. -/
theorem E18_le_wick (n : ℤ) (hn : n = 2 ∨ n = 4 ∨ 6 ≤ n) : E18 n ≤ wick 18 n := by
  rcases hn with rfl | hrest
  · exact E18_le_wick_base_two
  · rcases hrest with rfl | hge
    · exact E18_le_wick_base_four
    · have hpos := deficit_eighteen_nonneg_from_six n hge
      linarith

/-! ## The Wick cushion is strictly positive -/

/-- The depth-18 char-0 Wick deficit is strictly positive on the dyadic support range: `n = 2`,
`n = 4`, or `n ≥ 6`. -/
theorem deficit_eighteen_pos (n : ℤ) (hn : n = 2 ∨ n = 4 ∨ 6 ≤ n) :
    0 < wick 18 n - E18 n := by
  rcases hn with rfl | hrest
  · rw [deficit_eighteen]; norm_num
  · rcases hrest with rfl | hge
    · rw [deficit_eighteen]; norm_num
    · have hu0 : (0 : ℤ) ≤ n - 6 := by linarith
      have hn0 : (0 : ℤ) ≤ n := by linarith
      have hcert := deficit_eighteen_factored_v n
      have hstrict : (0 : ℤ) < n * 3751677190267453451509612115443050 := by positivity
      have h1 : (0 : ℤ) ≤ n * (10092584838014529671582672732866275 * (n - 6) ^ 1) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 1))
      have h2 : (0 : ℤ) ≤ n * (14839059093882366308429205574440300 * (n - 6) ^ 2) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 2))
      have h3 : (0 : ℤ) ≤ n * (11593719854413984142958030625498725 * (n - 6) ^ 3) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 3))
      have h4 : (0 : ℤ) ≤ n * (6819305060115898386953998954101075 * (n - 6) ^ 4) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 4))
      have h5 : (0 : ℤ) ≤ n * (3063239716817280080850154760858175 * (n - 6) ^ 5) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 5))
      have h6 : (0 : ℤ) ≤ n * (968750980296328884384801283212000 * (n - 6) ^ 6) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 6))
      have h7 : (0 : ℤ) ≤ n * (264447714087323300159681720915250 * (n - 6) ^ 7) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 7))
      have h8 : (0 : ℤ) ≤ n * (54597369336614405509891651093125 * (n - 6) ^ 8) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 8))
      have h9 : (0 : ℤ) ≤ n * (8777495657797558500555849477375 * (n - 6) ^ 9) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 9))
      have h10 : (0 : ℤ) ≤ n * (1275822059962688494501260015000 * (n - 6) ^ 10) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 10))
      have h11 : (0 : ℤ) ≤ n * (116858885011909111440605486250 * (n - 6) ^ 11) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 11))
      have h12 : (0 : ℤ) ≤ n * (11951261827580287390359431250 * (n - 6) ^ 12) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 12))
      have h13 : (0 : ℤ) ≤ n * (572324348289677542124816250 * (n - 6) ^ 13) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 13))
      have h14 : (0 : ℤ) ≤ n * (39789368499977143047000000 * (n - 6) ^ 14) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 14))
      have h15 : (0 : ℤ) ≤ n * (738514794128363639887500 * (n - 6) ^ 15) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 15))
      have h16 : (0 : ℤ) ≤ n * (33911393607935065096875 * (n - 6) ^ 16) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 16))
      nlinarith [hcert, hstrict, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]

/-- The second coefficient law at depth 18: `33911393607935065096875 = C(18,2)·35‼`. -/
theorem deficit_eighteen_leading :
    (33911393607935065096875 : ℤ) = 153 * 221643095476699771875 := by
  norm_num

end ProximityGap.Frontier.E18ClosedForm

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.E18ClosedForm.E18_two
#print axioms ProximityGap.Frontier.E18ClosedForm.deficit_eighteen
#print axioms ProximityGap.Frontier.E18ClosedForm.E18_le_wick
#print axioms ProximityGap.Frontier.E18ClosedForm.deficit_eighteen_pos
