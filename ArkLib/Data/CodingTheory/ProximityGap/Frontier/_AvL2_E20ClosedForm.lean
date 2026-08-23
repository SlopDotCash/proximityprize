/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# The char-0 additive energy `E_20(μ_n)`: exact closed form (#444, avenue L2)

This extends the verified char-0 closed-form ladder one rung beyond `E_19`. It records the
exact cross-polytope / Lam--Leung polynomial at depth `r = 20`, plus the Wick bound and a
strict positive cushion. The positivity certificate starts at `n = 6`, covering the dyadic
support range `n = 2`, `n = 4`, or `n ≥ 6`. This is deliberately only a char-0 rung; it
does not assert the char-p transfer that forms the #444 BGK/Paley wall.
-/

namespace ProximityGap.Frontier.E20ClosedForm

/-- `E_20(ℂ)(n)`: the char-0 additive energy of `μ_n` at depth `r = 20`, in closed form. -/
def E20 (n : ℤ) : ℤ :=
  319830986772877770815625 * n ^ 20
    - 60767887486846776454968750 * n ^ 19
    + 5621029592533326822084609375 * n ^ 18
    - 335226051321190242313835109375 * n ^ 17
    + 14400953039341410326133115016250 * n ^ 16
    - 471946489815327071231866479300000 * n ^ 15
    + 12197877711114862927876254851812500 * n ^ 14
    - 253667392216464549696134430931762500 * n ^ 13
    + 4294510879864816192327141715910966375 * n ^ 12
    - 59530701634445340885908146077511508250 * n ^ 11
    + 676400206260030915515838988247707336875 * n ^ 10
    - 6279279935913091685479908476081112125625 * n ^ 9
    + 47269821971338379705937324221572445189775 * n ^ 8
    - 284965808831589101458873118927166100573200 * n ^ 7
    + 1350032352788011955455321338835920665570400 * n ^ 6
    - 4888034015861826243790015248325297764933750 * n ^ 5
    + 12968193620814358704880023315032667679856205 * n ^ 4
    - 23559883834305809106656299851057000726621930 * n ^ 3
    + 25904946222143085507621331811452823974197285 * n ^ 2
    - 12806833139580706193135950543861768287899280 * n ^ 1

/-- The Wick leading term `(2r−1)‼·n^r`. -/
def wick (r : ℕ) (n : ℤ) : ℤ := (Nat.doubleFactorial (2 * r - 1) : ℤ) * n ^ r

@[simp] theorem wick_twenty (n : ℤ) : wick 20 n = 319830986772877770815625 * n ^ 20 := by
  simp [wick, Nat.doubleFactorial]

/-! ## Small-case exact values -/

/-- `E_20(2) = 137846528820 = C(40,20)`. -/
theorem E20_two : E20 2 = 137846528820 := by decide

/-- `E_20(4) = 19001665507723090592400`. -/
theorem E20_four : E20 4 = 19001665507723090592400 := by decide

/-! ## The exact char-0 deficit `D_20 = wick 20 n − E_20(ℂ)` -/

/-- The exact deficit `wick 20 n − E_20(ℂ)`. Its leading nonzero coefficient is
`C(20,2)·39‼ = 60767887486846776454968750`. -/
theorem deficit_twenty (n : ℤ) :
    wick 20 n - E20 n =
      60767887486846776454968750 * n ^ 19
        - 5621029592533326822084609375 * n ^ 18
        + 335226051321190242313835109375 * n ^ 17
        - 14400953039341410326133115016250 * n ^ 16
        + 471946489815327071231866479300000 * n ^ 15
        - 12197877711114862927876254851812500 * n ^ 14
        + 253667392216464549696134430931762500 * n ^ 13
        - 4294510879864816192327141715910966375 * n ^ 12
        + 59530701634445340885908146077511508250 * n ^ 11
        - 676400206260030915515838988247707336875 * n ^ 10
        + 6279279935913091685479908476081112125625 * n ^ 9
        - 47269821971338379705937324221572445189775 * n ^ 8
        + 284965808831589101458873118927166100573200 * n ^ 7
        - 1350032352788011955455321338835920665570400 * n ^ 6
        + 4888034015861826243790015248325297764933750 * n ^ 5
        - 12968193620814358704880023315032667679856205 * n ^ 4
        + 23559883834305809106656299851057000726621930 * n ^ 3
        - 25904946222143085507621331811452823974197285 * n ^ 2
        + 12806833139580706193135950543861768287899280 * n ^ 1 := by
  simp only [wick_twenty, E20]; ring

/-- `wick 20 n − E_20 = n · (Σ_k c_k · (n-6)^k)` with all `c_k ≥ 0`. -/
theorem deficit_twenty_factored_v (n : ℤ) :
    wick 20 n - E20 n =
      n * (        194892126941517644540231081531368759170
        + 243524338540103822218065872906421474135 * (n - 6) ^ 1
        + 1407179827895480874592399200316984665840 * (n - 6) ^ 2
        + 700138974639311953607942339858603799795 * (n - 6) ^ 3
        + 542077535148854489279972729240309070750 * (n - 6) ^ 4
        + 347606370388241072595953158644386334900 * (n - 6) ^ 5
        + 92251522851291663697386278938466908650 * (n - 6) ^ 6
        + 38715061073371736431554258690613230225 * (n - 6) ^ 7
        + 8815506201688447447872394168579494375 * (n - 6) ^ 8
        + 1591845711267637360744967778931535625 * (n - 6) ^ 9
        + 355357479079639244848177530640147500 * (n - 6) ^ 10
        + 30199832659476247783973143294733625 * (n - 6) ^ 11
        + 5868689345753015810226604043137500 * (n - 6) ^ 12
        + 269661160557325349775468968962500 * (n - 6) ^ 13
        + 39411288910684417241923245337500 * (n - 6) ^ 14
        + 970891779331350245915779983750 * (n - 6) ^ 15
        + 96590557160342951175172828125 * (n - 6) ^ 16
        + 941902256046125035052015625 * (n - 6) ^ 17
        + 60767887486846776454968750 * (n - 6) ^ 18) := by
  rw [deficit_twenty]; ring_nf

/-- `0 ≤ wick 20 n − E20 n` for `n ≥ 6`, from the nonnegative `v = n−6` certificate. -/
theorem deficit_twenty_nonneg_from_six (n : ℤ) (hn : 6 ≤ n) :
    0 ≤ wick 20 n - E20 n := by
  have hu0 : (0 : ℤ) ≤ n - 6 := by linarith
  have hn0 : (0 : ℤ) ≤ n := by linarith
  have h0 : (0 : ℤ) ≤ n * 194892126941517644540231081531368759170 := by positivity
  have h1 : (0 : ℤ) ≤ n * (243524338540103822218065872906421474135 * (n - 6) ^ 1) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 1))
  have h2 : (0 : ℤ) ≤ n * (1407179827895480874592399200316984665840 * (n - 6) ^ 2) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 2))
  have h3 : (0 : ℤ) ≤ n * (700138974639311953607942339858603799795 * (n - 6) ^ 3) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 3))
  have h4 : (0 : ℤ) ≤ n * (542077535148854489279972729240309070750 * (n - 6) ^ 4) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 4))
  have h5 : (0 : ℤ) ≤ n * (347606370388241072595953158644386334900 * (n - 6) ^ 5) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 5))
  have h6 : (0 : ℤ) ≤ n * (92251522851291663697386278938466908650 * (n - 6) ^ 6) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 6))
  have h7 : (0 : ℤ) ≤ n * (38715061073371736431554258690613230225 * (n - 6) ^ 7) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 7))
  have h8 : (0 : ℤ) ≤ n * (8815506201688447447872394168579494375 * (n - 6) ^ 8) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 8))
  have h9 : (0 : ℤ) ≤ n * (1591845711267637360744967778931535625 * (n - 6) ^ 9) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 9))
  have h10 : (0 : ℤ) ≤ n * (355357479079639244848177530640147500 * (n - 6) ^ 10) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 10))
  have h11 : (0 : ℤ) ≤ n * (30199832659476247783973143294733625 * (n - 6) ^ 11) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 11))
  have h12 : (0 : ℤ) ≤ n * (5868689345753015810226604043137500 * (n - 6) ^ 12) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 12))
  have h13 : (0 : ℤ) ≤ n * (269661160557325349775468968962500 * (n - 6) ^ 13) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 13))
  have h14 : (0 : ℤ) ≤ n * (39411288910684417241923245337500 * (n - 6) ^ 14) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 14))
  have h15 : (0 : ℤ) ≤ n * (970891779331350245915779983750 * (n - 6) ^ 15) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 15))
  have h16 : (0 : ℤ) ≤ n * (96590557160342951175172828125 * (n - 6) ^ 16) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 16))
  have h17 : (0 : ℤ) ≤ n * (941902256046125035052015625 * (n - 6) ^ 17) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 17))
  have h18 : (0 : ℤ) ≤ n * (60767887486846776454968750 * (n - 6) ^ 18) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 18))
  rw [deficit_twenty_factored_v]
  nlinarith [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18]

/-- Base case `n=2`. -/
theorem E20_le_wick_base_two : E20 2 ≤ wick 20 2 := by rw [E20_two, wick_twenty]; norm_num

/-- Base case `n=4`. -/
theorem E20_le_wick_base_four : E20 4 ≤ wick 20 4 := by rw [E20_four, wick_twenty]; norm_num

/-- The depth-20 char-0 Wick/Gaussian bound on the dyadic support range: `n = 2`,
`n = 4`, or `n ≥ 6`. -/
theorem E20_le_wick (n : ℤ) (hn : n = 2 ∨ n = 4 ∨ 6 ≤ n) : E20 n ≤ wick 20 n := by
  rcases hn with rfl | hrest
  · exact E20_le_wick_base_two
  · rcases hrest with rfl | hge
    · exact E20_le_wick_base_four
    · have hpos := deficit_twenty_nonneg_from_six n hge
      linarith

/-! ## The Wick cushion is strictly positive -/

/-- The depth-20 char-0 Wick deficit is strictly positive on the dyadic support range: `n = 2`,
`n = 4`, or `n ≥ 6`. -/
theorem deficit_twenty_pos (n : ℤ) (hn : n = 2 ∨ n = 4 ∨ 6 ≤ n) :
    0 < wick 20 n - E20 n := by
  rcases hn with rfl | hrest
  · rw [deficit_twenty]; norm_num
  · rcases hrest with rfl | hge
    · rw [deficit_twenty]; norm_num
    · have hu0 : (0 : ℤ) ≤ n - 6 := by linarith
      have hn0 : (0 : ℤ) ≤ n := by linarith
      have hcert := deficit_twenty_factored_v n
      have hstrict : (0 : ℤ) < n * 194892126941517644540231081531368759170 := by positivity
      have h1 : (0 : ℤ) ≤ n * (243524338540103822218065872906421474135 * (n - 6) ^ 1) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 1))
      have h2 : (0 : ℤ) ≤ n * (1407179827895480874592399200316984665840 * (n - 6) ^ 2) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 2))
      have h3 : (0 : ℤ) ≤ n * (700138974639311953607942339858603799795 * (n - 6) ^ 3) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 3))
      have h4 : (0 : ℤ) ≤ n * (542077535148854489279972729240309070750 * (n - 6) ^ 4) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 4))
      have h5 : (0 : ℤ) ≤ n * (347606370388241072595953158644386334900 * (n - 6) ^ 5) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 5))
      have h6 : (0 : ℤ) ≤ n * (92251522851291663697386278938466908650 * (n - 6) ^ 6) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 6))
      have h7 : (0 : ℤ) ≤ n * (38715061073371736431554258690613230225 * (n - 6) ^ 7) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 7))
      have h8 : (0 : ℤ) ≤ n * (8815506201688447447872394168579494375 * (n - 6) ^ 8) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 8))
      have h9 : (0 : ℤ) ≤ n * (1591845711267637360744967778931535625 * (n - 6) ^ 9) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 9))
      have h10 : (0 : ℤ) ≤ n * (355357479079639244848177530640147500 * (n - 6) ^ 10) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 10))
      have h11 : (0 : ℤ) ≤ n * (30199832659476247783973143294733625 * (n - 6) ^ 11) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 11))
      have h12 : (0 : ℤ) ≤ n * (5868689345753015810226604043137500 * (n - 6) ^ 12) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 12))
      have h13 : (0 : ℤ) ≤ n * (269661160557325349775468968962500 * (n - 6) ^ 13) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 13))
      have h14 : (0 : ℤ) ≤ n * (39411288910684417241923245337500 * (n - 6) ^ 14) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 14))
      have h15 : (0 : ℤ) ≤ n * (970891779331350245915779983750 * (n - 6) ^ 15) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 15))
      have h16 : (0 : ℤ) ≤ n * (96590557160342951175172828125 * (n - 6) ^ 16) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 16))
      have h17 : (0 : ℤ) ≤ n * (941902256046125035052015625 * (n - 6) ^ 17) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 17))
      have h18 : (0 : ℤ) ≤ n * (60767887486846776454968750 * (n - 6) ^ 18) :=
        mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 18))
      nlinarith [hcert, hstrict, h1, h2, h3, h4, h5, h6, h7, h8, h9,
        h10, h11, h12, h13, h14, h15, h16, h17, h18]

/-- The second coefficient law at depth 20: `60767887486846776454968750 = C(20,2)·39‼`. -/
theorem deficit_twenty_leading :
    (60767887486846776454968750 : ℤ) = 190 * 319830986772877770815625 := by
  norm_num

end ProximityGap.Frontier.E20ClosedForm

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.E20ClosedForm.E20_two
#print axioms ProximityGap.Frontier.E20ClosedForm.deficit_twenty
#print axioms ProximityGap.Frontier.E20ClosedForm.E20_le_wick
#print axioms ProximityGap.Frontier.E20ClosedForm.deficit_twenty_pos
