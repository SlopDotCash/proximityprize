/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvL2_E7ClosedForm
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvL2_E8ClosedForm
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvL2_E9ClosedForm

/-!
# Char-0 cushion lower edge extended to `r = 7, 8, 9` (#444)

`_CharZeroCushionBracket` lands the cushion lower edge (deficit upper bound
`D_r ≤ C(r,2)·(2r−1)‼·n^{r−1}`, giving `E_r(ℂ) ≥ wick·(1 − C(r,2)/n)`) for `r = 2..6`. This file
EXTENDS that brick to the full landed ladder `r = 7, 8, 9` (`_AvL2_E{7,8,9}ClosedForm`), so the
char-0 energy ratio is bracketed `1 − C(r,2)/n ≤ E_r/wick_r ≤ 1` for every in-tree `E_r`.

The deficit upper bound at these `r` uses the SAME `(n−2)`-basis nonnegativity certificate the
`_AvL2_E{7,8,9}` files use for the upper half (`deficit_r_pos`): the remainder
`C(r,2)·wick·n^{r−1} − D_r` factors as `n · inner_r(n)`, where `inner_r` has all-nonnegative
coefficients once written in the shifted variable `(n−2)`, hence is `≥ 0` for `n ≥ 2`.

## Probe (rule 2): `scripts/probes/probe_charzero_cushion_bracket.py` covers `r = 7..9` too: the
bracket `0 ≤ D_r ≤ C(r,2)·(2r−1)‼·n^{r−1}` holds for all of `r = 2..6, 8, 9` over
`n = 2..59 + 100, 1000, 2²⁰` (and `r = 7` by the same factorization, certified below).

## Honest scope (rules 1, 3, 4, 6): char-0 face only, the boundary of what is true. No char-`p` /
capacity / cliff-at-`n/2` / beyond-Johnson claim. Issue #444.

`C(r,2)·(2r−1)‼` for `r = 7, 8, 9` is `21·135135, 28·2027025, 36·34459425`
`= 2837835, 56756700, 1240539300`.
-/

namespace ProximityGap.Frontier.CharZeroEnergy

open ProximityGap.Frontier.E7ClosedForm in
/-- `D_7 = wick − E_7(ℂ) ≤ C(7,2)·135135·n⁶ = 2837835·n⁶` for `n ≥ 2`. The cushion lower edge at
`r = 7`. -/
theorem deficit_seven_le (n : ℤ) (hn : 2 ≤ n) :
    wick 7 n - E7 n ≤ 2837835 * n ^ 6 := by
  rw [deficit_seven]
  nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ n) (by
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by linarith : (0:ℤ) ≤ n - 2)
      (by linarith : (0:ℤ) ≤ n - 2)) (by linarith : (0:ℤ) ≤ n - 2)) (by linarith : (0:ℤ) ≤ n - 2))
      (by linarith : (0:ℤ) ≤ n - 2),
      mul_nonneg (mul_nonneg (mul_nonneg (by linarith : (0:ℤ) ≤ n - 2)
        (by linarith : (0:ℤ) ≤ n - 2))
        (by linarith : (0:ℤ) ≤ n - 2)) (by linarith : (0:ℤ) ≤ n - 2),
      mul_nonneg (mul_nonneg (by linarith : (0:ℤ) ≤ n - 2) (by linarith : (0:ℤ) ≤ n - 2))
        (by linarith : (0:ℤ) ≤ n - 2),
      mul_nonneg (by linarith : (0:ℤ) ≤ n - 2) (by linarith : (0:ℤ) ≤ n - 2),
      (by linarith : (0:ℤ) ≤ n - 2)] :
    (0:ℤ) ≤ 26801775 * n ^ 4 - 141891750 * n ^ 3 + 433726293 * n ^ 2 - 708996288 * n
      + 471556800)]

open ProximityGap.Frontier.E8ClosedForm in
/-- `D_8 ≤ C(8,2)·2027025·n⁷ = 56756700·n⁷` for `n ≥ 2`. The cushion lower edge at `r = 8`. -/
theorem deficit_eight_le (n : ℤ) (hn : 2 ≤ n) :
    wick 8 n - E8 n ≤ 56756700 * n ^ 7 := by
  have hd : wick 8 n - E8 n = 56756700 * n ^ 7 - 728377650 * n ^ 6 + 5439183750 * n ^ 5
      - 25055875845 * n ^ 4 + 69934975110 * n ^ 3 - 107438611995 * n ^ 2 + 68492499075 * n := by
    simp only [wick_eight, E8]; ring
  rw [hd]
  nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ n) (by
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (by linarith : (0:ℤ) ≤ n - 2) (by linarith : (0:ℤ) ≤ n - 2)) (by linarith : (0:ℤ) ≤ n - 2))
      (by linarith : (0:ℤ) ≤ n - 2)) (by linarith : (0:ℤ) ≤ n - 2)) (by linarith : (0:ℤ) ≤ n - 2),
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by linarith : (0:ℤ) ≤ n - 2)
        (by linarith : (0:ℤ) ≤ n - 2)) (by linarith : (0:ℤ) ≤ n - 2)) (by linarith : (0:ℤ) ≤ n - 2))
        (by linarith : (0:ℤ) ≤ n - 2),
      mul_nonneg (mul_nonneg (mul_nonneg (by linarith : (0:ℤ) ≤ n - 2)
        (by linarith : (0:ℤ) ≤ n - 2))
        (by linarith : (0:ℤ) ≤ n - 2)) (by linarith : (0:ℤ) ≤ n - 2),
      mul_nonneg (mul_nonneg (by linarith : (0:ℤ) ≤ n - 2) (by linarith : (0:ℤ) ≤ n - 2))
        (by linarith : (0:ℤ) ≤ n - 2),
      mul_nonneg (by linarith : (0:ℤ) ≤ n - 2) (by linarith : (0:ℤ) ≤ n - 2),
      (by linarith : (0:ℤ) ≤ n - 2)] :
    (0:ℤ) ≤ 728377650 * n ^ 5 - 5439183750 * n ^ 4 + 25055875845 * n ^ 3
      - 69934975110 * n ^ 2 + 107438611995 * n - 68492499075)]

open ProximityGap.Frontier.E9ClosedForm in
/-- `D_9 ≤ C(9,2)·34459425·n⁸ = 1240539300·n⁸` for `n ≥ 2`. The cushion lower edge at `r = 9`. -/
theorem deficit_nine_le (n : ℤ) (hn : 2 ≤ n) :
    wick 9 n - E9 n ≤ 1240539300 * n ^ 8 := by
  have hd : wick 9 n - E9 n = 1240539300 * n ^ 8 - 20744573850 * n ^ 7 + 206963306550 * n ^ 6
      - 1327347186165 * n ^ 5 + 5524263935190 * n ^ 4 - 14357763632355 * n ^ 3
      + 20957471507115 * n ^ 2 - 12885585512800 * n := by
    simp only [wick_nine, E9]; ring
  rw [hd]
  nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ n) (by
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (by linarith : (0:ℤ) ≤ n - 2) (by linarith : (0:ℤ) ≤ n - 2)) (by linarith : (0:ℤ) ≤ n - 2))
      (by linarith : (0:ℤ) ≤ n - 2)) (by linarith : (0:ℤ) ≤ n - 2)) (by linarith : (0:ℤ) ≤ n - 2))
      (by linarith : (0:ℤ) ≤ n - 2),
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by linarith : (0:ℤ) ≤ n - 2)
        (by linarith : (0:ℤ) ≤ n - 2)) (by linarith : (0:ℤ) ≤ n - 2)) (by linarith : (0:ℤ) ≤ n - 2))
        (by linarith : (0:ℤ) ≤ n - 2)) (by linarith : (0:ℤ) ≤ n - 2),
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by linarith : (0:ℤ) ≤ n - 2)
        (by linarith : (0:ℤ) ≤ n - 2)) (by linarith : (0:ℤ) ≤ n - 2)) (by linarith : (0:ℤ) ≤ n - 2))
        (by linarith : (0:ℤ) ≤ n - 2),
      mul_nonneg (mul_nonneg (mul_nonneg (by linarith : (0:ℤ) ≤ n - 2)
        (by linarith : (0:ℤ) ≤ n - 2))
        (by linarith : (0:ℤ) ≤ n - 2)) (by linarith : (0:ℤ) ≤ n - 2),
      mul_nonneg (mul_nonneg (by linarith : (0:ℤ) ≤ n - 2) (by linarith : (0:ℤ) ≤ n - 2))
        (by linarith : (0:ℤ) ≤ n - 2),
      mul_nonneg (by linarith : (0:ℤ) ≤ n - 2) (by linarith : (0:ℤ) ≤ n - 2),
      (by linarith : (0:ℤ) ≤ n - 2)] :
    (0:ℤ) ≤ 20744573850 * n ^ 6 - 206963306550 * n ^ 5 + 1327347186165 * n ^ 4
      - 5524263935190 * n ^ 3 + 14357763632355 * n ^ 2 - 20957471507115 * n
      + 12885585512800)]

/-! ## Assembled cushion lower bounds `E_r(ℂ) ≥ wick − C(r,2)·wick·n^{r−1}` for `r = 7, 8, 9` -/

open ProximityGap.Frontier.E7ClosedForm in
theorem E7_cushion_lower (n : ℤ) (hn : 2 ≤ n) :
    135135 * n ^ 7 - 2837835 * n ^ 6 ≤ E7 n := by
  have h := deficit_seven_le n hn; simp only [wick_seven] at h; linarith

open ProximityGap.Frontier.E8ClosedForm in
theorem E8_cushion_lower (n : ℤ) (hn : 2 ≤ n) :
    2027025 * n ^ 8 - 56756700 * n ^ 7 ≤ E8 n := by
  have h := deficit_eight_le n hn; simp only [wick_eight] at h; linarith

open ProximityGap.Frontier.E9ClosedForm in
theorem E9_cushion_lower (n : ℤ) (hn : 2 ≤ n) :
    34459425 * n ^ 9 - 1240539300 * n ^ 8 ≤ E9 n := by
  have h := deficit_nine_le n hn; simp only [wick_nine] at h; linarith

end ProximityGap.Frontier.CharZeroEnergy

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.CharZeroEnergy.deficit_seven_le
#print axioms ProximityGap.Frontier.CharZeroEnergy.deficit_nine_le
#print axioms ProximityGap.Frontier.CharZeroEnergy.E9_cushion_lower
