/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._CharZeroEnergyClosedForm

/-!
# The char-0 cushion is a two-sided bracket: `wick·(1 − C(r,2)/n) ≤ E_r(ℂ) ≤ wick` (#444)

## What this lane decides

`_CharZeroEnergyClosedForm` proves the *upper* half of the char-0 cushion: the deficit
`D_r := wick_r − E_r(ℂ)` is nonnegative (`E_r ≤ wick`, `deficit_r_pos`). Its docstring records
the companion fact `D_r / wick → C(r,2)/n` ("the cushion shrinks like `C(r,2)/n`") only as
a comment.
This file makes the **lower** half a theorem: an explicit upper bound on the deficit

  `D_r = wick_r − E_r(ℂ) ≤ C(r,2)·(2r−1)‼·n^{r−1}`   for `n ≥ 2`,   `r = 2..6`,

equivalently the **multiplicative cushion lower bound**

  `E_r(ℂ) ≥ wick_r − C(r,2)·(2r−1)‼·n^{r−1} = (2r−1)‼·n^{r−1}·(n − C(r,2))`,

so that, with the existing `E_r ≤ wick`, the char-0 energy ratio is *bracketed*:

  `1 − C(r,2)/n  ≤  E_r(ℂ) / wick_r  ≤  1`.

This is exactly the structural fact #444 flags as *mildly favorable to the floor being true*: the
char-0 anchor `K_eff(n) = (E_r/wick)^{1/r} → 1 strictly from below`, with a quantitative gap
of order `C(r,2)/n`. The deficit-upper-bound `D_r ≤ C(r,2)·wick·n^{r−1}` is the missing companion to
`deficit_r_pos`; together they pin the cushion to a clean `Θ(1/n)` band whose endpoints are both
in-tree theorems rather than asymptotic comments.

## Probe (rule 2, exact, `scripts/probes/probe_charzero_cushion_bracket.py`)

For `r = 2..6` (also cross-checked `r = 8, 9` against the landed `_AvL2_E{8,9}ClosedForm` forms) the
remainder `C(r,2)·wick·n^{r−1} − D_r` factors as `n · (positive-on-`n≥2`-polynomial)`:
`0`, `40n`, `35n(41n−33)`, `63n(625n²−1225n+912)` (disc `< 0`, min `1247/4 > 0`),
`231n(4425n³−15300n²+27041n−18920)` (the cubic's `n→n+2` shift has all-nonnegative coefficients),
so the bound holds with equality only at `r = 2`, strictly for `r ≥ 3`.

## Honest scope (rules 1, 3, 4, 6 + ASYMPTOTIC GUARD)

This is the **char-0 face only**, the boundary of what is true. It does NOT close CORE, makes no
char-`p` claim, no capacity / cliff-at-`n/2` / beyond-Johnson claim. The open prize wall is the
char-`p` transfer of this bracket to depth `r ≈ ln q`; at that depth the cushion collapses to
`≈ C(r,2)/n → 5.6×10⁻⁶` and the energy route is lossy. This file only certifies the char-0 cushion's
shape (a two-sided `Θ(1/n)` band) as a genuine theorem, the lower companion of the existing
nonnegative-deficit half. Issue #444.
-/

namespace ProximityGap.Frontier.CharZeroEnergy

/-! ## The deficit upper bound `D_r ≤ C(r,2)·(2r−1)‼·n^{r−1}` (the cushion's lower edge)

`C(r,2)·(2r−1)‼` for `r = 2..6` is
`1·3, 3·15, 6·105, 10·945, 15·10395 = 3, 45, 630, 9450, 155925`. -/

theorem deficit_two_le (n : ℤ) (_hn : 1 ≤ n) : wick 2 n - E2 n ≤ 3 * n := by
  rw [deficit_two]

theorem deficit_three_le (n : ℤ) (hn : 1 ≤ n) : wick 3 n - E3 n ≤ 45 * n ^ 2 := by
  rw [deficit_three]; nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ n) (by linarith : (0:ℤ) ≤ n)]

theorem deficit_four_le (n : ℤ) (hn : 1 ≤ n) : wick 4 n - E4 n ≤ 630 * n ^ 3 := by
  rw [deficit_four]
  nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ n) (by linarith : (0:ℤ) ≤ 41 * n - 33)]

theorem deficit_five_le (n : ℤ) (hn : 1 ≤ n) : wick 5 n - E5 n ≤ 9450 * n ^ 4 := by
  rw [deficit_five]
  nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ n) (by nlinarith [sq_nonneg (50 * n - 49)] :
    (0:ℤ) ≤ 625 * n ^ 2 - 1225 * n + 912)]

theorem deficit_six_le (n : ℤ) (hn : 2 ≤ n) : wick 6 n - E6 n ≤ 155925 * n ^ 5 := by
  rw [deficit_six]
  nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ n) (by
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℤ) ≤ n - 2) (by linarith : (0:ℤ) ≤ n - 2))
      (by linarith : (0:ℤ) ≤ n - 2), mul_nonneg (by linarith : (0:ℤ) ≤ n - 2)
      (by linarith : (0:ℤ) ≤ n - 2), (by linarith : (0:ℤ) ≤ n - 2)] :
    (0:ℤ) ≤ 4425 * n ^ 3 - 15300 * n ^ 2 + 27041 * n - 18920)]

/-! ## The assembled two-sided cushion bracket `wick − C(r,2)·wick·n^{r−1} ≤ E_r(ℂ) ≤ wick`

The lower edge is `wick_r − D_r_upper = (2r−1)‼·(n^r − C(r,2)·n^{r−1})`, which equals
`(2r−1)‼·n^{r−1}·(n − C(r,2))`, the explicit `1 − C(r,2)/n` multiplicative cushion. Paired with
`E_r ≤ wick` this is the full band. -/

theorem E2_cushion_lower (n : ℤ) (hn : 1 ≤ n) : 3 * n ^ 2 - 3 * n ≤ E2 n := by
  have h := deficit_two_le n hn; simp only [wick_two] at h; linarith

theorem E3_cushion_lower (n : ℤ) (hn : 1 ≤ n) : 15 * n ^ 3 - 45 * n ^ 2 ≤ E3 n := by
  have h := deficit_three_le n hn; simp only [wick_three] at h; linarith

theorem E4_cushion_lower (n : ℤ) (hn : 1 ≤ n) : 105 * n ^ 4 - 630 * n ^ 3 ≤ E4 n := by
  have h := deficit_four_le n hn; simp only [wick_four] at h; linarith

theorem E5_cushion_lower (n : ℤ) (hn : 1 ≤ n) : 945 * n ^ 5 - 9450 * n ^ 4 ≤ E5 n := by
  have h := deficit_five_le n hn; simp only [wick_five] at h; linarith

theorem E6_cushion_lower (n : ℤ) (hn : 2 ≤ n) : 10395 * n ^ 6 - 155925 * n ^ 5 ≤ E6 n := by
  have h := deficit_six_le n hn; simp only [wick_six] at h; linarith

/-- **The char-0 cushion is a two-sided `Θ(1/n)` band (headline, `r = 3`).** Combining the existing
`E3_le_wick` (upper) with `E3_cushion_lower` (this file): `15n³·(1 − 3/n) ≤ E₃(ℂ) ≤ 15n³`, i.e. the
energy ratio `E₃/wick₃ ∈ [1 − 3/n, 1]`. The cushion `K_eff → 1` strictly from below, gap `≤ 3/n`.
This is the char-0 anchor #444 flags as mildly favorable to the floor being true; the char-`p`
transfer at `r ≈ ln q` (where the cushion collapses) remains the open wall. -/
theorem E3_cushion_bracket (n : ℤ) (hn : 1 ≤ n) :
    15 * n ^ 3 - 45 * n ^ 2 ≤ E3 n ∧ E3 n ≤ 15 * n ^ 3 := by
  refine ⟨E3_cushion_lower n hn, ?_⟩
  have h := E3_le_wick n hn; simpa only [wick_three] using h

end ProximityGap.Frontier.CharZeroEnergy

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.CharZeroEnergy.deficit_six_le
#print axioms ProximityGap.Frontier.CharZeroEnergy.E6_cushion_lower
#print axioms ProximityGap.Frontier.CharZeroEnergy.E3_cushion_bracket
