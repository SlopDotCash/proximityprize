/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# char-0 step-ratio MONOTONICITY for `μ_{2^μ}`, proven for r = 2,3,4,5,6,7 (#444)

The localized prize reduced (`_StepRatioMonotone`) to the **monotonicity** of the step ratio
`R(r) = E_{r+1}/((2r+1)·n·E_r)`, equivalently the bounded-log-convexity
`(2r+1)·E_r·E_{r+2} ≤ (2r+3)·E_{r+1}²`. For the **Gaussian/Wick** values this is EQUALITY; the prize is
that the smooth-subgroup energies are *less log-convex than Gaussian* (sub-Gaussian).

This file PROVES the **char-0** monotonicity for the accessible depths `r = 2,3,4,5,6,7` from the in-tree
exact energy closed forms `E_2 = 3n²−3n`, `E_3 = 15n³−45n²+40n`, `E_4 = 105n⁴−630n³+1435n²−1155n`,
`E_5 = 945n⁵−9450n⁴+39375n³−77175n²+57456n`, plus the landed E₆,E₇,E₈,E₉ closed forms. The monotonicity gap `G(r) = (2r+3)E_{r+1}² −
(2r+1)E_r·E_{r+2}` is a polynomial in `n` with all-nonnegative coefficients in the `(n−4)` basis, hence
`> 0` for `n ≥ 8` (the prize regime `n = 2^μ`). Machine-verified by the one-sweep r=2..7 gap probe; proven here.

This is a genuine PARTIAL result: the char-0 step ratio `R(r)` is **antitone at r=2,3,4,5,6,7** (so the
energy sequence is sub-Gaussian at these depths), char-free arithmetic, no `sorry`. The char-`p` transfer (the
wraparound preserving the monotonicity) at deep `r` remains the open wall.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.CharZeroStepRatioMonotone

/-- char-0 additive energies of `μ_n` (the in-tree exact closed forms, r = 2..5). -/
def E2 (n : ℝ) : ℝ := 3*n^2 - 3*n
def E3 (n : ℝ) : ℝ := 15*n^3 - 45*n^2 + 40*n
def E4 (n : ℝ) : ℝ := 105*n^4 - 630*n^3 + 1435*n^2 - 1155*n
def E5 (n : ℝ) : ℝ := 945*n^5 - 9450*n^4 + 39375*n^3 - 77175*n^2 + 57456*n
def E6 (n : ℝ) : ℝ := 10395*n^6 - 155925*n^5 + 1022175*n^4 - 3534300*n^3 + 6246471*n^2 - 4370520*n
def E7 (n : ℝ) : ℝ :=
  135135*n^7 - 2837835*n^6 + 26801775*n^5 - 141891750*n^4 + 433726293*n^3 - 708996288*n^2 + 471556800*n
def E8 (n : ℝ) : ℝ :=
  2027025*n^8 - 56756700*n^7 + 728377650*n^6 - 5439183750*n^5
    + 25055875845*n^4 - 69934975110*n^3 + 107438611995*n^2 - 68492499075*n
def E9 (n : ℝ) : ℝ :=
  34459425*n^9 - 1240539300*n^8 + 20744573850*n^7 - 206963306550*n^6
    + 1327347186165*n^5 - 5524263935190*n^4 + 14357763632355*n^3
    - 20957471507115*n^2 + 12885585512800*n

/-- **char-0 step-ratio monotonicity at r = 2:** `5·E_2·E_4 ≤ 7·E_3²` for `n ≥ 8`. Equivalently the gap
`G(2) = 7·E_3² − 5·E_2·E_4 = n⁴·(1575n−8400) + n²·(13650n−6125) ≥ 0` — a sum of two manifestly nonnegative
pieces in the prize regime. So `R(2) ≥ R(3)` (the step ratio decreases at the first step), i.e. the energy
sequence is sub-Gaussian at depth 2. -/
theorem charZero_stepRatio_monotone_r2 {n : ℝ} (hn : 8 ≤ n) :
    5 * E2 n * E4 n ≤ 7 * (E3 n)^2 := by
  have hd : (0 : ℝ) ≤ n - 4 := by linarith
  simp only [E2, E3, E4]
  nlinarith [hd, pow_nonneg hd 2, pow_nonneg hd 3, pow_nonneg hd 4, pow_nonneg hd 5,
    mul_nonneg hd hd]

/-- **char-0 step-ratio monotonicity at r = 3:** `7·E_3·E_5 ≤ 9·E_4²` for `n ≥ 8`. The gap
`G(3) = 9·E_4² − 7·E_3·E_5` has all-nonnegative coefficients in the `(n−4)` basis; we discharge it via the
nonneg grouping `n⁶(99225n−1091475) + n⁵(4696650 − …)`-type pieces dominated for `n ≥ 8`. -/
theorem charZero_stepRatio_monotone_r3 {n : ℝ} (hn : 8 ≤ n) :
    7 * E3 n * E5 n ≤ 9 * (E4 n)^2 := by
  have hd : (0 : ℝ) ≤ n - 4 := by linarith
  simp only [E3, E4, E5]
  nlinarith [hd, pow_nonneg hd 2, pow_nonneg hd 3, pow_nonneg hd 4, pow_nonneg hd 5,
    pow_nonneg hd 6, pow_nonneg hd 7, mul_nonneg hd hd]

/-- **char-0 step-ratio monotonicity at r = 4:** `9·E_4·E_6 ≤ 11·E_5²` for `n ≥ 8` (`G(4) ≥ 0`, all
coeffs nonneg in the `(n−4)` basis). -/
theorem charZero_stepRatio_monotone_r4 {n : ℝ} (hn : 8 ≤ n) :
    9 * E4 n * E6 n ≤ 11 * (E5 n)^2 := by
  have hd : (0 : ℝ) ≤ n - 4 := by linarith
  simp only [E4, E5, E6]
  nlinarith [hd, pow_nonneg hd 2, pow_nonneg hd 3, pow_nonneg hd 4, pow_nonneg hd 5,
    pow_nonneg hd 6, pow_nonneg hd 7, pow_nonneg hd 8, pow_nonneg hd 9, pow_nonneg hd 10,
    mul_nonneg hd hd]

/-- **char-0 step-ratio monotonicity at r = 5:** `11·E_5·E_7 ≤ 13·E_6²` for `n ≥ 8` (`G(5) ≥ 0`, all
coeffs nonneg in the `(n−8)` basis). -/
theorem charZero_stepRatio_monotone_r5 {n : ℝ} (hn : 8 ≤ n) :
    11 * E5 n * E7 n ≤ 13 * (E6 n)^2 := by
  have hd : (0 : ℝ) ≤ n - 8 := by linarith
  simp only [E5, E6, E7]
  nlinarith [hd, pow_nonneg hd 2, pow_nonneg hd 3, pow_nonneg hd 4, pow_nonneg hd 5,
    pow_nonneg hd 6, pow_nonneg hd 7, pow_nonneg hd 8, pow_nonneg hd 9, pow_nonneg hd 10,
    pow_nonneg hd 11, pow_nonneg hd 12, mul_nonneg hd hd]

/-- **char-0 step-ratio monotonicity at r = 6:** `13·E_6·E_8 ≤ 15·E_7²` for `n ≥ 8` (`G(6) ≥ 0`, all
coeffs nonneg in the `(n−8)` certificate basis). -/
theorem charZero_stepRatio_monotone_r6 {n : ℝ} (hn : 8 ≤ n) :
    13 * E6 n * E8 n ≤ 15 * (E7 n)^2 := by
  have hd : (0 : ℝ) ≤ n - 8 := by linarith
  simp only [E6, E7, E8]
  nlinarith [hd, pow_nonneg hd 2, pow_nonneg hd 3, pow_nonneg hd 4, pow_nonneg hd 5,
    pow_nonneg hd 6, pow_nonneg hd 7, pow_nonneg hd 8, pow_nonneg hd 9, pow_nonneg hd 10,
    pow_nonneg hd 11, pow_nonneg hd 12, pow_nonneg hd 13, pow_nonneg hd 14, mul_nonneg hd hd]


/-- **char-0 step-ratio monotonicity at r = 7:** `15·E_7·E_9 ≤ 17·E_8²` for `n ≥ 8` (`G(7) ≥ 0`, all
coeffs nonneg in the `(n−8)` certificate basis). This extends the accessible char-0 monotonicity
ladder one rung using the landed `E_9` closed form. -/
theorem charZero_stepRatio_monotone_r7 {n : ℝ} (hn : 8 ≤ n) :
    15 * E7 n * E9 n ≤ 17 * (E8 n)^2 := by
  have hd : (0 : ℝ) ≤ n - 8 := by linarith
  simp only [E7, E8, E9]
  nlinarith [hd, pow_nonneg hd 2, pow_nonneg hd 3, pow_nonneg hd 4, pow_nonneg hd 5,
    pow_nonneg hd 6, pow_nonneg hd 7, pow_nonneg hd 8, pow_nonneg hd 9, pow_nonneg hd 10,
    pow_nonneg hd 11, pow_nonneg hd 12, pow_nonneg hd 13, pow_nonneg hd 14, pow_nonneg hd 15,
    pow_nonneg hd 16, mul_nonneg hd hd]


/-- **The r = 2 gap is strict/non-vacuous** in the prize regime `n ≥ 8`. -/
theorem charZero_stepRatio_monotone_r2_strict {n : ℝ} (hn : 8 ≤ n) :
    5 * E2 n * E4 n < 7 * (E3 n)^2 := by
  have hd : (0 : ℝ) ≤ n - 4 := by linarith
  have hpos : (0 : ℝ) < 1 := by norm_num
  simp only [E2, E3, E4]
  nlinarith [hd, pow_nonneg hd 2, pow_nonneg hd 3, pow_nonneg hd 4, pow_nonneg hd 5,
    hpos]

/-- **The r = 3 gap is strict/non-vacuous** in the prize regime `n ≥ 8`. -/
theorem charZero_stepRatio_monotone_r3_strict {n : ℝ} (hn : 8 ≤ n) :
    7 * E3 n * E5 n < 9 * (E4 n)^2 := by
  have hd : (0 : ℝ) ≤ n - 4 := by linarith
  have hpos : (0 : ℝ) < 1 := by norm_num
  simp only [E3, E4, E5]
  nlinarith [hd, pow_nonneg hd 2, pow_nonneg hd 3, pow_nonneg hd 4, pow_nonneg hd 5,
    pow_nonneg hd 6, pow_nonneg hd 7, hpos]

/-- **The r = 4 gap is strict/non-vacuous** in the prize regime `n ≥ 8`. -/
theorem charZero_stepRatio_monotone_r4_strict {n : ℝ} (hn : 8 ≤ n) :
    9 * E4 n * E6 n < 11 * (E5 n)^2 := by
  have hd : (0 : ℝ) ≤ n - 4 := by linarith
  have hpos : (0 : ℝ) < 1 := by norm_num
  simp only [E4, E5, E6]
  nlinarith [hd, pow_nonneg hd 2, pow_nonneg hd 3, pow_nonneg hd 4, pow_nonneg hd 5,
    pow_nonneg hd 6, pow_nonneg hd 7, pow_nonneg hd 8, pow_nonneg hd 9, pow_nonneg hd 10,
    hpos]

/-- **The r = 5 gap is strict/non-vacuous** in the prize regime `n ≥ 8`. -/
theorem charZero_stepRatio_monotone_r5_strict {n : ℝ} (hn : 8 ≤ n) :
    11 * E5 n * E7 n < 13 * (E6 n)^2 := by
  have hd : (0 : ℝ) ≤ n - 8 := by linarith
  have hpos : (0 : ℝ) < 1 := by norm_num
  simp only [E5, E6, E7]
  nlinarith [hd, pow_nonneg hd 2, pow_nonneg hd 3, pow_nonneg hd 4, pow_nonneg hd 5,
    pow_nonneg hd 6, pow_nonneg hd 7, pow_nonneg hd 8, pow_nonneg hd 9, pow_nonneg hd 10,
    pow_nonneg hd 11, pow_nonneg hd 12, hpos]

/-- **The r = 6 gap is strict/non-vacuous** in the prize regime `n ≥ 8`. -/
theorem charZero_stepRatio_monotone_r6_strict {n : ℝ} (hn : 8 ≤ n) :
    13 * E6 n * E8 n < 15 * (E7 n)^2 := by
  have hd : (0 : ℝ) ≤ n - 8 := by linarith
  have hpos : (0 : ℝ) < 1 := by norm_num
  simp only [E6, E7, E8]
  nlinarith [hd, pow_nonneg hd 2, pow_nonneg hd 3, pow_nonneg hd 4, pow_nonneg hd 5,
    pow_nonneg hd 6, pow_nonneg hd 7, pow_nonneg hd 8, pow_nonneg hd 9, pow_nonneg hd 10,
    pow_nonneg hd 11, pow_nonneg hd 12, pow_nonneg hd 13, pow_nonneg hd 14, hpos]

/-- **The r = 7 gap is strict/non-vacuous:** in the same prize regime `n ≥ 8`, the landed
non-strict rung actually has positive slack. This records that the `r = 7` char-0 step-ratio drop
is genuine, not just equality transported from the Gaussian/Wick model. -/
theorem charZero_stepRatio_monotone_r7_strict {n : ℝ} (hn : 8 ≤ n) :
    15 * E7 n * E9 n < 17 * (E8 n)^2 := by
  have hd : (0 : ℝ) ≤ n - 8 := by linarith
  have hpos : (0 : ℝ) < 1 := by norm_num
  simp only [E7, E8, E9]
  nlinarith [hd, pow_nonneg hd 2, pow_nonneg hd 3, pow_nonneg hd 4, pow_nonneg hd 5,
    pow_nonneg hd 6, pow_nonneg hd 7, pow_nonneg hd 8, pow_nonneg hd 9, pow_nonneg hd 10,
    pow_nonneg hd 11, pow_nonneg hd 12, pow_nonneg hd 13, pow_nonneg hd 14, pow_nonneg hd 15,
    pow_nonneg hd 16, hpos]


/-- **All accessible char-0 step-ratio drops are strict** for r = 2,3,4,5,6,7 in the prize
regime `n ≥ 8`. This is the non-vacuity companion to `charZero_stepRatio_monotone_r2_to_r7`:
the char-0 model is genuinely *below* Wick log-convex equality at every landed rung, not merely
non-strict by transported equality. -/
theorem charZero_stepRatio_strict_r2_to_r7 {n : ℝ} (hn : 8 ≤ n) :
    (5 * E2 n * E4 n < 7 * (E3 n)^2) ∧ (7 * E3 n * E5 n < 9 * (E4 n)^2) ∧
      (9 * E4 n * E6 n < 11 * (E5 n)^2) ∧ (11 * E5 n * E7 n < 13 * (E6 n)^2) ∧
        (13 * E6 n * E8 n < 15 * (E7 n)^2) ∧ (15 * E7 n * E9 n < 17 * (E8 n)^2) :=
  ⟨charZero_stepRatio_monotone_r2_strict hn, charZero_stepRatio_monotone_r3_strict hn,
   charZero_stepRatio_monotone_r4_strict hn, charZero_stepRatio_monotone_r5_strict hn,
   charZero_stepRatio_monotone_r6_strict hn, charZero_stepRatio_monotone_r7_strict hn⟩

/-- **The char-0 step ratio `R(r)` is ANTITONE for r = 2,3,4,5,6,7** — proven from the exact energy closed
forms. So the smooth-subgroup energy sequence is *sub-Gaussian* (less log-convex than the Gaussian/Wick
sequence, which has `R ≡ 1`) at every accessible depth. This establishes the char-0 half of the
`_StepRatioMonotone` reduction across the formalizable range; the deep-`r` char-`p` transfer (the
wraparound preserving the monotonicity at `r ≈ log p`) is the remaining open wall. -/
theorem charZero_stepRatio_monotone_r2_to_r7 {n : ℝ} (hn : 8 ≤ n) :
    (5 * E2 n * E4 n ≤ 7 * (E3 n)^2) ∧ (7 * E3 n * E5 n ≤ 9 * (E4 n)^2) ∧
      (9 * E4 n * E6 n ≤ 11 * (E5 n)^2) ∧ (11 * E5 n * E7 n ≤ 13 * (E6 n)^2) ∧
        (13 * E6 n * E8 n ≤ 15 * (E7 n)^2) ∧ (15 * E7 n * E9 n ≤ 17 * (E8 n)^2) :=
  ⟨charZero_stepRatio_monotone_r2 hn, charZero_stepRatio_monotone_r3 hn,
   charZero_stepRatio_monotone_r4 hn, charZero_stepRatio_monotone_r5 hn,
   charZero_stepRatio_monotone_r6 hn, charZero_stepRatio_monotone_r7 hn⟩

/-- Backward-compatible name for the already-landed r=2..6 bundle. -/
theorem charZero_stepRatio_monotone_r2_to_r6 {n : ℝ} (hn : 8 ≤ n) :
    (5 * E2 n * E4 n ≤ 7 * (E3 n)^2) ∧ (7 * E3 n * E5 n ≤ 9 * (E4 n)^2) ∧
      (9 * E4 n * E6 n ≤ 11 * (E5 n)^2) ∧ (11 * E5 n * E7 n ≤ 13 * (E6 n)^2) ∧
        (13 * E6 n * E8 n ≤ 15 * (E7 n)^2) := by
  exact ⟨(charZero_stepRatio_monotone_r2_to_r7 hn).1,
    (charZero_stepRatio_monotone_r2_to_r7 hn).2.1,
    (charZero_stepRatio_monotone_r2_to_r7 hn).2.2.1,
    (charZero_stepRatio_monotone_r2_to_r7 hn).2.2.2.1,
    (charZero_stepRatio_monotone_r2_to_r7 hn).2.2.2.2.1⟩

/-- Backward-compatible name for the already-landed r=2..5 bundle. -/
theorem charZero_stepRatio_monotone_r2_to_r5 {n : ℝ} (hn : 8 ≤ n) :
    (5 * E2 n * E4 n ≤ 7 * (E3 n)^2) ∧ (7 * E3 n * E5 n ≤ 9 * (E4 n)^2) ∧
      (9 * E4 n * E6 n ≤ 11 * (E5 n)^2) ∧ (11 * E5 n * E7 n ≤ 13 * (E6 n)^2) := by
  exact ⟨(charZero_stepRatio_monotone_r2_to_r7 hn).1,
    (charZero_stepRatio_monotone_r2_to_r7 hn).2.1,
    (charZero_stepRatio_monotone_r2_to_r7 hn).2.2.1,
    (charZero_stepRatio_monotone_r2_to_r7 hn).2.2.2.1⟩

end ArkLib.ProximityGap.CharZeroStepRatioMonotone

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.CharZeroStepRatioMonotone.charZero_stepRatio_monotone_r2
#print axioms ArkLib.ProximityGap.CharZeroStepRatioMonotone.charZero_stepRatio_monotone_r3
#print axioms ArkLib.ProximityGap.CharZeroStepRatioMonotone.charZero_stepRatio_monotone_r4
#print axioms ArkLib.ProximityGap.CharZeroStepRatioMonotone.charZero_stepRatio_monotone_r5
#print axioms ArkLib.ProximityGap.CharZeroStepRatioMonotone.charZero_stepRatio_monotone_r6
#print axioms ArkLib.ProximityGap.CharZeroStepRatioMonotone.charZero_stepRatio_monotone_r7
#print axioms ArkLib.ProximityGap.CharZeroStepRatioMonotone.charZero_stepRatio_monotone_r7_strict
#print axioms ArkLib.ProximityGap.CharZeroStepRatioMonotone.charZero_stepRatio_monotone_r2_strict
#print axioms ArkLib.ProximityGap.CharZeroStepRatioMonotone.charZero_stepRatio_monotone_r3_strict
#print axioms ArkLib.ProximityGap.CharZeroStepRatioMonotone.charZero_stepRatio_monotone_r4_strict
#print axioms ArkLib.ProximityGap.CharZeroStepRatioMonotone.charZero_stepRatio_monotone_r5_strict
#print axioms ArkLib.ProximityGap.CharZeroStepRatioMonotone.charZero_stepRatio_monotone_r6_strict
#print axioms ArkLib.ProximityGap.CharZeroStepRatioMonotone.charZero_stepRatio_strict_r2_to_r7

#print axioms ArkLib.ProximityGap.CharZeroStepRatioMonotone.charZero_stepRatio_monotone_r2_to_r7
#print axioms ArkLib.ProximityGap.CharZeroStepRatioMonotone.charZero_stepRatio_monotone_r2_to_r6
#print axioms ArkLib.ProximityGap.CharZeroStepRatioMonotone.charZero_stepRatio_monotone_r2_to_r5
