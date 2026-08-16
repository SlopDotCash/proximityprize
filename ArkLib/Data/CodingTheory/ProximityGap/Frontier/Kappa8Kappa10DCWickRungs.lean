/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# The r=4 and r=5 DC-Wick rungs: `E₄, E₅` closed forms, `κ₈ = −1155 n`, `κ₁₀ = 57456 n` (#444)

This file extends AVENUE A (`Frontier/CharZeroEnergyThreeExact.lean`, the verified `r = 3` rung)
to the **`r = 4` and `r = 5` rungs** of the DC-subtracted moment-Wick ladder consumed by
`Frontier/DCWickMGFFromTermwise.lean`.  Same method: model the class-balanced count by an abstract
carrier `B : ℕ → ℕ → ℤ` satisfying the *add-one-class* recursion, solve the recursion in closed form
by induction on `m`, and read off the exact char-0 additive energies and cumulants.

## The add-one-class recursion (probe `scripts/probes/probe_b8b10_dcwick_rungs.py`)

`B k m` = the number of *class-balanced* length-`k` tuples over `m` antipodal classes `{z,−z}`
(each class used with as many `+`'s as `−`'s).  Under the Lam–Leung depth-`≤r` balance
characterization this is exactly the zero-sum count `E_{k/2}(μ_{2m})`.  A new class occupies an even
number `2j` of the `k` positions, with `j` `+`'s and `j` `−`'s among them, giving
`B k (m+1) = Σ_j C(k,2j)·C(2j,j)·B (k−2j) m`.  For `k = 8, 10` (extending `rec2/rec4/rec6`):

* `rec8  : B 8  (m+1) = B 8  m + 56·B 6 m + 420·B 4 m  + 560·B 2 m + 70`
  (coeffs `C(8,2)C(2,1)=56, C(8,4)C(4,2)=420, C(8,6)C(6,3)=560, C(8,8)C(8,4)=70`).
* `rec10 : B 10 (m+1) = B 10 m + 90·B 8 m + 1260·B 6 m + 4200·B 4 m + 3150·B 2 m + 252`
  (coeffs `C(10,2)C(2,1)=90, C(10,4)C(4,2)=1260, C(10,6)C(6,3)=4200, C(10,8)C(8,4)=3150,
  C(10,10)C(10,5)=252`).

Both recursions are exact ring-identities on the closed forms below (probe: `rec8/rec10` residual `0`),
and brute-force verified `B 8 m, B 10 m` for `m = 0,1,2` (`probe_b8b10_dcwick_rungs.py`).

## What THIS file proves (axiom-clean; only inputs = the elementary recursion fields)

Solving the recursion (`B 2 m = 2m`, `B 4 m = 12m²−6m`, `B 6 m = 120m³−180m²+80m` reproved as
lemmas, then):

* `B8_closed`  : `B 8 m  = 1680m⁴ − 5040m³ + 5740m² − 2310m`,
* `B10_closed` : `B 10 m = 30240m⁵ − 151200m⁴ + 315000m³ − 308700m² + 114912m`,
* `B8_eq_E4`   : `B 8 m  = 105n⁴ − 630n³ + 1435n² − 1155n`   (`n = 2m`) — the depth-4 energy,
* `B10_eq_E5`  : `B 10 m = 945n⁵ − 9450n⁴ + 39375n³ − 77175n² + 57456n` (`n = 2m`) — depth-5 energy.

Cumulant consequences (mean-0 symmetric inversion of moments `μ_{2r}=E_r`, `μ_odd=0`, derived by
inverting `exp(K)` symbolically — see probe; the common `−9450/+9450` `κ₁₀` table is WRONG and was
corrected here to `−18900/+22680`):

* `kappa8_eq`  : `E₄ − 28 E₃ E₁ − 35 E₂² + 420 E₂ E₁² − 630 E₁⁴ = −1155 n`  — **`κ₈ = −1155 n`**,
* `kappa10_eq` : `E₅ − 45 E₄ E₁ − 210 E₃ E₂ + 1260 E₃ E₁² + 3150 E₂² E₁ − 18900 E₂ E₁³ + 22680 E₁⁵
  = 57456 n` — **`κ₁₀ = 57456 n`**.

Both cumulants are **EXACTLY LINEAR** in `n` (the structural reason: `κ_{2r}` = connected
balanced-config count; connected antipodal-pair configs over `μ_{2^μ}` are `O(n)`).  All the higher
powers `n²…n⁵` of `E₄, E₅` cancel against the lower-energy products.

Energy-level Wick-budget rungs (the actual `DCWickBound` energy face `E_r ≤ (2r−1)‼·n^r`):

* `E4_le_wick`  : `E₄ ≤ 105 n⁴`  for `n ≥ 1`  (`105 = 7‼`),
* `E5_le_wick`  : `E₅ ≤ 945 n⁵`  for `n ≥ 2`  (`945 = 9‼`; FAILS at `n = 1` by `10206`, holds on the
  dyadic regime `n = 2^μ ≥ 2`).

## Honest status (REDUCTION of two more ladder inputs, NOT a CORE closure)

These are the `r = 4, 5` rungs of the DC-Wick ladder.  Like the `r = 3` rung, they rest only on
(i) the Lam–Leung depth-`≤5` balance characterization and (ii) the add-one-class counting recursion
— both elementary, field-theory-free, probe-verified.  The deep BGK/Paley wall (the char-`p`
transfer of these char-0 bounds to depth `r ≈ log m`) is UNTOUCHED; the prize CORE of #444 stays
OPEN.  These rungs FORMALIZE more of the char-0 ladder, matching the closed-form breakthrough
`κ_{2r} = c_r·n` for `r = 4, 5`.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`.  Issue #444 / #389.
-/

namespace ArkLib.ProximityGap.Frontier.Kappa8Kappa10

/-- **The balanced-class-count carrier through depth 5.** `B k m` is the number of *class-balanced*
length-`k` tuples over `m` antipodal classes (each class `{+,−}` used with equal `+`/`−`
multiplicity); by the Lam–Leung balance characterization this is the zero-sum count
`E_{k/2}(μ_{2m})`.  The structure records the base case and the *add-one-class* recursions for
`k = 2, 4, 6, 8, 10` (a new class occupies `2j` positions with `j` `+`'s and `j` `−`'s, contributing
`C(k,2j)·C(2j,j)·B (k−2j) m`). -/
structure BalancedCount (B : ℕ → ℕ → ℤ) : Prop where
  /-- No classes ⟹ no nonempty balanced tuple. -/
  base0 : ∀ k, 1 ≤ k → B k 0 = 0
  /-- `B 2 (m+1) = B 2 m + C(2,2)·C(2,1)`. -/
  rec2 : ∀ m, B 2 (m + 1) = B 2 m + 2
  /-- `B 4 (m+1) = B 4 m + C(4,2)C(2,1)·B 2 m + C(4,4)C(4,2)`. -/
  rec4 : ∀ m, B 4 (m + 1) = B 4 m + 12 * B 2 m + 6
  /-- `B 6 (m+1) = B 6 m + C(6,2)C(2,1)·B 4 m + C(6,4)C(4,2)·B 2 m + C(6,6)C(6,3)`. -/
  rec6 : ∀ m, B 6 (m + 1) = B 6 m + 30 * B 4 m + 90 * B 2 m + 20
  /-- `B 8 (m+1) = B 8 m + C(8,2)C(2,1)·B 6 m + C(8,4)C(4,2)·B 4 m + C(8,6)C(6,3)·B 2 m + C(8,8)C(8,4)`
      `= B 8 m + 56·B 6 m + 420·B 4 m + 560·B 2 m + 70`. -/
  rec8 : ∀ m, B 8 (m + 1) = B 8 m + 56 * B 6 m + 420 * B 4 m + 560 * B 2 m + 70
  /-- `B 10 (m+1) = B 10 m + 90·B 8 m + 1260·B 6 m + 4200·B 4 m + 3150·B 2 m + 252`
      (coeffs `C(10,2)C(2,1), C(10,4)C(4,2), C(10,6)C(6,3), C(10,8)C(8,4), C(10,10)C(10,5)`). -/
  rec10 : ∀ m, B 10 (m + 1) = B 10 m + 90 * B 8 m + 1260 * B 6 m + 4200 * B 4 m + 3150 * B 2 m + 252

variable {B : ℕ → ℕ → ℤ}

/-- **`B 2 m = 2m`** — depth-1 energy `E₁(μ_{2m}) = n` (`n = 2m`). -/
theorem B2_closed (h : BalancedCount B) (m : ℕ) : B 2 m = 2 * m := by
  induction m with
  | zero => simpa using h.base0 2 (by norm_num)
  | succ k ih => rw [h.rec2 k, ih]; push_cast; ring

/-- **`B 4 m = 12m² − 6m`** — depth-2 energy `E₂(μ_{2m}) = 3n² − 3n`. -/
theorem B4_closed (h : BalancedCount B) (m : ℕ) : B 4 m = 12 * (m : ℤ) ^ 2 - 6 * m := by
  induction m with
  | zero => simpa using h.base0 4 (by norm_num)
  | succ k ih => rw [h.rec4 k, ih, B2_closed h k]; push_cast; ring

/-- **`B 6 m = 120m³ − 180m² + 80m`** — depth-3 energy `E₃(μ_{2m}) = 15n³ − 45n² + 40n`. -/
theorem B6_closed (h : BalancedCount B) (m : ℕ) :
    B 6 m = 120 * (m : ℤ) ^ 3 - 180 * (m : ℤ) ^ 2 + 80 * m := by
  induction m with
  | zero => simpa using h.base0 6 (by norm_num)
  | succ k ih => rw [h.rec6 k, ih, B4_closed h k, B2_closed h k]; push_cast; ring

/-- **`B 8 m = 1680m⁴ − 5040m³ + 5740m² − 2310m`** — the depth-4 energy, solving `rec8` with the
lower closed forms.  With `n = 2m` this is `105n⁴ − 630n³ + 1435n² − 1155n` (`B8_eq_E4`). -/
theorem B8_closed (h : BalancedCount B) (m : ℕ) :
    B 8 m = 1680 * (m : ℤ) ^ 4 - 5040 * (m : ℤ) ^ 3 + 5740 * (m : ℤ) ^ 2 - 2310 * m := by
  induction m with
  | zero => simpa using h.base0 8 (by norm_num)
  | succ k ih => rw [h.rec8 k, ih, B6_closed h k, B4_closed h k, B2_closed h k]; push_cast; ring

/-- **`B 10 m = 30240m⁵ − 151200m⁴ + 315000m³ − 308700m² + 114912m`** — the depth-5 energy, solving
`rec10` with the lower closed forms.  With `n = 2m` this is
`945n⁵ − 9450n⁴ + 39375n³ − 77175n² + 57456n` (`B10_eq_E5`). -/
theorem B10_closed (h : BalancedCount B) (m : ℕ) :
    B 10 m = 30240 * (m : ℤ) ^ 5 - 151200 * (m : ℤ) ^ 4 + 315000 * (m : ℤ) ^ 3
      - 308700 * (m : ℤ) ^ 2 + 114912 * m := by
  induction m with
  | zero => simpa using h.base0 10 (by norm_num)
  | succ k ih =>
    rw [h.rec10 k, ih, B8_closed h k, B6_closed h k, B4_closed h k, B2_closed h k]
    push_cast; ring

/-- **Depth-4 energy: `E₄(μ_n) = 105n⁴ − 630n³ + 1435n² − 1155n`** (`n = 2m`).  From `B8_closed`. -/
theorem B8_eq_E4 (h : BalancedCount B) (m : ℕ) :
    B 8 m = 105 * (2 * (m : ℤ)) ^ 4 - 630 * (2 * (m : ℤ)) ^ 3 + 1435 * (2 * (m : ℤ)) ^ 2
      - 1155 * (2 * (m : ℤ)) := by
  rw [B8_closed h]; ring

/-- **Depth-5 energy: `E₅(μ_n) = 945n⁵ − 9450n⁴ + 39375n³ − 77175n² + 57456n`** (`n = 2m`).  From
`B10_closed`. -/
theorem B10_eq_E5 (h : BalancedCount B) (m : ℕ) :
    B 10 m = 945 * (2 * (m : ℤ)) ^ 5 - 9450 * (2 * (m : ℤ)) ^ 4 + 39375 * (2 * (m : ℤ)) ^ 3
      - 77175 * (2 * (m : ℤ)) ^ 2 + 57456 * (2 * (m : ℤ)) := by
  rw [B10_closed h]; ring

/-- **`κ₈ = −1155 n`, unconditional on the closed-form energies.** The mean-0 symmetric 8th cumulant
`κ₈ = E₄ − 28 E₃ E₁ − 35 E₂² + 420 E₂ E₁² − 630 E₁⁴` with `E₁ = n`, `E₂ = 3n²−3n`, `E₃ =
15n³−45n²+40n`, `E₄ = 105n⁴−630n³+1435n²−1155n` equals `−1155 n`: every power `n²…n⁴` cancels,
leaving the bare linear `−1155 n`.  Pure algebra (probe-verified). -/
theorem kappa8_eq (n : ℝ) :
    (105 * n ^ 4 - 630 * n ^ 3 + 1435 * n ^ 2 - 1155 * n)
      - 28 * (15 * n ^ 3 - 45 * n ^ 2 + 40 * n) * n
      - 35 * (3 * n ^ 2 - 3 * n) ^ 2
      + 420 * (3 * n ^ 2 - 3 * n) * n ^ 2
      - 630 * n ^ 4 = -1155 * n := by
  ring

/-- **`κ₁₀ = 57456 n`, unconditional on the closed-form energies.** The mean-0 symmetric 10th cumulant
`κ₁₀ = E₅ − 45 E₄ E₁ − 210 E₃ E₂ + 1260 E₃ E₁² + 3150 E₂² E₁ − 18900 E₂ E₁³ + 22680 E₁⁵` with the five
closed-form energies equals `57456 n`: every power `n²…n⁵` cancels, leaving the bare linear
`57456 n`.  (The `−18900/+22680` coefficients are the CORRECT cumulant-inversion values, derived by
inverting `exp(K)`; the common `−9450/+9450` table is wrong and leaves a spurious `n⁵, n⁴` residual.)
Pure algebra (probe-verified). -/
theorem kappa10_eq (n : ℝ) :
    (945 * n ^ 5 - 9450 * n ^ 4 + 39375 * n ^ 3 - 77175 * n ^ 2 + 57456 * n)
      - 45 * (105 * n ^ 4 - 630 * n ^ 3 + 1435 * n ^ 2 - 1155 * n) * n
      - 210 * (15 * n ^ 3 - 45 * n ^ 2 + 40 * n) * (3 * n ^ 2 - 3 * n)
      + 1260 * (15 * n ^ 3 - 45 * n ^ 2 + 40 * n) * n ^ 2
      + 3150 * (3 * n ^ 2 - 3 * n) ^ 2 * n
      - 18900 * (3 * n ^ 2 - 3 * n) * n ^ 3
      + 22680 * n ^ 5 = 57456 * n := by
  ring

/-- **Exact r=4 Wick slack.**  The depth-4 char-0 closed form is below the Wick budget by
`630n³ − 1435n² + 1155n`.  This is the arithmetic identity used by `E4_le_wick`, recorded as a
separate reusable bookkeeping lemma so later DC-Wick slack arguments can rewrite the gap exactly. -/
theorem E4_wick_slack_eq (n : ℝ) :
    105 * n ^ 4 - (105 * n ^ 4 - 630 * n ^ 3 + 1435 * n ^ 2 - 1155 * n)
      = 630 * n ^ 3 - 1435 * n ^ 2 + 1155 * n := by
  ring

/-- **Exact r=5 Wick slack in the dyadic-valid shifted form.**  The depth-5 Wick gap factors as
`n` times a polynomial in `t = n - 2` with positive coefficients.  This packages the positivity
certificate used by `E5_le_wick`; in the dyadic regime `n = 2^μ ≥ 2`, every displayed term is
nonnegative and the constant term is strictly positive. -/
theorem E5_wick_slack_shift_eq (n : ℝ) :
    945 * n ^ 5
        - (945 * n ^ 5 - 9450 * n ^ 4 + 39375 * n ^ 3 - 77175 * n ^ 2 + 57456 * n)
      = n * (9450 * (n - 2) ^ 3 + 17325 * (n - 2) ^ 2 + 33075 * (n - 2) + 14994) := by
  ring

/-- **The r=4 energy Wick-budget rung: `E₄ ≤ 105 n⁴`** for `n ≥ 1** (`105 = 7‼`).  The slack
`105n⁴ − E₄ = 630n³ − 1435n² + 1155n = n(630n² − 1435n + 1155)` is positive: the quadratic
`630n² − 1435n + 1155` has negative discriminant (`1435² − 4·630·1155 < 0`), so it is positive for
all real `n`.  Pure arithmetic. -/
theorem E4_le_wick (n : ℝ) (hn : 1 ≤ n) :
    105 * n ^ 4 - 630 * n ^ 3 + 1435 * n ^ 2 - 1155 * n ≤ 105 * n ^ 4 := by
  nlinarith [hn, sq_nonneg (n - 1), sq_nonneg n, mul_nonneg (by linarith : (0:ℝ) ≤ n)
    (sq_nonneg (n - 1))]

/-- **The r=5 energy Wick-budget rung: `E₅ ≤ 945 n⁵`** for `n ≥ 2` (`945 = 9‼`).  The slack
`945n⁵ − E₅ = 9450n⁴ − 39375n³ + 77175n² − 57456n = n·(9450n³ − 39375n² + 77175n − 57456)`; the cubic
factor `c(n) = 9450n³ − 39375n² + 77175n − 57456`, written in `t = n − 2`, is
`9450t³ + 17325t² + 33075t + 14994` with all positive coefficients, hence `c(n) > 0` for `n ≥ 2`.
(At `n = 1` the budget FAILS by `10206`; the dyadic regime `n = 2^μ ≥ 2` is exactly the valid range.)
Pure arithmetic. -/
theorem E5_le_wick (n : ℝ) (hn : 2 ≤ n) :
    945 * n ^ 5 - 9450 * n ^ 4 + 39375 * n ^ 3 - 77175 * n ^ 2 + 57456 * n ≤ 945 * n ^ 5 := by
  have ht : (0:ℝ) ≤ n - 2 := by linarith
  nlinarith [ht, mul_nonneg ht (sq_nonneg (n - 2)), sq_nonneg (n - 2),
    mul_nonneg (by linarith : (0:ℝ) ≤ n) ht, mul_nonneg (by linarith : (0:ℝ) ≤ n)
      (mul_nonneg ht (sq_nonneg (n - 2)))]

end ArkLib.ProximityGap.Frontier.Kappa8Kappa10

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.Kappa8Kappa10.B8_closed
#print axioms ArkLib.ProximityGap.Frontier.Kappa8Kappa10.B10_closed
#print axioms ArkLib.ProximityGap.Frontier.Kappa8Kappa10.B8_eq_E4
#print axioms ArkLib.ProximityGap.Frontier.Kappa8Kappa10.B10_eq_E5
#print axioms ArkLib.ProximityGap.Frontier.Kappa8Kappa10.kappa8_eq
#print axioms ArkLib.ProximityGap.Frontier.Kappa8Kappa10.kappa10_eq
#print axioms ArkLib.ProximityGap.Frontier.Kappa8Kappa10.E4_wick_slack_eq
#print axioms ArkLib.ProximityGap.Frontier.Kappa8Kappa10.E5_wick_slack_shift_eq
#print axioms ArkLib.ProximityGap.Frontier.Kappa8Kappa10.E4_le_wick
#print axioms ArkLib.ProximityGap.Frontier.Kappa8Kappa10.E5_le_wick
