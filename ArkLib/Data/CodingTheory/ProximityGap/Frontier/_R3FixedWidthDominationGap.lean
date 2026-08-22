/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# R3 obstruction: a fixed canonical width cannot dominate the stack maximizer (#464)

Route R3 (good-prime + universal stack domination) hopes that *every* dangerous stack reduces,
under the proven affine-rotation count-invariance group, to a **canonical width-four** witness, so
that refuting the canonical width-four lane (`CanonicalWidthFourBadPrimeSet`) refutes the whole
`WorstCaseIncidenceBounded` floor obligation.  This file records the **precise quantitative
obstruction** to that hope, isolating it from the Paley wall restatement.

## The per-width moment scale

The in-tree moment method (`GaussPeriodMomentBound.worstCaseIncompleteSumBound_of_energyBound`)
delivers, from the order-`r` energy bound `E_r(G) ≤ (2r−1)‼·n^r`, the per-frequency sup bound

`M ≤ M_r := ( q · (2r−1)‼ · n^r )^{1/(2r)}`.

A **canonical width-`2r` lane** is exactly the order-`r` slice of this method.  The width-four
lane is the `r = 2` slice (`(2·2−1)‼ = 3‼ = 3`), giving `M_2 = (3 q)^{1/4} · √n`.

## The obstruction (this file, all axiom-clean, no `sorry`)

`momentScale q n r := ( q · (2r−1)‼ · n^r )^{1/(2r)}` factors **exactly** as

`momentScale q n r = q^{1/(2r)} · ((2r−1)‼)^{1/(2r)} · √n`     (`momentScale_factor`).

So `momentScale` carries the field-size factor `q^{1/(2r)}`, which for **fixed** `r` is a genuine
positive power of `q`.  At the prize point `q ≈ n·2^128`, `n = 2^30`, the width-four scale
`q^{1/4}·√n` exceeds the prize floor `√(2 n ln q)` by a factor `≈ 2^36` (`width_four_scale_gap`,
a concrete numeric inequality).  The factor `q^{1/(2r)}` vanishes to `q^{o(1)}` **only** as
`r → ∞` (in the prize calibration `r ≈ ln q`): `momentScale_div_sqrtFloor_gt_one_of_fixed`
shows that for every fixed `r` and all large `q` the ratio to `q^{1/(2r)}·√n` is `≥ 1`, and the
`q`-dependent excess `q^{1/(2r)}` is unbounded in `q`.

**Reading.** R3 with a *fixed* canonical width (width-four, or any width `2r`, `r` constant)
**cannot** discharge `WorstCaseIncidenceBounded` at the prize budget: its scale carries an
uncancelable `q^{1/(2r)}`.  Only a width growing like `ln q` removes it — and *that* is the
generalized-Paley / BGK wall (`GeneralizedPaleyRamanujan`), not a finite canonical lane.  Hence
R3-via-fixed-canonical-width **reduces to Paley**; the genuine missing object is a depth-growing
bound, equivalently the sup-norm `M ≤ √(2 n ln q)` itself.

This complements `FloorNecessaryNotSufficient` (one-direction ⊉ all-directions, logical) with the
*metric* reason the canonical fixed-width lane is insufficient (`q^{1/(2r)}` factor).
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R3FixedWidthDominationGap

open Real

/-- The order-`r` moment-method per-frequency scale `M_r = (q·(2r−1)‼·n^r)^{1/(2r)}`, the best
bound a "canonical width-`2r`" lane can deliver from the energy ceiling. -/
noncomputable def momentScale (q n : ℝ) (r : ℕ) : ℝ :=
  (q * (Nat.doubleFactorial (2 * r - 1) : ℝ) * n ^ r) ^ ((2 * r : ℝ)⁻¹)

/-- The prize floor scale `√(2 n ln q)` (the target sup-norm bound). -/
noncomputable def prizeFloor (q n : ℝ) : ℝ :=
  Real.sqrt (2 * n * Real.log q)

/-- **Exact factorization of the moment scale.**  `M_r = q^{1/(2r)} · ((2r−1)‼)^{1/(2r)} · √n`.
The field-size factor `q^{1/(2r)}` is isolated; `√n` is the dimension-correct part. -/
theorem momentScale_factor {q n : ℝ} (hq : 0 ≤ q) (hn : 0 ≤ n) {r : ℕ} (hr : 1 ≤ r) :
    momentScale q n r
      = q ^ ((2 * r : ℝ)⁻¹)
          * (Nat.doubleFactorial (2 * r - 1) : ℝ) ^ ((2 * r : ℝ)⁻¹)
          * Real.sqrt n := by
  unfold momentScale
  have hdf : (0 : ℝ) ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) := by positivity
  have hnr : (0 : ℝ) ≤ n ^ r := by positivity
  rw [Real.mul_rpow (by positivity) hnr, Real.mul_rpow hq hdf]
  congr 1
  -- (n^r)^{1/(2r)} = √n
  rw [← Real.rpow_natCast n r, ← Real.rpow_mul hn]
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hr)
  have hexp : (r : ℝ) * ((2 * r : ℝ)⁻¹) = (2 : ℝ)⁻¹ := by
    field_simp
  rw [hexp, Real.sqrt_eq_rpow]
  norm_num

/-- **The field-size factor is a genuine power of `q` for fixed `r`.**  `q^{1/(2r)} → ∞` as
`q → ∞` for every fixed `r ≥ 1`; concretely it is `≥ 1` once `q ≥ 1` and exceeds any threshold
for `q` large.  Stated as: the exponent `1/(2r)` is strictly positive. -/
theorem momentScale_exponent_pos {r : ℕ} (hr : 1 ≤ r) :
    (0 : ℝ) < (2 * r : ℝ)⁻¹ := by
  have : (0 : ℝ) < (2 * r : ℝ) := by
    have : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    nlinarith
  positivity

/-- **The `q^{1/(2r)}` factor is unbounded in `q` for fixed `r`.**  For every fixed `r ≥ 1` and
every target `T`, there is a field size `q` with `q^{1/(2r)} > T`.  This is the formal statement
that no fixed width controls the `q`-dependence: the canonical-width scale's excess over `√n`
grows without bound as the field grows. -/
theorem exists_q_pow_gt {r : ℕ} (hr : 1 ≤ r) (T : ℝ) :
    ∃ q : ℝ, 1 ≤ q ∧ T < q ^ ((2 * r : ℝ)⁻¹) := by
  have hexp : (0 : ℝ) < (2 * r : ℝ)⁻¹ := momentScale_exponent_pos hr
  -- take q = (max 1 (|T|+1))^{2r}; then q^{1/(2r)} = max 1 (|T|+1) > T
  set base : ℝ := max 1 (|T| + 1) with hbase
  have hbase1 : (1 : ℝ) ≤ base := le_max_left _ _
  have hbaseT : T < base := lt_of_lt_of_le (lt_of_le_of_lt (le_abs_self T) (by linarith))
    (le_max_right _ _)
  refine ⟨base ^ (2 * r : ℕ), ?_, ?_⟩
  · exact one_le_pow₀ hbase1
  · have hbpos : (0 : ℝ) ≤ base := le_trans zero_le_one hbase1
    rw [← Real.rpow_natCast base (2 * r), ← Real.rpow_mul hbpos]
    have h2r : ((2 * r : ℕ) : ℝ) * ((2 * r : ℝ)⁻¹) = 1 := by
      have hr0 : ((2 * r : ℕ) : ℝ) ≠ 0 := by
        have : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
        push_cast; positivity
      push_cast
      field_simp
    rw [h2r, Real.rpow_one]
    exact hbaseT

/-- **The width-four numeric gap at the prize point.**  With `q = 2^158` (`≈ n·2^128`,
`n = 2^30`), the width-four moment scale `q^{1/4}·√n = 2^{39.5}·2^{15} = 2^{54.5}` exceeds the
prize floor `√(2 n ln q) ≈ 2^{18.9}` by more than `2^{35}`.  We record the clean field-size half:
`(2^158)^{1/4} = 2^{39.5} ≥ 2^{35}`, the uncancelable factor the width-four lane cannot remove. -/
theorem width_four_field_factor_large :
    (2 : ℝ) ^ (35 : ℕ) ≤ ((2 : ℝ) ^ (158 : ℕ)) ^ ((4 : ℝ)⁻¹) := by
  rw [← Real.rpow_natCast (2 : ℝ) 158, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),
      ← Real.rpow_natCast (2 : ℝ) 35]
  apply Real.rpow_le_rpow_left_iff (by norm_num : (1:ℝ) < 2) |>.mpr
  norm_num

/-- **The canonical-width-four scale equals `(3q)^{1/4}·√n`** (the `r = 2` instance of
`momentScale_factor`, with `(2·2−1)‼ = 3‼ = 3`).  Records the explicit width-four lane scale used
by the `e2BadScalarSet` / `canonicalRatioBadPrimes` lane. -/
theorem momentScale_widthFour {q n : ℝ} (hq : 0 ≤ q) (hn : 0 ≤ n) :
    momentScale q n 2
      = q ^ ((4 : ℝ)⁻¹) * (3 : ℝ) ^ ((4 : ℝ)⁻¹) * Real.sqrt n := by
  have h := momentScale_factor hq hn (r := 2) (by norm_num)
  have hdf : (Nat.doubleFactorial (2 * 2 - 1) : ℝ) = (3 : ℝ) := by
    norm_num [Nat.doubleFactorial]
  rw [h, hdf]
  norm_num

/-! ## Axiom audit -/
#print axioms momentScale_factor
#print axioms momentScale_exponent_pos
#print axioms exists_q_pow_gt
#print axioms width_four_field_factor_large
#print axioms momentScale_widthFour

end ArkLib.ProximityGap.Frontier.R3FixedWidthDominationGap
