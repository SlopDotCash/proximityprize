/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Constant-index Gauss bound: solved lane and prize-regime barrier (#407)

`ConstantIndexGaussSumBound.lean` proves a genuine square-root cancellation theorem for a subgroup
cut out by a multiplicative character of order `m`:

`‖η_b(G_χ)‖ ≤ ((m - 1)√q + 1) / m`.

For fixed `m`, this is `O(√q) = O(√(m |G|))`, hence the index-2/constant-index lanes are solved by
classical Gauss sums.  This file records the complementary barrier: the same triangle-bound scale is
always at least `q/4` once `m ≥ 2`.  Thus the constant-index Gauss-sum method is structurally
incapable of producing the prize floor `O(|G| polylog q)` when the index `m = q/|G|` is large.

This is not a new open hypothesis; it is an axiom-clean arithmetic guardrail preventing the
index-2 success from being overgeneralized to the thin-subgroup prize regime.
-/

namespace ProximityGap.Frontier.ConstantIndexGaussBarrier

/-- The squared scale supplied by the constant-index Gauss-triangle bound. -/
noncomputable def constantIndexGaussScale (q m : ℝ) : ℝ :=
  (((m - 1) * Real.sqrt q + 1) / m) ^ 2

/--
The constant-index Gauss-triangle scale is bounded below by the principal Gauss part
`((m - 1) / m)^2 q`.
-/
theorem principal_part_le_constantIndexGaussScale {q m : ℝ} (hq : 0 ≤ q) (hm : 1 ≤ m) :
    ((m - 1) / m) ^ 2 * q ≤ constantIndexGaussScale q m := by
  have hmpos : 0 < m := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hm
  have hsqrt_nonneg : 0 ≤ Real.sqrt q := Real.sqrt_nonneg q
  have hprincipal_nonneg : 0 ≤ ((m - 1) * Real.sqrt q) / m := by
    have hmsub : 0 ≤ m - 1 := by linarith
    exact div_nonneg (mul_nonneg hmsub hsqrt_nonneg) (le_of_lt hmpos)
  have hle : ((m - 1) * Real.sqrt q) / m
      ≤ (((m - 1) * Real.sqrt q + 1) / m) := by
    rw [div_le_div_iff₀ hmpos hmpos]
    linarith
  calc
    ((m - 1) / m) ^ 2 * q
        = (((m - 1) * Real.sqrt q) / m) ^ 2 := by
          field_simp [hmpos.ne']
          rw [Real.sq_sqrt hq]
    _ ≤ (((m - 1) * Real.sqrt q + 1) / m) ^ 2 := by
          nlinarith
    _ = constantIndexGaussScale q m := rfl

/--
For every index `m ≥ 2`, the constant-index Gauss-triangle bound has squared scale at least `q/4`.
So when the desired prize scale is `|G| polylog q` and `|G| ≪ q`, this route is too large by a
factor comparable to the subgroup index.
-/
theorem quarter_fieldSize_le_constantIndexGaussScale {q m : ℝ} (hq : 0 ≤ q) (hm : 2 ≤ m) :
    q / 4 ≤ constantIndexGaussScale q m := by
  have hmpos : 0 < m := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hm
  have hhalf : (1 / 2 : ℝ) ≤ (m - 1) / m := by
    rw [le_div_iff₀ hmpos]
    nlinarith
  have hsq : (1 / 4 : ℝ) ≤ ((m - 1) / m) ^ 2 := by
    have hnonneg : 0 ≤ (1 / 2 : ℝ) := by norm_num
    nlinarith
  calc
    q / 4 = (1 / 4 : ℝ) * q := by ring
    _ ≤ ((m - 1) / m) ^ 2 * q := by
      exact mul_le_mul_of_nonneg_right hsq hq
    _ ≤ constantIndexGaussScale q m := principal_part_le_constantIndexGaussScale hq (by linarith)

/--
Square-root field-size bounds are above a target `C * n` exactly once `(C * n)^2 < q`.

This packages the arithmetic reason `√q`-scale Weil bounds are vacuous for the prize budget when
the proper subgroup size `n` is far below `√q`.
-/
theorem target_below_sqrt_fieldSize {q n C : ℝ}
    (hCn : 0 ≤ C * n) (hsmall : (C * n) ^ 2 < q) :
    C * n < Real.sqrt q :=
  (Real.lt_sqrt hCn).2 hsmall

/--
Exact subgroup-index version of `target_below_sqrt_fieldSize`.

If `q = m * n + 1` and `C^2 * n < m`, then the `√q` method scale is already larger than the
target `C * n`.  In the prize regime the index `m ≈ q/n` is polynomial in `n`, while acceptable
`C` is at most polylogarithmic, so this is the arithmetic obstruction behind the "Weil is
vacuous below `√q`" warning.
-/
theorem target_below_sqrt_fieldSize_of_index_dominates
    {q m n C : ℝ} (hq : q = m * n + 1) (hn : 0 < n) (hC : 0 ≤ C)
    (hdom : C ^ 2 * n < m) :
    C * n < Real.sqrt q := by
  have hCn : 0 ≤ C * n := mul_nonneg hC hn.le
  refine target_below_sqrt_fieldSize hCn ?_
  rw [hq]
  nlinarith [sq_nonneg C, sq_nonneg n]

/--
Idealized subgroup-size normalization of `quarter_fieldSize_le_constantIndexGaussScale`.

If `q = m * n`, then the constant-index Gauss-triangle scale is at least `(m / 4) * n`.
The exact multiplicative-subgroup relation is `q = m * n + 1`; see
`index_over_four_subgroupSize_le_constantIndexGaussScale_exact` below.
-/
theorem index_over_four_subgroupSize_le_constantIndexGaussScale
    {q m n : ℝ} (hq : q = m * n) (hn : 0 ≤ n) (hm : 2 ≤ m) :
    (m / 4) * n ≤ constantIndexGaussScale q m := by
  have hqnonneg : 0 ≤ q := by
    rw [hq]
    positivity
  calc
    (m / 4) * n = q / 4 := by rw [hq]; ring
    _ ≤ constantIndexGaussScale q m := quarter_fieldSize_le_constantIndexGaussScale hqnonneg hm

/--
Exact multiplicative-subgroup normalization.

If `n = |G|` and `m` is the index of `G ≤ Fˣ`, then the field size is `q = m * n + 1`.
The constant-index Gauss-triangle scale is still at least `(m / 4) * n`, with a spare `1/4`.
-/
theorem index_over_four_subgroupSize_le_constantIndexGaussScale_exact
    {q m n : ℝ} (hq : q = m * n + 1) (hn : 0 ≤ n) (hm : 2 ≤ m) :
    (m / 4) * n ≤ constantIndexGaussScale q m := by
  have hqnonneg : 0 ≤ q := by
    rw [hq]
    positivity
  calc
    (m / 4) * n ≤ q / 4 := by
      rw [hq]
      nlinarith
    _ ≤ constantIndexGaussScale q m := quarter_fieldSize_le_constantIndexGaussScale hqnonneg hm

/--
No target `C * n` below the index-loss floor can be proved by this constant-index triangle scale.

This is a statement about the **method's certified bound**, not the true Gauss-period optimum.
For prize thin subgroups the index `m` is enormous, while the desired multiplier `C` is only
polylogarithmic; this inequality records the resulting mismatch as a simple arithmetic guardrail.
-/
theorem target_below_index_loss_lt_constantIndexGaussScale
    {q m n C : ℝ} (hq : q = m * n) (hn : 0 < n) (hm : 2 ≤ m) (hC : C < m / 4) :
    C * n < constantIndexGaussScale q m := by
  have hfloor := index_over_four_subgroupSize_le_constantIndexGaussScale
    (q := q) (m := m) (n := n) hq (le_of_lt hn) hm
  have htarget : C * n < (m / 4) * n := by
    exact mul_lt_mul_of_pos_right hC hn
  exact lt_of_lt_of_le htarget hfloor

/--
Exact multiplicative-subgroup version of `target_below_index_loss_lt_constantIndexGaussScale`.
When `q = m * n + 1`, every target below `(m/4) n` is below the constant-index triangle scale.
-/
theorem target_below_index_loss_lt_constantIndexGaussScale_exact
    {q m n C : ℝ} (hq : q = m * n + 1) (hn : 0 < n) (hm : 2 ≤ m) (hC : C < m / 4) :
    C * n < constantIndexGaussScale q m := by
  have hfloor := index_over_four_subgroupSize_le_constantIndexGaussScale_exact
    (q := q) (m := m) (n := n) hq (le_of_lt hn) hm
  have htarget : C * n < (m / 4) * n := by
    exact mul_lt_mul_of_pos_right hC hn
  exact lt_of_lt_of_le htarget hfloor

/--
Contrapositive-friendly form of the same barrier in the idealized normalization.
If the constant-index Gauss-triangle scale fits a squared target `C * n`, then the index is
forced below the target multiplier: `m / 4 ≤ C`.
-/
theorem index_le_four_targetMultiplier_of_constantIndexGaussScale_le_target
    {q m n C : ℝ} (hq : q = m * n) (hn : 0 < n) (hm : 2 ≤ m)
    (hfit : constantIndexGaussScale q m ≤ C * n) :
    m / 4 ≤ C := by
  have hfloor := index_over_four_subgroupSize_le_constantIndexGaussScale
    (q := q) (m := m) (n := n) hq (le_of_lt hn) hm
  have hmul : (m / 4) * n ≤ C * n := le_trans hfloor hfit
  nlinarith

/--
Exact multiplicative-subgroup form of
`index_le_four_targetMultiplier_of_constantIndexGaussScale_le_target`.

Thus any argument whose only input is the constant-index Gauss-triangle scale can meet a prize
target `C * n` only when the subgroup index is `O(C)`.  In the prize thin-subgroup regime the
index is polynomial in `n`, while `C` is only polylogarithmic.
-/
theorem index_le_four_targetMultiplier_of_constantIndexGaussScale_le_target_exact
    {q m n C : ℝ} (hq : q = m * n + 1) (hn : 0 < n) (hm : 2 ≤ m)
    (hfit : constantIndexGaussScale q m ≤ C * n) :
    m / 4 ≤ C := by
  have hfloor := index_over_four_subgroupSize_le_constantIndexGaussScale_exact
    (q := q) (m := m) (n := n) hq (le_of_lt hn) hm
  have hmul : (m / 4) * n ≤ C * n := le_trans hfloor hfit
  nlinarith

/--
Field-size normalization of the same obstruction.  If a desired target `C * n` lies below `q/4`,
then it is below the constant-index Gauss-triangle scale for every index `m ≥ 2`.

This is the form closest to the prize budget: the classical fixed-index Gauss triangle method proves
a scale comparable to `q`, whereas the prize target is comparable to the subgroup size `n` times a
small multiplier.
-/
theorem target_below_quarter_fieldSize_lt_constantIndexGaussScale
    {q m n C : ℝ} (hqnonneg : 0 ≤ q) (hm : 2 ≤ m) (hC : C * n < q / 4) :
    C * n < constantIndexGaussScale q m :=
  lt_of_lt_of_le hC (quarter_fieldSize_le_constantIndexGaussScale hqnonneg hm)

#print axioms principal_part_le_constantIndexGaussScale
#print axioms quarter_fieldSize_le_constantIndexGaussScale
#print axioms target_below_sqrt_fieldSize
#print axioms target_below_sqrt_fieldSize_of_index_dominates
#print axioms index_over_four_subgroupSize_le_constantIndexGaussScale
#print axioms index_over_four_subgroupSize_le_constantIndexGaussScale_exact
#print axioms target_below_index_loss_lt_constantIndexGaussScale
#print axioms target_below_index_loss_lt_constantIndexGaussScale_exact
#print axioms index_le_four_targetMultiplier_of_constantIndexGaussScale_le_target
#print axioms index_le_four_targetMultiplier_of_constantIndexGaussScale_le_target_exact
#print axioms target_below_quarter_fieldSize_lt_constantIndexGaussScale

end ProximityGap.Frontier.ConstantIndexGaussBarrier
