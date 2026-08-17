/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._PhaseLinearFormDecoupling

/-!
# Door-IV pair-discrepancy budget for the phase-linear form (#444)

`_PhaseLinearFormDecoupling` names the honest open residual `PairEquidistributed φ δ` and proves the
variance proxy

`avg η² ≤ 2m + 2δ · m(2m-1)`.

This file repackages that inequality in the normalized prize-budget form.  Dividing by the prize proxy
`2m = n`, the entire remaining door-(iv) obligation is the dimensionless correction

`δ · (2m-1)`.

So the pair-discrepancy residual must be at the `O(1/m)` scale to keep the variance within a constant
multiple of the Plancherel/prize floor.  This is a reduction/constraint only: it proves no new
anti-concentration, no CORE cancellation, and no capacity claim.
-/

set_option linter.style.longLine false
set_option autoImplicit false


namespace ArkLib.ProximityGap.Frontier.PhasePairEquidistBudget

open ArkLib.ProximityGap.Frontier.PhaseLinearFormDecoupling

variable {B : Type*} [Fintype B] [Nonempty B]

/-- The prize variance proxy attached to `m = n/2` antipodal phase pairs: `2m = n`. -/
def prizeVarianceProxy (m : ℕ) : ℝ := 2 * (m : ℝ)

/-- The pair-discrepancy correction in `_PhaseLinearFormDecoupling.variance_le_of_pairEquidist`. -/
def pairResidualCorrection (m : ℕ) (δ : ℝ) : ℝ := 2 * δ * ((m : ℝ) * (2 * (m : ℝ) - 1))

/-- **Pair-discrepancy budget, exact normalized form.**  Dividing by the prize proxy `2m`,
the decoupling theorem gives the dimensionless bound `1 + δ(2m-1)`.

This states the door-(iv) residual without hiding any scale factor: keeping the normalized variance
`O(1)` is exactly the requirement that `δ(2m-1)` stay `O(1)`. -/
theorem normalized_variance_le_one_add_pairResidual {m : ℕ} (hm : 0 < m)
    (φ : Fin m → B → ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (hpair : PairEquidistributed φ δ) :
    avg (fun b => (∑ k : Fin m, 2 * Real.cos (φ k b)) ^ 2) / prizeVarianceProxy m
      ≤ 1 + δ * (2 * (m : ℝ) - 1) := by
  have hbase := variance_le_of_pairEquidist (B := B) φ δ hδ hpair
  have hproxy_pos : 0 < prizeVarianceProxy m := by
    unfold prizeVarianceProxy
    positivity
  calc
    avg (fun b => (∑ k : Fin m, 2 * Real.cos (φ k b)) ^ 2) / prizeVarianceProxy m
        ≤ (2 * (m : ℝ) + 2 * δ * ((m : ℝ) * (2 * (m : ℝ) - 1))) / prizeVarianceProxy m :=
      div_le_div_of_nonneg_right hbase (le_of_lt hproxy_pos)
    _ = 1 + δ * (2 * (m : ℝ) - 1) := by
      have hm2 : (2 * (m : ℝ)) ≠ 0 := by positivity
      unfold prizeVarianceProxy
      field_simp [hm2]

/-- **Pair-discrepancy budget, exact normalized lower form.**  The lower companion to
`normalized_variance_le_one_add_pairResidual`: pair-equidistribution pins the normalized variance
from below by `1 - δ(2m-1)`.

Together with the upper bound this says the entire two-sided normalized error is controlled by the
same door-(iv) residual.  This is only a reduction statement; it proves no pair-equidistribution or
CORE cancellation. -/
theorem one_sub_pairResidual_le_normalized_variance {m : ℕ} (hm : 0 < m)
    (φ : Fin m → B → ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (hpair : PairEquidistributed φ δ) :
    1 - δ * (2 * (m : ℝ) - 1)
      ≤ avg (fun b => (∑ k : Fin m, 2 * Real.cos (φ k b)) ^ 2) / prizeVarianceProxy m := by
  have hbase := variance_ge_of_pairEquidist (B := B) φ δ hδ hpair
  have hproxy_pos : 0 < prizeVarianceProxy m := by
    unfold prizeVarianceProxy
    positivity
  calc
    1 - δ * (2 * (m : ℝ) - 1)
        = (2 * (m : ℝ) - 2 * δ * ((m : ℝ) * (2 * (m : ℝ) - 1))) /
            prizeVarianceProxy m := by
          have hm2 : (2 * (m : ℝ)) ≠ 0 := by positivity
          unfold prizeVarianceProxy
          field_simp [hm2]
    _ ≤ avg (fun b => (∑ k : Fin m, 2 * Real.cos (φ k b)) ^ 2) / prizeVarianceProxy m :=
      div_le_div_of_nonneg_right hbase (le_of_lt hproxy_pos)

/-- **Pair-discrepancy budget, exact normalized two-sided form.**  After dividing by the prize
variance proxy `2m`, the averaged second moment lies in the symmetric interval

`1 ± δ(2m-1)`.

Equivalently, the normalized Shaw/prize variance error is bounded by the dimensionless pair residual
`δ(2m-1)`.  This is the citable two-sided Lane-2 capstone for the pair-discrepancy reduction, not a
proof that the residual has the required `O(1/m)` size in the prize regime. -/
theorem abs_normalized_variance_sub_one_le_pairResidual {m : ℕ} (hm : 0 < m)
    (φ : Fin m → B → ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (hpair : PairEquidistributed φ δ) :
    |avg (fun b => (∑ k : Fin m, 2 * Real.cos (φ k b)) ^ 2) / prizeVarianceProxy m - 1|
      ≤ δ * (2 * (m : ℝ) - 1) := by
  rw [abs_le]
  constructor
  · have hlower := one_sub_pairResidual_le_normalized_variance (hm := hm) (φ := φ) (hδ := hδ)
      (hpair := hpair)
    linarith
  · have hupper := normalized_variance_le_one_add_pairResidual (hm := hm) (φ := φ) (hδ := hδ)
      (hpair := hpair)
    linarith

/-- **Pair-discrepancy budget, exact normalized `ε/(2m-1)` upper form.**  If the residual satisfies
`δ ≤ ε/(2m-1)`, then the normalized variance is at most `1+ε`.  This is the exact-scale companion
to the coarser `C/m` interface. -/
theorem normalized_variance_le_one_add_of_delta_le_div {m : ℕ} (hm : 0 < m)
    (φ : Fin m → B → ℝ) {δ ε : ℝ} (hδ : 0 ≤ δ)
    (hδle : δ ≤ ε / (2 * (m : ℝ) - 1)) (hpair : PairEquidistributed φ δ) :
    avg (fun b => (∑ k : Fin m, 2 * Real.cos (φ k b)) ^ 2) / prizeVarianceProxy m
      ≤ 1 + ε := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hden_pos : 0 < 2 * (m : ℝ) - 1 := by nlinarith [hmR]
  have hres : δ * (2 * (m : ℝ) - 1) ≤ ε := by
    calc
      δ * (2 * (m : ℝ) - 1) ≤ (ε / (2 * (m : ℝ) - 1)) * (2 * (m : ℝ) - 1) :=
        mul_le_mul_of_nonneg_right hδle (le_of_lt hden_pos)
      _ = ε := by field_simp [ne_of_gt hden_pos]
  have hbase := normalized_variance_le_one_add_pairResidual (hm := hm) (φ := φ)
    (hδ := hδ) (hpair := hpair)
  linarith

/-- **Pair-discrepancy budget, exact normalized `ε/(2m-1)` lower form.**  The same exact residual
scale gives the lower corridor endpoint `1-ε`. -/
theorem one_sub_le_normalized_variance_of_delta_le_div {m : ℕ} (hm : 0 < m)
    (φ : Fin m → B → ℝ) {δ ε : ℝ} (hδ : 0 ≤ δ)
    (hδle : δ ≤ ε / (2 * (m : ℝ) - 1)) (hpair : PairEquidistributed φ δ) :
    1 - ε ≤ avg (fun b => (∑ k : Fin m, 2 * Real.cos (φ k b)) ^ 2) / prizeVarianceProxy m := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hden_pos : 0 < 2 * (m : ℝ) - 1 := by nlinarith [hmR]
  have hres : δ * (2 * (m : ℝ) - 1) ≤ ε := by
    calc
      δ * (2 * (m : ℝ) - 1) ≤ (ε / (2 * (m : ℝ) - 1)) * (2 * (m : ℝ) - 1) :=
        mul_le_mul_of_nonneg_right hδle (le_of_lt hden_pos)
      _ = ε := by field_simp [ne_of_gt hden_pos]
  have hbase := one_sub_pairResidual_le_normalized_variance (hm := hm) (φ := φ)
    (hδ := hδ) (hpair := hpair)
  linarith

/-- **Pair-discrepancy budget, exact normalized `ε/(2m-1)` two-sided form.**  The normalized
variance error is at most `ε` exactly when the named residual is driven to the explicit scale
`δ ≤ ε/(2m-1)`.  This proves only the reduction/corridor, not the arithmetic residual estimate. -/
theorem abs_normalized_variance_sub_one_le_of_delta_le_div {m : ℕ} (hm : 0 < m)
    (φ : Fin m → B → ℝ) {δ ε : ℝ} (hδ : 0 ≤ δ)
    (hδle : δ ≤ ε / (2 * (m : ℝ) - 1)) (hpair : PairEquidistributed φ δ) :
    |avg (fun b => (∑ k : Fin m, 2 * Real.cos (φ k b)) ^ 2) / prizeVarianceProxy m - 1|
      ≤ ε := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hden_pos : 0 < 2 * (m : ℝ) - 1 := by nlinarith [hmR]
  have hres : δ * (2 * (m : ℝ) - 1) ≤ ε := by
    calc
      δ * (2 * (m : ℝ) - 1) ≤ (ε / (2 * (m : ℝ) - 1)) * (2 * (m : ℝ) - 1) :=
        mul_le_mul_of_nonneg_right hδle (le_of_lt hden_pos)
      _ = ε := by field_simp [ne_of_gt hden_pos]
  exact le_trans (abs_normalized_variance_sub_one_le_pairResidual (hm := hm) (φ := φ)
    (hδ := hδ) (hpair := hpair)) hres

/-- **Ideal normalized endpoint.**  Exact pair-equidistribution (`δ = 0`) pins the normalized
variance to the Shaw/prize floor exactly:

`avg_B η² / (2m) = 1`.

This is the equality form of the two-sided normalized budget at zero residual.  It proves no
prize-regime anti-concentration; it only records the endpoint of the named reduction. -/
theorem normalized_variance_eq_one_of_ideal_pairEquidist {m : ℕ} (hm : 0 < m)
    (φ : Fin m → B → ℝ) (hpair : PairEquidistributed φ 0) :
    avg (fun b => (∑ k : Fin m, 2 * Real.cos (φ k b)) ^ 2) / prizeVarianceProxy m = 1 := by
  have h := abs_normalized_variance_sub_one_le_pairResidual (hm := hm) (φ := φ) (hδ := by norm_num)
    (hpair := hpair)
  have hnonneg : 0 ≤
      |avg (fun b => (∑ k : Fin m, 2 * Real.cos (φ k b)) ^ 2) / prizeVarianceProxy m - 1| :=
    abs_nonneg _
  have habs :
      |avg (fun b => (∑ k : Fin m, 2 * Real.cos (φ k b)) ^ 2) / prizeVarianceProxy m - 1| = 0 := by
    apply le_antisymm
    · simpa using h
    · exact hnonneg
  exact sub_eq_zero.mp (abs_eq_zero.mp habs)

/-- **Pair-discrepancy budget, standard `C/m` form.**  If the residual is bounded by
`C/m`, then the normalized variance is bounded by `1+2C`.

This is the coarse asymptotic interface used by the door-(iv) target: a genuine `O(1/m)`
pair-discrepancy estimate is exactly enough to keep the normalized variance `O(1)`. -/
theorem normalized_variance_le_one_add_two_mul_of_delta_le_const_div {m : ℕ} (hm : 0 < m)
    (φ : Fin m → B → ℝ) {δ C : ℝ} (hδ : 0 ≤ δ) (hC : 0 ≤ C)
    (hδle : δ ≤ C / (m : ℝ)) (hpair : PairEquidistributed φ δ) :
    avg (fun b => (∑ k : Fin m, 2 * Real.cos (φ k b)) ^ 2) / prizeVarianceProxy m
      ≤ 1 + 2 * C := by
  have hnorm := normalized_variance_le_one_add_pairResidual (hm := hm) (φ := φ) (hδ := hδ)
    (hpair := hpair)
  have hmR_pos : 0 < (m : ℝ) := by exact_mod_cast hm
  have hmR_one : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hfactor_nonneg : 0 ≤ 2 * (m : ℝ) - 1 := by nlinarith
  have hres : δ * (2 * (m : ℝ) - 1) ≤ 2 * C := by
    calc
      δ * (2 * (m : ℝ) - 1) ≤ (C / (m : ℝ)) * (2 * (m : ℝ) - 1) :=
        mul_le_mul_of_nonneg_right hδle hfactor_nonneg
      _ = C * (2 - 1 / (m : ℝ)) := by
        field_simp [ne_of_gt hmR_pos]
      _ ≤ 2 * C := by
        have hinv_nonneg : 0 ≤ (1 : ℝ) / (m : ℝ) := div_nonneg zero_le_one (le_of_lt hmR_pos)
        have hcoef : 2 - 1 / (m : ℝ) ≤ 2 := by linarith
        nlinarith [mul_le_mul_of_nonneg_left hcoef hC]
  nlinarith

/-- **Pair-discrepancy budget, two-sided standard `C/m` form.**  If the residual is bounded
by `C/m`, then the normalized variance stays within `2C` of the prize floor `1`.

This is the symmetric companion to `normalized_variance_le_one_add_two_mul_of_delta_le_const_div`:
the same `O(1/m)` residual scale controls the full normalized error, not only the upper tail. -/
theorem abs_normalized_variance_sub_one_le_two_mul_of_delta_le_const_div {m : ℕ} (hm : 0 < m)
    (φ : Fin m → B → ℝ) {δ C : ℝ} (hδ : 0 ≤ δ) (hC : 0 ≤ C)
    (hδle : δ ≤ C / (m : ℝ)) (hpair : PairEquidistributed φ δ) :
    |avg (fun b => (∑ k : Fin m, 2 * Real.cos (φ k b)) ^ 2) / prizeVarianceProxy m - 1|
      ≤ 2 * C := by
  have habs := abs_normalized_variance_sub_one_le_pairResidual (hm := hm) (φ := φ) (hδ := hδ)
    (hpair := hpair)
  have hmR_pos : 0 < (m : ℝ) := by exact_mod_cast hm
  have hmR_one : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hfactor_nonneg : 0 ≤ 2 * (m : ℝ) - 1 := by nlinarith
  have hres : δ * (2 * (m : ℝ) - 1) ≤ 2 * C := by
    calc
      δ * (2 * (m : ℝ) - 1) ≤ (C / (m : ℝ)) * (2 * (m : ℝ) - 1) :=
        mul_le_mul_of_nonneg_right hδle hfactor_nonneg
      _ = C * (2 - 1 / (m : ℝ)) := by
        field_simp [ne_of_gt hmR_pos]
      _ ≤ 2 * C := by
        have hinv_nonneg : 0 ≤ (1 : ℝ) / (m : ℝ) := div_nonneg zero_le_one (le_of_lt hmR_pos)
        have hcoef : 2 - 1 / (m : ℝ) ≤ 2 := by linarith
        nlinarith [mul_le_mul_of_nonneg_left hcoef hC]
  exact le_trans habs hres

/-- **Pair-discrepancy budget, multiplicative form.**  If the dimensionless residual obeys
`δ(2m-1) ≤ ε`, then the variance is bounded by the prize proxy times `1+ε`.

This is the clean normalized statement of the open door-(iv) target: the named pair-equidistribution
residual must be `O(1/m)` to make the variance proxy stay at the prize scale. -/
theorem variance_le_prizeProxy_mul_one_add_of_pairResidual {m : ℕ} (hm : 0 < m)
    (φ : Fin m → B → ℝ) {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : δ * (2 * (m : ℝ) - 1) ≤ ε)
    (hpair : PairEquidistributed φ δ) :
    avg (fun b => (∑ k : Fin m, 2 * Real.cos (φ k b)) ^ 2)
      ≤ prizeVarianceProxy m * (1 + ε) := by
  have hbase := variance_le_of_pairEquidist (B := B) φ δ hδ hpair
  have hmnonneg : (0 : ℝ) ≤ 2 * (m : ℝ) := by positivity
  have hcorr : 2 * δ * ((m : ℝ) * (2 * (m : ℝ) - 1)) ≤ 2 * (m : ℝ) * ε := by
    calc
      2 * δ * ((m : ℝ) * (2 * (m : ℝ) - 1))
          = 2 * (m : ℝ) * (δ * (2 * (m : ℝ) - 1)) := by ring
      _ ≤ 2 * (m : ℝ) * ε := mul_le_mul_of_nonneg_left hε hmnonneg
  calc
    avg (fun b => (∑ k : Fin m, 2 * Real.cos (φ k b)) ^ 2)
        ≤ 2 * (m : ℝ) + 2 * δ * ((m : ℝ) * (2 * (m : ℝ) - 1)) := hbase
    _ ≤ 2 * (m : ℝ) + 2 * (m : ℝ) * ε := by
      simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hcorr (2 * (m : ℝ))
    _ = prizeVarianceProxy m * (1 + ε) := by unfold prizeVarianceProxy; ring


/-- **Pair-discrepancy budget, lower multiplicative form.**  If the dimensionless residual obeys
`δ(2m-1) ≤ ε`, then the variance is bounded below by the prize proxy times `1-ε`.
Together with `variance_le_prizeProxy_mul_one_add_of_pairResidual`, this gives the raw two-sided
Lane-2 corridor around the Plancherel/prize variance scale. -/
theorem prizeProxy_mul_one_sub_le_variance_of_pairResidual {m : ℕ} (hm : 0 < m)
    (φ : Fin m → B → ℝ) {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : δ * (2 * (m : ℝ) - 1) ≤ ε)
    (hpair : PairEquidistributed φ δ) :
    prizeVarianceProxy m * (1 - ε)
      ≤ avg (fun b => (∑ k : Fin m, 2 * Real.cos (φ k b)) ^ 2) := by
  have hbase := variance_ge_of_pairEquidist (B := B) φ δ hδ hpair
  have hmnonneg : (0 : ℝ) ≤ 2 * (m : ℝ) := by positivity
  have hcorr : 2 * (m : ℝ) * ε ≥ 2 * δ * ((m : ℝ) * (2 * (m : ℝ) - 1)) := by
    calc
      2 * δ * ((m : ℝ) * (2 * (m : ℝ) - 1))
          = 2 * (m : ℝ) * (δ * (2 * (m : ℝ) - 1)) := by ring
      _ ≤ 2 * (m : ℝ) * ε := mul_le_mul_of_nonneg_left hε hmnonneg
  calc
    prizeVarianceProxy m * (1 - ε) = 2 * (m : ℝ) - 2 * (m : ℝ) * ε := by
      unfold prizeVarianceProxy
      ring
    _ ≤ 2 * (m : ℝ) - 2 * δ * ((m : ℝ) * (2 * (m : ℝ) - 1)) := by linarith
    _ ≤ avg (fun b => (∑ k : Fin m, 2 * Real.cos (φ k b)) ^ 2) := hbase

/-- **Pair-discrepancy budget, raw two-sided multiplicative form.**  If the dimensionless residual is
at most `ε`, then the raw variance proxy differs from `2m` by at most `(2m)ε`.
This is the exact unnormalized companion to the normalized absolute-error capstone. -/
theorem abs_variance_sub_prizeProxy_le_prizeProxy_mul_of_pairResidual {m : ℕ} (hm : 0 < m)
    (φ : Fin m → B → ℝ) {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : δ * (2 * (m : ℝ) - 1) ≤ ε)
    (hpair : PairEquidistributed φ δ) :
    |avg (fun b => (∑ k : Fin m, 2 * Real.cos (φ k b)) ^ 2) - prizeVarianceProxy m|
      ≤ prizeVarianceProxy m * ε := by
  rw [abs_le]
  constructor
  · have hlower := prizeProxy_mul_one_sub_le_variance_of_pairResidual (hm := hm) (φ := φ)
      (hδ := hδ) (hε := hε) (hpair := hpair)
    linarith
  · have hupper := variance_le_prizeProxy_mul_one_add_of_pairResidual (hm := hm) (φ := φ)
      (hδ := hδ) (hε := hε) (hpair := hpair)
    linarith

/-- **Pair-discrepancy budget, explicit `O(1/m)` form.**  If
`δ ≤ ε/(2m-1)`, then the variance is bounded by the prize proxy times `1+ε`.
The denominator is positive for every nonempty antipodal-pair list `m>0`. -/
theorem variance_le_prizeProxy_mul_one_add_of_delta_le_div {m : ℕ} (hm : 0 < m)
    (φ : Fin m → B → ℝ) {δ ε : ℝ} (hδ : 0 ≤ δ) (hδle : δ ≤ ε / (2 * (m : ℝ) - 1))
    (hpair : PairEquidistributed φ δ) :
    avg (fun b => (∑ k : Fin m, 2 * Real.cos (φ k b)) ^ 2)
      ≤ prizeVarianceProxy m * (1 + ε) := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hden_pos : 0 < 2 * (m : ℝ) - 1 := by
    nlinarith [hmR]
  apply variance_le_prizeProxy_mul_one_add_of_pairResidual (hm := hm) (φ := φ) (hδ := hδ) (hpair := hpair)
  calc
    δ * (2 * (m : ℝ) - 1) ≤ (ε / (2 * (m : ℝ) - 1)) * (2 * (m : ℝ) - 1) :=
      mul_le_mul_of_nonneg_right hδle (le_of_lt hden_pos)
    _ = ε := by
      exact div_mul_cancel₀ ε (ne_of_gt hden_pos)

/-- **Pair-discrepancy budget, lower explicit `O(1/m)` form.**  If
`δ ≤ ε/(2m-1)`, then the variance is bounded below by the prize proxy times `1-ε`. -/
theorem prizeProxy_mul_one_sub_le_variance_of_delta_le_div {m : ℕ} (hm : 0 < m)
    (φ : Fin m → B → ℝ) {δ ε : ℝ} (hδ : 0 ≤ δ) (hδle : δ ≤ ε / (2 * (m : ℝ) - 1))
    (hpair : PairEquidistributed φ δ) :
    prizeVarianceProxy m * (1 - ε)
      ≤ avg (fun b => (∑ k : Fin m, 2 * Real.cos (φ k b)) ^ 2) := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hden_pos : 0 < 2 * (m : ℝ) - 1 := by
    nlinarith [hmR]
  apply prizeProxy_mul_one_sub_le_variance_of_pairResidual (hm := hm) (φ := φ) (hδ := hδ)
    (hpair := hpair)
  calc
    δ * (2 * (m : ℝ) - 1) ≤ (ε / (2 * (m : ℝ) - 1)) * (2 * (m : ℝ) - 1) :=
      mul_le_mul_of_nonneg_right hδle (le_of_lt hden_pos)
    _ = ε := by
      exact div_mul_cancel₀ ε (ne_of_gt hden_pos)

/-- **Pair-discrepancy budget, raw two-sided explicit `O(1/m)` form.**  If
`δ ≤ ε/(2m-1)`, then the raw variance proxy differs from `2m` by at most `(2m)ε`. -/
theorem abs_variance_sub_prizeProxy_le_prizeProxy_mul_of_delta_le_div {m : ℕ} (hm : 0 < m)
    (φ : Fin m → B → ℝ) {δ ε : ℝ} (hδ : 0 ≤ δ) (hδle : δ ≤ ε / (2 * (m : ℝ) - 1))
    (hpair : PairEquidistributed φ δ) :
    |avg (fun b => (∑ k : Fin m, 2 * Real.cos (φ k b)) ^ 2) - prizeVarianceProxy m|
      ≤ prizeVarianceProxy m * ε := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hden_pos : 0 < 2 * (m : ℝ) - 1 := by
    nlinarith [hmR]
  apply abs_variance_sub_prizeProxy_le_prizeProxy_mul_of_pairResidual (hm := hm) (φ := φ)
    (hδ := hδ) (hpair := hpair)
  calc
    δ * (2 * (m : ℝ) - 1) ≤ (ε / (2 * (m : ℝ) - 1)) * (2 * (m : ℝ) - 1) :=
      mul_le_mul_of_nonneg_right hδle (le_of_lt hden_pos)
    _ = ε := by
      exact div_mul_cancel₀ ε (ne_of_gt hden_pos)

/-- **The ideal pair-equidistribution endpoint.**  At exact residual `δ = 0`, the variance proxy is
bounded directly by the prize variance proxy `2m`.  This is only the endpoint specialization of the
already-proven decoupling theorem; the hard analytic content is proving that a prize-regime phase set
actually reaches this endpoint or an `O(1/m)` neighborhood of it. -/
theorem variance_le_prizeProxy_of_ideal_pairEquidist {m : ℕ} (φ : Fin m → B → ℝ)
    (hpair : PairEquidistributed φ 0) :
    avg (fun b => (∑ k : Fin m, 2 * Real.cos (φ k b)) ^ 2) ≤ prizeVarianceProxy m := by
  have hbase := variance_le_of_pairEquidist (B := B) φ 0 (by norm_num) hpair
  simpa [prizeVarianceProxy] using hbase

/-- **The raw ideal pair-equidistribution endpoint.**  At exact residual `δ = 0`, the raw
variance proxy is exactly the prize variance proxy `2m`. -/
theorem variance_eq_prizeProxy_of_ideal_pairEquidist {m : ℕ} (hm : 0 < m)
    (φ : Fin m → B → ℝ) (hpair : PairEquidistributed φ 0) :
    avg (fun b => (∑ k : Fin m, 2 * Real.cos (φ k b)) ^ 2) = prizeVarianceProxy m := by
  apply le_antisymm
  · exact variance_le_prizeProxy_of_ideal_pairEquidist (m := m) φ hpair
  · have hlower := prizeProxy_mul_one_sub_le_variance_of_pairResidual (hm := hm) (φ := φ)
      (δ := 0) (ε := 0) (hδ := by norm_num) (hε := by norm_num) (hpair := hpair)
    simpa using hlower

/-- The raw absolute-error form also vanishes at the ideal endpoint. -/
theorem abs_variance_sub_prizeProxy_eq_zero_of_ideal_pairEquidist {m : ℕ} (hm : 0 < m)
    (φ : Fin m → B → ℝ) (hpair : PairEquidistributed φ 0) :
    |avg (fun b => (∑ k : Fin m, 2 * Real.cos (φ k b)) ^ 2) - prizeVarianceProxy m| = 0 := by
  have h := variance_eq_prizeProxy_of_ideal_pairEquidist (hm := hm) (φ := φ) hpair
  simp [h]

/-- **The normalized correction is exactly `δ(2m-1)`.**  This pins the anti-concentration target with
no asymptotic handwaving: after division by the prize variance proxy `2m`, the pair-discrepancy
correction from `_PhaseLinearFormDecoupling` is precisely `δ(2m-1)`. -/
theorem correction_div_prizeProxy_eq_pairResidual {m : ℕ} (hm : 0 < m) (δ : ℝ) :
    pairResidualCorrection m δ / prizeVarianceProxy m = δ * (2 * (m : ℝ) - 1) := by
  have hm2 : (2 * (m : ℝ)) ≠ 0 := by positivity
  unfold pairResidualCorrection prizeVarianceProxy
  field_simp [hm2]

/-- **Raw correction budget iff dimensionless residual budget.**  Since the correction divided by
the prize proxy is exactly `δ(2m-1)`, a raw correction spend `≤ (2m)ε` is equivalent to the
normalized residual spend `≤ ε`.  This is a reduction identity only; it proves no residual estimate. -/
theorem correction_le_prizeProxy_mul_iff_pairResidual_le {m : ℕ} (hm : 0 < m) {δ ε : ℝ} :
    pairResidualCorrection m δ ≤ prizeVarianceProxy m * ε ↔
      δ * (2 * (m : ℝ) - 1) ≤ ε := by
  have hp : 0 < prizeVarianceProxy m := by
    unfold prizeVarianceProxy
    positivity
  constructor
  · intro h
    have hdiv : pairResidualCorrection m δ / prizeVarianceProxy m ≤
        (prizeVarianceProxy m * ε) / prizeVarianceProxy m :=
      div_le_div_of_nonneg_right h (le_of_lt hp)
    simpa [correction_div_prizeProxy_eq_pairResidual (hm := hm) δ, ne_of_gt hp, mul_comm,
      mul_left_comm, mul_assoc] using hdiv
  · intro h
    have hmul : (pairResidualCorrection m δ / prizeVarianceProxy m) * prizeVarianceProxy m ≤
        ε * prizeVarianceProxy m := by
      have h' := h
      rw [← correction_div_prizeProxy_eq_pairResidual (hm := hm) δ] at h'
      exact mul_le_mul_of_nonneg_right h' (le_of_lt hp)
    calc
      pairResidualCorrection m δ =
          (pairResidualCorrection m δ / prizeVarianceProxy m) * prizeVarianceProxy m := by
        field_simp [ne_of_gt hp]
      _ ≤ ε * prizeVarianceProxy m := hmul
      _ = prizeVarianceProxy m * ε := by ring

/-- Equality form of the raw-correction/normalized-residual bridge.  Spending exactly `(2m)ε` of
raw correction is the same as having exact dimensionless residual `ε`. -/
theorem correction_eq_prizeProxy_mul_iff_pairResidual_eq {m : ℕ} (hm : 0 < m) {δ ε : ℝ} :
    pairResidualCorrection m δ = prizeVarianceProxy m * ε ↔
      δ * (2 * (m : ℝ) - 1) = ε := by
  have hp : prizeVarianceProxy m ≠ 0 := ne_of_gt (by
    unfold prizeVarianceProxy
    positivity)
  constructor
  · intro h
    have hdiv : pairResidualCorrection m δ / prizeVarianceProxy m =
        (prizeVarianceProxy m * ε) / prizeVarianceProxy m := by rw [h]
    simpa [correction_div_prizeProxy_eq_pairResidual (hm := hm) δ, hp, mul_comm, mul_left_comm,
      mul_assoc] using hdiv
  · intro h
    calc
      pairResidualCorrection m δ =
          (pairResidualCorrection m δ / prizeVarianceProxy m) * prizeVarianceProxy m := by
        field_simp [hp]
      _ = ε * prizeVarianceProxy m := by
        rw [correction_div_prizeProxy_eq_pairResidual (hm := hm) δ, h]
      _ = prizeVarianceProxy m * ε := by ring

/-- The pair-discrepancy correction itself vanishes at the ideal residual `δ = 0`. -/
theorem pairResidualCorrection_zero (m : ℕ) : pairResidualCorrection m 0 = 0 := by
  unfold pairResidualCorrection
  ring

end ArkLib.ProximityGap.Frontier.PhasePairEquidistBudget

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound; no `sorryAx`). -/
#print axioms ArkLib.ProximityGap.Frontier.PhasePairEquidistBudget.normalized_variance_le_one_add_pairResidual
#print axioms ArkLib.ProximityGap.Frontier.PhasePairEquidistBudget.one_sub_pairResidual_le_normalized_variance
#print axioms ArkLib.ProximityGap.Frontier.PhasePairEquidistBudget.abs_normalized_variance_sub_one_le_pairResidual
#print axioms ArkLib.ProximityGap.Frontier.PhasePairEquidistBudget.normalized_variance_eq_one_of_ideal_pairEquidist
#print axioms ArkLib.ProximityGap.Frontier.PhasePairEquidistBudget.normalized_variance_le_one_add_of_delta_le_div
#print axioms ArkLib.ProximityGap.Frontier.PhasePairEquidistBudget.one_sub_le_normalized_variance_of_delta_le_div
#print axioms ArkLib.ProximityGap.Frontier.PhasePairEquidistBudget.abs_normalized_variance_sub_one_le_of_delta_le_div
#print axioms ArkLib.ProximityGap.Frontier.PhasePairEquidistBudget.abs_normalized_variance_sub_one_le_two_mul_of_delta_le_const_div
#print axioms ArkLib.ProximityGap.Frontier.PhasePairEquidistBudget.normalized_variance_le_one_add_two_mul_of_delta_le_const_div
#print axioms ArkLib.ProximityGap.Frontier.PhasePairEquidistBudget.variance_le_prizeProxy_mul_one_add_of_pairResidual
#print axioms ArkLib.ProximityGap.Frontier.PhasePairEquidistBudget.prizeProxy_mul_one_sub_le_variance_of_pairResidual
#print axioms ArkLib.ProximityGap.Frontier.PhasePairEquidistBudget.abs_variance_sub_prizeProxy_le_prizeProxy_mul_of_pairResidual
#print axioms ArkLib.ProximityGap.Frontier.PhasePairEquidistBudget.variance_le_prizeProxy_mul_one_add_of_delta_le_div
#print axioms ArkLib.ProximityGap.Frontier.PhasePairEquidistBudget.prizeProxy_mul_one_sub_le_variance_of_delta_le_div
#print axioms ArkLib.ProximityGap.Frontier.PhasePairEquidistBudget.abs_variance_sub_prizeProxy_le_prizeProxy_mul_of_delta_le_div
#print axioms ArkLib.ProximityGap.Frontier.PhasePairEquidistBudget.variance_le_prizeProxy_of_ideal_pairEquidist
#print axioms ArkLib.ProximityGap.Frontier.PhasePairEquidistBudget.variance_eq_prizeProxy_of_ideal_pairEquidist
#print axioms ArkLib.ProximityGap.Frontier.PhasePairEquidistBudget.abs_variance_sub_prizeProxy_eq_zero_of_ideal_pairEquidist
#print axioms ArkLib.ProximityGap.Frontier.PhasePairEquidistBudget.correction_div_prizeProxy_eq_pairResidual
#print axioms ArkLib.ProximityGap.Frontier.PhasePairEquidistBudget.correction_le_prizeProxy_mul_iff_pairResidual_le
#print axioms ArkLib.ProximityGap.Frontier.PhasePairEquidistBudget.correction_eq_prizeProxy_mul_iff_pairResidual_eq
#print axioms ArkLib.ProximityGap.Frontier.PhasePairEquidistBudget.pairResidualCorrection_zero
