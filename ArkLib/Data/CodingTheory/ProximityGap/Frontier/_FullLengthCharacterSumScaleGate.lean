/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Full-length character-sum scale gate

Large-value results for Fekete polynomials, interval character sums, and high moments of Dirichlet
character sums naturally live at the full field square-root scale `p^(1/2)` (up to logarithms).
The #464 subgroup-period target at `n = p^gamma` is `sqrt(n) = p^(gamma/2)`.

This file records the exponent bookkeeping that any transfer from those full-length objects to the
dyadic subgroup period must pay:

* a full-length `p^(1/2)` bound reaches the subgroup prize scale only after a power saving
  `nu >= (1 - gamma) / 2`;
* at the binding beta-four diagonal, `gamma = 1/4`, so the required saving is `3/8`;
* without that `p^{-3/8}` transfer saving, full-length large-value or moment results remain
  off-object for the subgroup period.

No analytic theorem is asserted here.  This is a routing guardrail for local PDFs such as
large-values of mixed/Fekete character sums, maximum short character sums, and high moments of
Dirichlet character sums: they can inform heuristics, but they do not by themselves produce the
subgroup-scale worst-period bound.
-/

namespace ArkLib.ProximityGap.Frontier.FullLengthCharacterSumScaleGate

/-- The subgroup prize exponent in `p`-scale when `n = p^gamma`: `sqrt(n) = p^(gamma/2)`. -/
noncomputable def subgroupPrizeExponent (gamma : ℝ) : ℝ :=
  gamma / 2

/-- The natural full-length character-sum square-root exponent. -/
noncomputable def fullLengthExponent : ℝ :=
  1 / 2

/-- A transfer with power saving `p^{-nu}` from the full-length scale has exponent `1/2 - nu`. -/
noncomputable def transferredFullLengthExponent (nu : ℝ) : ℝ :=
  fullLengthExponent - nu

/-- Required power saving for a full-length character-sum input to reach the subgroup prize scale. -/
noncomputable def requiredFullLengthSaving (gamma : ℝ) : ℝ :=
  fullLengthExponent - subgroupPrizeExponent gamma

/-- Exact threshold: a transferred full-length character-sum bound reaches the subgroup prize scale
iff the transfer saving pays the full exponent gap. -/
theorem transferredFullLength_reaches_prize_iff {gamma nu : ℝ} :
    transferredFullLengthExponent nu ≤ subgroupPrizeExponent gamma ↔
      requiredFullLengthSaving gamma ≤ nu := by
  unfold transferredFullLengthExponent requiredFullLengthSaving
  constructor <;> intro h <;> linarith

/-- Strict complement: if the transfer saving is below the exponent gap, the full-length input
stays above the subgroup prize exponent. -/
theorem transferredFullLength_misses_prize_iff {gamma nu : ℝ} :
    subgroupPrizeExponent gamma < transferredFullLengthExponent nu ↔
      nu < requiredFullLengthSaving gamma := by
  unfold transferredFullLengthExponent requiredFullLengthSaving
  constructor <;> intro h <;> linarith

/-- At the beta-four subgroup exponent `gamma = 1/4`, the subgroup prize exponent is `1/8`. -/
theorem subgroupPrizeExponent_beta_four :
    subgroupPrizeExponent (1 / 4 : ℝ) = 1 / 8 := by
  norm_num [subgroupPrizeExponent]

/-- At beta four, the full-length `sqrt(p)` scale sits `3/8` powers of `p` above the subgroup
prize scale. -/
theorem requiredFullLengthSaving_beta_four :
    requiredFullLengthSaving (1 / 4 : ℝ) = 3 / 8 := by
  norm_num [requiredFullLengthSaving, fullLengthExponent, subgroupPrizeExponent]

/-- With no power saving, the full-length scale misses the beta-four subgroup target. -/
theorem fullLength_misses_beta_four_without_saving :
    subgroupPrizeExponent (1 / 4 : ℝ) < transferredFullLengthExponent 0 := by
  norm_num [subgroupPrizeExponent, transferredFullLengthExponent, fullLengthExponent]

/-- At beta four, any transfer saving below `3/8` still misses the subgroup prize exponent. -/
theorem beta_four_misses_of_saving_lt_three_eighths {nu : ℝ} (hnu : nu < 3 / 8) :
    subgroupPrizeExponent (1 / 4 : ℝ) < transferredFullLengthExponent nu := by
  have hgap : nu < requiredFullLengthSaving (1 / 4 : ℝ) := by
    rwa [requiredFullLengthSaving_beta_four]
  exact (transferredFullLength_misses_prize_iff
    (gamma := (1 / 4 : ℝ)) (nu := nu)).2 hgap

/-- At beta four, a `p^{-3/8}` transfer saving is exactly sufficient at exponent level. -/
theorem beta_four_reaches_of_three_eighths_le_saving {nu : ℝ} (hnu : 3 / 8 ≤ nu) :
    transferredFullLengthExponent nu ≤ subgroupPrizeExponent (1 / 4 : ℝ) := by
  have hgap : requiredFullLengthSaving (1 / 4 : ℝ) ≤ nu := by
    rwa [requiredFullLengthSaving_beta_four]
  exact (transferredFullLength_reaches_prize_iff
    (gamma := (1 / 4 : ℝ)) (nu := nu)).2 hgap

/-- For every genuinely thin subgroup exponent `gamma < 1`, the full-length square-root scale is
strictly above the subgroup square-root scale. -/
theorem fullLength_gap_positive_of_gamma_lt_one {gamma : ℝ} (hgamma : gamma < 1) :
    0 < requiredFullLengthSaving gamma := by
  unfold requiredFullLengthSaving fullLengthExponent subgroupPrizeExponent
  linarith

/-- Packaged verdict for the local large-values character-sum literature at beta four. -/
theorem fullLengthCharacterSumScaleGate :
    subgroupPrizeExponent (1 / 4 : ℝ) = 1 / 8 ∧
    requiredFullLengthSaving (1 / 4 : ℝ) = 3 / 8 ∧
    subgroupPrizeExponent (1 / 4 : ℝ) < transferredFullLengthExponent 0 ∧
    (∀ nu : ℝ, nu < 3 / 8 ->
      subgroupPrizeExponent (1 / 4 : ℝ) < transferredFullLengthExponent nu) ∧
    (∀ nu : ℝ, 3 / 8 ≤ nu ->
      transferredFullLengthExponent nu ≤ subgroupPrizeExponent (1 / 4 : ℝ)) := by
  exact ⟨subgroupPrizeExponent_beta_four,
    requiredFullLengthSaving_beta_four,
    fullLength_misses_beta_four_without_saving,
    fun nu hnu => beta_four_misses_of_saving_lt_three_eighths hnu,
    fun nu hnu => beta_four_reaches_of_three_eighths_le_saving hnu⟩

end ArkLib.ProximityGap.Frontier.FullLengthCharacterSumScaleGate

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.FullLengthCharacterSumScaleGate.transferredFullLength_reaches_prize_iff
#print axioms ArkLib.ProximityGap.Frontier.FullLengthCharacterSumScaleGate.transferredFullLength_misses_prize_iff
#print axioms ArkLib.ProximityGap.Frontier.FullLengthCharacterSumScaleGate.subgroupPrizeExponent_beta_four
#print axioms ArkLib.ProximityGap.Frontier.FullLengthCharacterSumScaleGate.requiredFullLengthSaving_beta_four
#print axioms ArkLib.ProximityGap.Frontier.FullLengthCharacterSumScaleGate.fullLength_misses_beta_four_without_saving
#print axioms ArkLib.ProximityGap.Frontier.FullLengthCharacterSumScaleGate.beta_four_misses_of_saving_lt_three_eighths
#print axioms ArkLib.ProximityGap.Frontier.FullLengthCharacterSumScaleGate.beta_four_reaches_of_three_eighths_le_saving
#print axioms ArkLib.ProximityGap.Frontier.FullLengthCharacterSumScaleGate.fullLength_gap_positive_of_gamma_lt_one
#print axioms ArkLib.ProximityGap.Frontier.FullLengthCharacterSumScaleGate.fullLengthCharacterSumScaleGate
