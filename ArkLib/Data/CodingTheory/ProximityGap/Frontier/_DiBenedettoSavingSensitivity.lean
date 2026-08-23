/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DiBenedettoNearSidonImprovement

/-!
# di Benedetto edge-saving SENSITIVITY: the t3-dominance lever-selection theorem (#444)

`_DiBenedettoNearSidonImprovement.lean` pins the saving formula
`diBenedettoSaving t₂ t₃ = (10 − 2·t₃ − t₂/2)/72`, its baseline (`31/2880`), the near-Sidon value
(`1/24`), the antitone monotonicity, the `1/24` ceiling, and the conditional character-sum bound.
That file's docstring asserts the **lever-selection rationale**: "`t₃` is the dominant input
(sensitivity `−2/72`, four times `t₂`'s `−1/144`)", to justify *why* the near-Sidon improvement
attacks the third energy `E₃` rather than `E₂`. But it never proves it: the sensitivity is stated in
prose only (grep-confirmed: no `1/36`, `1/144` sensitivity statement anywhere in `ProximityGap`).

This file formalises that quantitative core: the per-unit sensitivities of the saving in each energy
exponent, and the exact `4×` dominance of `t₃` over `t₂`.

**The bricks.** The saving is affine in `(t₂,t₃)`, so a one-unit DECREASE in an exponent raises the
saving by exactly the negated slope:

  `diBenedettoSaving t₂ t₃ − diBenedettoSaving t₂ (t₃+1) = 1/36`   (per-unit `t₃`-decrease)
  `diBenedettoSaving t₂ t₃ − diBenedettoSaving (t₂+1) t₃ = 1/144`  (per-unit `t₂`-decrease)

Both hold for ALL `(t₂,t₃)` (the formula is affine, so finite differences equal the exact slopes).
The `t₃`-step is exactly `4×` the `t₂`-step (`(1/36)/(1/144) = 4`): the `t₃`-dominance the cited
near-Sidon improvement leans on. Lowering the third-energy exponent from di Benedetto's pessimistic
`t₃=4` to the dyadic near-Sidon `t₃=3` is the dominant lever, worth four times as much edge saving
per unit as the corresponding move in `t₂`.

**HONESTY.** This is the energy-method LEVER-SELECTION arithmetic, the quantitative basis for
the near-Sidon target. It does NOT push past the `1/24` ceiling (proven in the parent file): the
energy/sum-product/di-Benedetto family is provably capped `12×` short of the prize cancellation
exponent `1/2`, so this sensitivity theorem identifies the best lever WITHIN a method that cannot
close the prize. It is exponent bookkeeping over `ℝ`, field-universal, NOT thinness-essential, NOT a
moment/census/orbit/pencil/resonance object, and touches NEITHER `δ*` NOR the cliff-at-n/2 incidence
object. CORE `M(μ_n) ≤ C√(n·log(p/n))` UNCHANGED/OPEN. Issue #444.
-/

namespace ProximityGap.Frontier.DiBenedettoNearSidon

/-- **Per-unit `t₃`-decrease sensitivity.** Lowering the third-energy exponent `t₃` by one lifts the
di Benedetto edge saving by exactly `1/36`, for ANY `(t₂, t₃)` (the saving is affine in `t₃`). -/
theorem diBenedettoSaving_t3_step (t₂ t₃ : ℝ) :
    diBenedettoSaving t₂ t₃ - diBenedettoSaving t₂ (t₃ + 1) = 1 / 36 := by
  unfold diBenedettoSaving; ring

/-- **Per-unit `t₂`-decrease sensitivity.** Lowering the 2nd-energy exponent `t₂` by one lifts the
di Benedetto edge saving by exactly `1/144`, for ANY `(t₂, t₃)` (the saving is affine in `t₂`). -/
theorem diBenedettoSaving_t2_step (t₂ t₃ : ℝ) :
    diBenedettoSaving t₂ t₃ - diBenedettoSaving (t₂ + 1) t₃ = 1 / 144 := by
  unfold diBenedettoSaving; ring

/-- **The `t₃`-dominance (the lever-selection theorem).** A one-unit cut in `t₃` is worth exactly
`4×` a one-unit cut in `t₂`: the `t₃`-step `1/36` equals four times the `t₂`-step `1/144`. This is
the quantitative basis the near-Sidon improvement leans on: `t₃` (the third additive energy
`E₃`) is the dominant exponent to attack. -/
theorem diBenedettoSaving_t3_dominates_t2 (t₂ t₃ t₂' t₃' : ℝ) :
    diBenedettoSaving t₂ t₃ - diBenedettoSaving t₂ (t₃ + 1)
      = 4 * (diBenedettoSaving t₂' t₃' - diBenedettoSaving (t₂' + 1) t₃') := by
  rw [diBenedettoSaving_t3_step, diBenedettoSaving_t2_step]; norm_num

/-- **Strict `t₃`-dominance.** A unit decrease in `t₃` strictly outperforms a unit decrease in `t₂`
for the edge saving (`1/36 > 1/144`). -/
theorem diBenedettoSaving_t3_step_gt_t2_step (t₂ t₃ t₂' t₃' : ℝ) :
    diBenedettoSaving t₂' t₃' - diBenedettoSaving (t₂' + 1) t₃'
      < diBenedettoSaving t₂ t₃ - diBenedettoSaving t₂ (t₃ + 1) := by
  rw [diBenedettoSaving_t3_step, diBenedettoSaving_t2_step]; norm_num

/-- **The absolute `t₃`-slope.** Increasing `t₃` by one LOWERS the saving by exactly `1/36`
(the negated sensitivity, matching the docstring's `−2/72 = −1/36`). -/
theorem diBenedettoSaving_t3_slope (t₂ t₃ : ℝ) :
    diBenedettoSaving t₂ (t₃ + 1) - diBenedettoSaving t₂ t₃ = -(1 / 36) := by
  unfold diBenedettoSaving; ring

/-- **The absolute `t₂`-slope.** Increasing `t₂` by one LOWERS the saving by exactly `1/144`
(the negated sensitivity, matching the docstring's `−1/144`). -/
theorem diBenedettoSaving_t2_slope (t₂ t₃ : ℝ) :
    diBenedettoSaving (t₂ + 1) t₃ - diBenedettoSaving t₂ t₃ = -(1 / 144) := by
  unfold diBenedettoSaving; ring

end ProximityGap.Frontier.DiBenedettoNearSidon

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.DiBenedettoNearSidon.diBenedettoSaving_t3_step
#print axioms ProximityGap.Frontier.DiBenedettoNearSidon.diBenedettoSaving_t2_step
#print axioms ProximityGap.Frontier.DiBenedettoNearSidon.diBenedettoSaving_t3_dominates_t2
#print axioms ProximityGap.Frontier.DiBenedettoNearSidon.diBenedettoSaving_t3_step_gt_t2_step
#print axioms ProximityGap.Frontier.DiBenedettoNearSidon.diBenedettoSaving_t3_slope
#print axioms ProximityGap.Frontier.DiBenedettoNearSidon.diBenedettoSaving_t2_slope
