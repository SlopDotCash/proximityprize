/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R28IterConvBaseline

/-!
# LANE B2 (#466 round 29): when the no-cancellation baseline already reaches Wick scale

Round 28 made the no-cancellation deficit explicit:

  `∑ ‖J^{∗r}‖² ≤ m^(2r+1) q^r`.

The Wick target from round 27 is

  `∑ ‖J^{∗r}‖² ≤ C^r r! (m q)^r`.

This brick records the exact algebraic bridge between the two.  If the combinatorial/Wick
budget satisfies `m^(r+1) ≤ C^r r!`, then the elementary triangle baseline is already enough
to prove `IterConvEnergyWick`.  Equivalently, the whole missing content below this budget is
precisely the improvement of `m^(r+1)` into the factorial-constant allowance.

This is a bookkeeping theorem, but it is useful at the deep-depth interface: any later argument
that supplies even a partial `m`-saving can be plugged into the same budget comparison.

Axiom-clean (`propext, Classical.choice, Quot.sound`).  Issue #466, round 29, LANE B2.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.Frontier.R29BaselineToWickBudget

open ArkLib.ProximityGap.Frontier.R27FullTowerCollapse
open ArkLib.ProximityGap.Frontier.R28IterConvBaseline

variable {m : ℕ} [NeZero m]

/-- **Baseline-to-Wick budget bridge.**  Under the exact budget inequality
`m^(r+1) ≤ C^r r!`, the no-cancellation iterated-convolution baseline proves the round-27
`IterConvEnergyWick` target. -/
theorem iterConvEnergyWick_of_uniform_sq_bound_of_budget (J : ZMod m → ℂ) (q r : ℕ) {C : ℝ}
    (hJ : ∀ j : ZMod m, ‖J j‖ ^ 2 ≤ (q : ℝ))
    (hbudget : (m : ℝ) ^ (r + 1) ≤ C ^ r * (r.factorial : ℝ)) :
    IterConvEnergyWick J q r C := by
  have hbase := iterConv_energy_le_card_pow_mul_of_uniform_sq_bound J q r hJ
  refine le_trans hbase ?_
  have hm_nonneg : 0 ≤ (m : ℝ) ^ r := by positivity
  have hq_nonneg : 0 ≤ (q : ℝ) ^ r := by positivity
  have hbudget' :
      (m : ℝ) ^ (r + 1) * (m : ℝ) ^ r
        ≤ (C ^ r * (r.factorial : ℝ)) * (m : ℝ) ^ r :=
    mul_le_mul_of_nonneg_right hbudget hm_nonneg
  have hbudget'' :
      ((m : ℝ) ^ (r + 1) * (m : ℝ) ^ r) * (q : ℝ) ^ r
        ≤ ((C ^ r * (r.factorial : ℝ)) * (m : ℝ) ^ r) * (q : ℝ) ^ r :=
    mul_le_mul_of_nonneg_right hbudget' hq_nonneg
  calc (m : ℝ) ^ (2 * r + 1) * (q : ℝ) ^ r
      = ((m : ℝ) ^ (r + 1) * (m : ℝ) ^ r) * (q : ℝ) ^ r := by ring
    _ ≤ ((C ^ r * (r.factorial : ℝ)) * (m : ℝ) ^ r) * (q : ℝ) ^ r := hbudget''
    _ = C ^ r * (r.factorial : ℝ) * ((m : ℝ) * (q : ℝ)) ^ r := by ring

end ArkLib.ProximityGap.Frontier.R29BaselineToWickBudget

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
open ArkLib.ProximityGap.Frontier.R29BaselineToWickBudget in
#print axioms
  iterConvEnergyWick_of_uniform_sq_bound_of_budget
