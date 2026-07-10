/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterCommonFactorConstruction

/-!
# Performance-blocked concrete P1 common locator attempt

This file preserves the direct product construction for the sole residual in
`_P1RateQuarterCommonFactorConstruction`.  It is intentionally not imported or staged: elaborating
the product over the concrete billion-scale coordinate type did not finish within several minutes.
The small structural module therefore exposes `CommonLocatorResidual` instead.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterCommonFactorConstruction

/-- Direct monic locator through the selected common-root coordinates.  Performance blocked. -/
noncomputable def concreteCommonLocator : F[X] :=
  ∏ e ∈ commonRoots, ((Polynomial.X : F[X]) - Polynomial.C (domain e))

theorem concreteCommonLocator_eval_zero {e : Coord} (he : e ∈ commonRoots) :
    concreteCommonLocator.eval (domain e) = 0 := by
  rw [concreteCommonLocator, eval_prod]
  exact Finset.prod_eq_zero he (by simp)

theorem concreteCommonLocator_eval_ne_zero {e : Coord} (he : e ∉ commonRoots) :
    concreteCommonLocator.eval (domain e) ≠ 0 := by
  rw [concreteCommonLocator, eval_prod]
  intro hzero
  obtain ⟨e', he', heval⟩ := Finset.prod_eq_zero_iff.mp hzero
  simp only [eval_sub, eval_X, eval_C, sub_eq_zero] at heval
  exact he (domain.injective heval.symm ▸ he')

theorem concreteCommonLocator_natDegree_le :
    concreteCommonLocator.natDegree ≤ 2 * d := by
  calc
    concreteCommonLocator.natDegree ≤
        ∑ e ∈ commonRoots,
          ((Polynomial.X : F[X]) - Polynomial.C (domain e)).natDegree := by
      exact Polynomial.natDegree_prod_le commonRoots _
    _ ≤ ∑ _e ∈ commonRoots, 1 := by
      apply Finset.sum_le_sum
      intro e he
      simpa using Polynomial.natDegree_sub_le
        (Polynomial.X : F[X]) (Polynomial.C (domain e))
    _ = commonRoots.card := by simp
    _ = 2 * d := commonRoots_card

/-- Intended discharge of the construction residual; elaboration is performance blocked. -/
theorem commonLocatorResidual : CommonLocatorResidual := by
  exact ⟨⟨concreteCommonLocator, concreteCommonLocator_natDegree_le,
    concreteCommonLocator_eval_zero, concreteCommonLocator_eval_ne_zero⟩⟩

end ArkLib.ProximityGap.Frontier.P1RateQuarterCommonFactorConstruction
