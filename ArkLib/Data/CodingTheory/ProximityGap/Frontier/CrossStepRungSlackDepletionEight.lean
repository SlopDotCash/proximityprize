/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.CrossStepRungSlackDepletionSeven
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvL2_E9ClosedForm

/-!
# The rung-slack/depletion-defect bridge at `r = 8` (#444)

This file extends the same finite char-`0` ℤ-carrier bridge used for the previous concrete
cross-step rungs:

`stepTarget 8 − (E_9 − nE_8) = δ̂_9 − nδ̂_8`.

The bridge is only an exact algebraic reformulation of one finite rung.  It does not prove the
`∀ r` cross-step statement, does not transfer the char-`0` moment ladder to char `p` at prize depth,
and does not touch CORE.
-/

set_option linter.style.longLine false
set_option autoImplicit false


namespace ProximityGap.Frontier.ShawDepletionEight

open ProximityGap.Frontier.ShawDepletion
open ProximityGap.Frontier.E8ClosedForm (E8)
open ProximityGap.Frontier.E9ClosedForm (E9)

/-- The `r = 8` step target is the one-step Wick gap `wick 9 − n·wick 8`. -/
theorem stepTarget_eq_wickGap_eight (n : ℤ) :
    stepTarget 8 n = E9ClosedForm.wick 9 n - n * E8ClosedForm.wick 8 n := by
  simp only [stepTarget, E9ClosedForm.wick, E8ClosedForm.wick, Nat.doubleFactorial]
  ring

/-- **THE BRIDGE at `r = 8`.** The rung slack equals the depletion-defect difference
`δ̂_9 − n·δ̂_8`, with `δ̂_9` supplied by the in-tree exact `E_9` closed form. -/
theorem rungSlack_eq_defect_diff_eight (n : ℤ) :
    stepTarget 8 n - crossMassZ E8 E9 n
      = E9ClosedForm.wick 9 n - E9 n - n * (E8ClosedForm.wick 8 n - E8 n) := by
  simp only [stepTarget, crossMassZ, E9ClosedForm.wick, E8ClosedForm.wick, E8, E9,
    Nat.doubleFactorial]
  ring

/-- **The characterization at `r = 8`: the rung is defect-superlinearity.** -/
theorem crossStepRung_iff_defect_superlinear_eight (n : ℤ) :
    crossMassZ E8 E9 n ≤ stepTarget 8 n
      ↔ n * (E8ClosedForm.wick 8 n - E8 n) ≤ E9ClosedForm.wick 9 n - E9 n := by
  have h := rungSlack_eq_defect_diff_eight n
  constructor
  · intro hr; linarith
  · intro hd; linarith

/-- **Defect superlinearity at `r = 8` (`n ≥ 4`).**
The slack `δ̂_9 − nδ̂_8`, after shifting `n = t + 4`, is a polynomial in `t` with every
coefficient nonnegative. -/
theorem defect_superlinear_eight (n : ℤ) (hn : 4 ≤ n) :
    n * (E8ClosedForm.wick 8 n - E8 n) ≤ E9ClosedForm.wick 9 n - E9 n := by
  rw [E8ClosedForm.deficit_eight, E9ClosedForm.deficit_nine]
  have ht : (0 : ℤ) ≤ n - 4 := by linarith
  have hshift :
      1183782600 * n ^ 8 - 20016196200 * n ^ 7 + 201524122800 * n ^ 6
          - 1302291310320 * n ^ 5 + 5454328960080 * n ^ 4 - 14250325020360 * n ^ 3
          + 20888979008040 * n ^ 2 - 12885585512800 * n
        = 1183782600 * (n - 4) ^ 8 + 17864847000 * (n - 4) ^ 7
          + 171405234000 * (n - 4) ^ 6 + 1051522552080 * (n - 4) ^ 5
          + 4151396929680 * (n - 4) ^ 4 + 11140917336120 * (n - 4) ^ 3
          + 19224227622600 * (n - 4) ^ 2 + 19006568129120 * (n - 4)
          + 8500257708800 := by
    ring
  nlinarith [hshift, pow_nonneg ht 8, pow_nonneg ht 7, pow_nonneg ht 6, pow_nonneg ht 5,
    pow_nonneg ht 4, pow_nonneg ht 3, pow_nonneg ht 2, ht]

/-- **The `r = 8` rung on the ℤ-carrier, from defect superlinearity.** -/
theorem crossStepRungZ_eight (n : ℤ) (hn : 4 ≤ n) :
    crossMassZ E8 E9 n ≤ stepTarget 8 n :=
  (crossStepRung_iff_defect_superlinear_eight n).mpr (defect_superlinear_eight n hn)

end ProximityGap.Frontier.ShawDepletionEight

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.ShawDepletionEight.stepTarget_eq_wickGap_eight
#print axioms ProximityGap.Frontier.ShawDepletionEight.rungSlack_eq_defect_diff_eight
#print axioms ProximityGap.Frontier.ShawDepletionEight.crossStepRung_iff_defect_superlinear_eight
#print axioms ProximityGap.Frontier.ShawDepletionEight.defect_superlinear_eight
#print axioms ProximityGap.Frontier.ShawDepletionEight.crossStepRungZ_eight
