/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.CrossStepRungSlackDepletion
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvL2_E7ClosedForm

/-!
# The rung-slack/depletion-defect bridge at `r = 6` (#444)

`CrossStepRungSlackDepletion` proved the exact bridge

`stepTarget r − (E_{r+1} − nE_r) = δ̂_{r+1} − nδ̂_r`

through the contiguous range `r = 2..5`.  After `CrossStepRungSix` landed the concrete `r = 6`
cross-step rung from the in-tree `E_6,E_7` closed forms, this file extends the same char-`0` ℤ-carrier
bridge one more rung.

Honest scope: this is still a finite char-`0` identity/reformulation.  It does not prove the `∀ r`
M3CrossStepBound, does not transfer to char `p` at prize depth, and does not touch CORE.
-/

set_option linter.style.longLine false
set_option autoImplicit false


namespace ProximityGap.Frontier.ShawDepletionSix

open ProximityGap.Frontier.ShawDepletion
open ProximityGap.Frontier.E7ClosedForm (E7)

/-- The `r = 6` step target is the one-step Wick gap `wick 7 − n·wick 6`. -/
theorem stepTarget_eq_wickGap_six (n : ℤ) :
    stepTarget 6 n = E7ClosedForm.wick 7 n - n * ProximityGap.Frontier.CharZeroEnergy.wick 6 n := by
  simp only [stepTarget, E7ClosedForm.wick, ProximityGap.Frontier.CharZeroEnergy.wick, Nat.doubleFactorial]
  ring

/-- **THE BRIDGE at `r = 6`.** The rung slack equals the depletion-defect difference
`δ̂_7 − n·δ̂_6`, with `δ̂_7` supplied by the in-tree exact `E_7` closed form. -/
theorem rungSlack_eq_defect_diff_six (n : ℤ) :
    stepTarget 6 n - crossMassZ ProximityGap.Frontier.CharZeroEnergy.E6 E7 n
      = E7ClosedForm.wick 7 n - E7 n - n * depletionDefect ProximityGap.Frontier.CharZeroEnergy.E6 6 n := by
  simp only [stepTarget, crossMassZ, depletionDefect, E7ClosedForm.wick,
    ProximityGap.Frontier.ShawDepletion.wick, ProximityGap.Frontier.CharZeroEnergy.E6, E7,
    Nat.doubleFactorial]
  ring

/-- **The characterization at `r = 6`: the rung is defect-superlinearity.** -/
theorem crossStepRung_iff_defect_superlinear_six (n : ℤ) :
    crossMassZ ProximityGap.Frontier.CharZeroEnergy.E6 E7 n ≤ stepTarget 6 n
      ↔ n * depletionDefect ProximityGap.Frontier.CharZeroEnergy.E6 6 n ≤ E7ClosedForm.wick 7 n - E7 n := by
  have h := rungSlack_eq_defect_diff_six n
  constructor
  · intro hr; linarith
  · intro hd; linarith

/-- **Defect superlinearity at `r = 6` (`n ≥ 2`).**
The slack is
`2681910n⁶ − 25779600n⁵ + 138357450n⁴ − 427479822n³ + 704625768n² − 471556800n`, whose shift by
`n = t + 2` has all nonnegative coefficients. -/
theorem defect_superlinear_six (n : ℤ) (hn : 2 ≤ n) :
    n * depletionDefect ProximityGap.Frontier.CharZeroEnergy.E6 6 n ≤ E7ClosedForm.wick 7 n - E7 n := by
  rw [ProximityGap.Frontier.ShawDepletion.defect_six, E7ClosedForm.deficit_seven]
  have ht : (0 : ℤ) ≤ n - 2 := by linarith
  have hshift :
      2681910 * n ^ 6 - 25779600 * n ^ 5 + 138357450 * n ^ 4 - 427479822 * n ^ 3
          + 704625768 * n ^ 2 - 471556800 * n
        = 2681910 * (n - 2) ^ 6 + 6403320 * (n - 2) ^ 5 + 41476050 * (n - 2) ^ 4
          + 77301378 * (n - 2) ^ 3 + 41616036 * (n - 2) ^ 2 + 97185528 * (n - 2)
          + 15965136 := by
    ring
  nlinarith [hshift, pow_nonneg ht 6, pow_nonneg ht 5, pow_nonneg ht 4, pow_nonneg ht 3,
    pow_nonneg ht 2, ht]

/-- **The `r = 6` rung on the ℤ-carrier, from defect superlinearity.** -/
theorem crossStepRungZ_six (n : ℤ) (hn : 2 ≤ n) :
    crossMassZ ProximityGap.Frontier.CharZeroEnergy.E6 E7 n ≤ stepTarget 6 n :=
  (crossStepRung_iff_defect_superlinear_six n).mpr (defect_superlinear_six n hn)

end ProximityGap.Frontier.ShawDepletionSix

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.ShawDepletionSix.stepTarget_eq_wickGap_six
#print axioms ProximityGap.Frontier.ShawDepletionSix.rungSlack_eq_defect_diff_six
#print axioms ProximityGap.Frontier.ShawDepletionSix.crossStepRung_iff_defect_superlinear_six
#print axioms ProximityGap.Frontier.ShawDepletionSix.defect_superlinear_six
#print axioms ProximityGap.Frontier.ShawDepletionSix.crossStepRungZ_six
