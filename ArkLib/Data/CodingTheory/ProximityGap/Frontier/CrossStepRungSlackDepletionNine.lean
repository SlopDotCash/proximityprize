/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.CrossStepRungSlackDepletionEight
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvL2_E10ClosedForm

/-!
# The rung-slack/depletion-defect bridge at `r = 9` (#444)

This extends the finite char-`0` ℤ-carrier bridge one more adjacent rung:

`stepTarget 9 − (E_10 − nE_9) = δ̂_10 − nδ̂_9`.

Honest scope: this is exact arithmetic on already-landed char-`0` closed forms.  It does not prove
the all-`r` cross-step statement, does not transfer to char `p` in the prize regime, and does not
change CORE.
-/

set_option linter.style.longLine false
set_option autoImplicit false


namespace ProximityGap.Frontier.ShawDepletionNine

open ProximityGap.Frontier.ShawDepletion
open ProximityGap.Frontier.E9ClosedForm (E9)
open ProximityGap.Frontier.E10ClosedForm (E10)

/-- The `r = 9` step target is the one-step Wick gap `wick 10 − n·wick 9`. -/
theorem stepTarget_eq_wickGap_nine (n : ℤ) :
    stepTarget 9 n = E10ClosedForm.wick 10 n - n * E9ClosedForm.wick 9 n := by
  simp only [stepTarget, E10ClosedForm.wick, E9ClosedForm.wick, Nat.doubleFactorial]
  ring

/-- **THE BRIDGE at `r = 9`.** The rung slack equals the depletion-defect difference
`δ̂_10 − n·δ̂_9`, with `δ̂_10` supplied by the in-tree exact `E_10` closed form. -/
theorem rungSlack_eq_defect_diff_nine (n : ℤ) :
    stepTarget 9 n - crossMassZ E9 E10 n
      = E10ClosedForm.wick 10 n - E10 n - n * (E9ClosedForm.wick 9 n - E9 n) := by
  simp only [stepTarget, crossMassZ, E10ClosedForm.wick, E9ClosedForm.wick, E9, E10,
    Nat.doubleFactorial]
  ring

/-- **The characterization at `r = 9`: the rung is defect-superlinearity.** -/
theorem crossStepRung_iff_defect_superlinear_nine (n : ℤ) :
    crossMassZ E9 E10 n ≤ stepTarget 9 n
      ↔ n * (E9ClosedForm.wick 9 n - E9 n) ≤ E10ClosedForm.wick 10 n - E10 n := by
  have h := rungSlack_eq_defect_diff_nine n
  constructor
  · intro hr; linarith
  · intro hd; linarith

/-- **Defect superlinearity at `r = 9` (`n ≥ 4`).**
The slack `δ̂_10 − nδ̂_9`, after shifting `n = t + 4`, has all coefficients nonnegative. -/
theorem defect_superlinear_nine (n : ℤ) (hn : 4 ≤ n) :
    n * (E9ClosedForm.wick 9 n - E9 n) ≤ E10ClosedForm.wick 10 n - E10 n := by
  rw [E9ClosedForm.deficit_nine, E10ClosedForm.deficit_ten]
  have ht : (0 : ℤ) ≤ n - 4 := by linarith
  have hshift :
      28222269075 * n ^ 9 - 601248047400 * n ^ 8 + 7767636826950 * n ^ 7
          - 66260291577480 * n ^ 6 + 382601968884135 * n ^ 5 - 1478178449696520 * n ^ 4
          + 3638680020910935 * n ^ 3 - 5102863644440133 * n ^ 2 + 3048056301418128 * n
        = 28222269075 * (n - 4) ^ 9 + 414753639300 * (n - 4) ^ 8
          + 4783726297350 * (n - 4) ^ 7 + 33597332889120 * (n - 4) ^ 6
          + 157745454281415 * (n - 4) ^ 5 + 537882477483780 * (n - 4) ^ 4
          + 1221291354441015 * (n - 4) ^ 3 + 1807403765362767 * (n - 4) ^ 2
          + 1648464415358904 * (n - 4) + 650375189356464 := by
    ring
  nlinarith [hshift, pow_nonneg ht 9, pow_nonneg ht 8, pow_nonneg ht 7, pow_nonneg ht 6,
    pow_nonneg ht 5, pow_nonneg ht 4, pow_nonneg ht 3, pow_nonneg ht 2, ht]

/-- **The `r = 9` rung on the ℤ-carrier, from defect superlinearity.** -/
theorem crossStepRungZ_nine (n : ℤ) (hn : 4 ≤ n) :
    crossMassZ E9 E10 n ≤ stepTarget 9 n :=
  (crossStepRung_iff_defect_superlinear_nine n).mpr (defect_superlinear_nine n hn)

end ProximityGap.Frontier.ShawDepletionNine

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.ShawDepletionNine.stepTarget_eq_wickGap_nine
#print axioms ProximityGap.Frontier.ShawDepletionNine.rungSlack_eq_defect_diff_nine
#print axioms ProximityGap.Frontier.ShawDepletionNine.crossStepRung_iff_defect_superlinear_nine
#print axioms ProximityGap.Frontier.ShawDepletionNine.defect_superlinear_nine
#print axioms ProximityGap.Frontier.ShawDepletionNine.crossStepRungZ_nine
