/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.CrossStepRungSlackDepletionSix
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvL2_E8ClosedForm

/-!
# The rung-slack/depletion-defect bridge at `r = 7` (#444)

After `CrossStepRungSeven` extends the concrete cross-step prefix to `r = 7`, this file extends the
same char-`0` ℤ-carrier bridge one rung:

`stepTarget 7 − (E_8 − nE_7) = δ̂_8 − nδ̂_7`.

It is an exact algebraic reformulation: the `r = 7` rung is equivalent to defect superlinearity
`n·δ̂_7 ≤ δ̂_8`, and the displayed in-tree deficits prove that inequality for `n ≥ 3` by a shifted
nonnegative polynomial certificate.  This is still finite char-`0` bookkeeping only; no `∀ r`, no
char-`p` transfer at prize depth, and no CORE/capacity claim.
-/

set_option linter.style.longLine false
set_option autoImplicit false


namespace ProximityGap.Frontier.ShawDepletionSeven

open ProximityGap.Frontier.ShawDepletion
open ProximityGap.Frontier.E7ClosedForm (E7)
open ProximityGap.Frontier.E8ClosedForm (E8)

/-- The `r = 7` step target is the one-step Wick gap `wick 8 − n·wick 7`. -/
theorem stepTarget_eq_wickGap_seven (n : ℤ) :
    stepTarget 7 n = E8ClosedForm.wick 8 n - n * E7ClosedForm.wick 7 n := by
  simp only [stepTarget, E8ClosedForm.wick, E7ClosedForm.wick, Nat.doubleFactorial]
  ring

/-- **THE BRIDGE at `r = 7`.** The rung slack equals the depletion-defect difference
`δ̂_8 − n·δ̂_7`, with `δ̂_8` supplied by the in-tree exact `E_8` closed form. -/
theorem rungSlack_eq_defect_diff_seven (n : ℤ) :
    stepTarget 7 n - crossMassZ E7 E8 n
      = E8ClosedForm.wick 8 n - E8 n - n * (E7ClosedForm.wick 7 n - E7 n) := by
  simp only [stepTarget, crossMassZ, E8ClosedForm.wick, E7ClosedForm.wick, E7, E8,
    Nat.doubleFactorial]
  ring

/-- **The characterization at `r = 7`: the rung is defect-superlinearity.** -/
theorem crossStepRung_iff_defect_superlinear_seven (n : ℤ) :
    crossMassZ E7 E8 n ≤ stepTarget 7 n
      ↔ n * (E7ClosedForm.wick 7 n - E7 n) ≤ E8ClosedForm.wick 8 n - E8 n := by
  have h := rungSlack_eq_defect_diff_seven n
  constructor
  · intro hr; linarith
  · intro hd; linarith

/-- **Defect superlinearity at `r = 7` (`n ≥ 3`).**
The slack is
`53918865n⁷ − 701575875n⁶ + 5297292000n⁵ − 24622149552n⁴ + 69225978822n³
 − 106967055195n² + 68492499075n`; after shifting `n = t + 3`, every coefficient is nonnegative. -/
theorem defect_superlinear_seven (n : ℤ) (hn : 3 ≤ n) :
    n * (E7ClosedForm.wick 7 n - E7 n) ≤ E8ClosedForm.wick 8 n - E8 n := by
  rw [E7ClosedForm.deficit_seven, E8ClosedForm.deficit_eight]
  have ht : (0 : ℤ) ≤ n - 3 := by linarith
  have hshift :
      53918865 * n ^ 7 - 701575875 * n ^ 6 + 5297292000 * n ^ 5
          - 24622149552 * n ^ 4 + 69225978822 * n ^ 3 - 106967055195 * n ^ 2
          + 68492499075 * n
        = 53918865 * (n - 3) ^ 7 + 430720290 * (n - 3) ^ 6
          + 2859591735 * (n - 3) ^ 5 + 11077814748 * (n - 3) ^ 4
          + 24525473973 * (n - 3) ^ 3 + 39472798365 * (n - 3) ^ 2
          + 34253046828 * (n - 3) + 11195015832 := by
    ring
  nlinarith [hshift, pow_nonneg ht 7, pow_nonneg ht 6, pow_nonneg ht 5, pow_nonneg ht 4,
    pow_nonneg ht 3, pow_nonneg ht 2, ht]

/-- **The `r = 7` rung on the ℤ-carrier, from defect superlinearity.** -/
theorem crossStepRungZ_seven (n : ℤ) (hn : 3 ≤ n) :
    crossMassZ E7 E8 n ≤ stepTarget 7 n :=
  (crossStepRung_iff_defect_superlinear_seven n).mpr (defect_superlinear_seven n hn)

end ProximityGap.Frontier.ShawDepletionSeven

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.ShawDepletionSeven.stepTarget_eq_wickGap_seven
#print axioms ProximityGap.Frontier.ShawDepletionSeven.rungSlack_eq_defect_diff_seven
#print axioms ProximityGap.Frontier.ShawDepletionSeven.crossStepRung_iff_defect_superlinear_seven
#print axioms ProximityGap.Frontier.ShawDepletionSeven.defect_superlinear_seven
#print axioms ProximityGap.Frontier.ShawDepletionSeven.crossStepRungZ_seven
