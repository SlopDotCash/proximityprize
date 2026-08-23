/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonanceConvolutionOffDiagSign
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonanceMomentConvolutionRecursion

/-!
# The convolution off-diagonal fits inside the trivial Young gap (#444)

The exact real gap identity isolates the lower-recurrence obligation as

`Re Off(r) = T(r+1) − (m−1)T(r)`.

The already-proven convolution/Young upper recurrence gives

`T(r+1) ≤ (m−1)^2 T(r)`.

Combining them kernel-checks the exact remaining room for the off-diagonal:

`Re Off(r) ≤ ((m−1)^2 − (m−1)) T(r) = (m−1)(m−2)T(r)`.

Honest scope: this is an upper envelope on the named off-diagonal budget, not a positivity theorem
and not a CORE bound.  It says the whole open sign/positivity question lives inside the same trivial
CS/Young slack already known from the resonance recursion.
-/

namespace ArkLib.ProximityGap.GaussPhaseResonance

open scoped BigOperators

variable {m : ℕ} [NeZero m]

/-- **The real cast of the nonzero-residue count is `m - 1`.** -/
private theorem real_cast_pred_eq_sub_one :
    (((m : ℕ) - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
  exact Nat.cast_pred (Nat.pos_of_neZero m)

/-- **The off-diagonal real part is bounded by the exact trivial Young gap.**
Combining the exact identity
`Re Off(r) = T(r+1) − (m−1)T(r)` with the proven upper recurrence
`T(r+1) ≤ (m−1)^2 T(r)` gives the precise ceiling
`Re Off(r) ≤ ((m−1)^2 − (m−1))T(r)`. -/
theorem convOffDiag_re_le_trivial_gap
    (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1) (r : ℕ) :
    (convOffDiag u r).re
      ≤ (((m : ℝ) - 1) ^ 2 - ((m : ℝ) - 1)) * resonanceMoment u r := by
  have hupper := resonanceMoment_succ_le u hu r
  have hgap := resonanceMoment_succ_sub_diag_eq_re_convOffDiag u hu r
  rw [real_cast_pred_eq_sub_one] at hgap
  linarith

/-- **Factorized form of the same trivial-gap ceiling.**
The room left by the Cauchy-Schwarz/Young envelope is exactly `(m−1)(m−2)T(r)`. -/
theorem convOffDiag_re_le_trivial_gap_factorized
    (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1) (r : ℕ) :
    (convOffDiag u r).re
      ≤ ((m : ℝ) - 1) * ((m : ℝ) - 2) * resonanceMoment u r := by
  have h := convOffDiag_re_le_trivial_gap u hu r
  convert h using 1
  ring

end ArkLib.ProximityGap.GaussPhaseResonance

#print axioms ArkLib.ProximityGap.GaussPhaseResonance.convOffDiag_re_le_trivial_gap
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.convOffDiag_re_le_trivial_gap_factorized
