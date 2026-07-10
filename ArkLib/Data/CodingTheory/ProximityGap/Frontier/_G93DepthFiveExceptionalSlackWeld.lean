/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G81FactorialPaddingWickAbsorption

/-!
# G93: conditional quotient-envelope calibration for the depth-five exception

G91 isolates the only possible short scaling-orbit stratum for disjoint five-set equal-sum pairs:
the side-swapping `B = -A`, zero-sum exception.  Its crude orbit count is at most `n^3`.  The
generic free-orbit sector still needs the factor-ten incidence estimate
`n^8 / (2 * (5!)^2 * 10) = n^8 / 288000`.

This file checks the quotient-envelope arithmetic.  At production parameters, the stated
depth-zero through depth-four envelopes, a generic factor-ten *quotient allowance*, and the
additional `n^3` exceptional allowance fit jointly inside one Wick budget.

**Retraction (same day).**  G83's free-action interpretation was red-teamed after this file was
written: a decoder for raw endpoint mass cannot store only a scaling-orbit representative, because
reconstructing the actual core also needs its scale in the subgroup.  That restores the factor
`n`.  Therefore the declarations below are true arithmetic diagnostics for a hypothetical
quotient envelope, but they do **not** give a sufficient raw-sector target and do not establish
that the exceptional stratum is free in the corrected decoder.  The honest raw-sector frontier is
G84's canonical-slot/actual-energy route.  Issue #466/#505.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G93DepthFiveExceptionalSlackWeld

open ArkLib.ProximityGap.Frontier.G81FactorialPaddingWickAbsorption

/-- **Conditional quotient-envelope arithmetic.**  If quotient counts were valid decoder core
coordinates, the crude `n^3` exception could be added to the factor-ten quotient allowance.  The
G83 retraction explains why this hypothesis is unavailable for raw endpoint sectors. -/
theorem production_zero_through_five_with_exception_fit :
    correctedPadEnvelope (2 ^ 30) 110 1 0 +
      correctedPadEnvelope (2 ^ 30) 110 ((2 ^ 30) ^ 2) 1 +
      correctedPadEnvelope (2 ^ 30) 110 ((2 ^ 30) ^ 4) 2 +
      correctedPadEnvelope (2 ^ 30) 110 ((2 ^ 30) ^ 5) 3 +
      correctedPadEnvelope (2 ^ 30) 110 ((2 ^ 30) ^ 6) 4 +
      correctedPadEnvelope (2 ^ 30) 110
        (((2 ^ 30) ^ 8) / (28800 * 10) + (2 ^ 30) ^ 3) 5 ≤
      Nat.doubleFactorial (2 * 110 - 1) * (2 ^ 30) ^ 110 := by
  norm_num [correctedPadEnvelope, Nat.doubleFactorial]

/-- Within the same conditional quotient-envelope model, ninefold saving is insufficient even if
every exceptional orbit is ignored.  This is not a raw-sector lower bound. -/
theorem production_generic_ninefold_fails :
    Nat.doubleFactorial (2 * 110 - 1) * (2 ^ 30) ^ 110 <
      correctedPadEnvelope (2 ^ 30) 110
        (((2 ^ 30) ^ 8) / (28800 * 9)) 5 := by
  norm_num [correctedPadEnvelope, Nat.doubleFactorial]

/-- Arithmetic addition of the two conditional quotient allowances.  It does not construct a
decoder from quotient data. -/
theorem depthFive_count_le_calibrated_of_split
    {generic exceptional : ℕ}
    (hgeneric : generic ≤ ((2 ^ 30) ^ 8) / (28800 * 10))
    (hexceptional : exceptional ≤ (2 ^ 30) ^ 3) :
    generic + exceptional ≤
      ((2 ^ 30) ^ 8) / (28800 * 10) + (2 ^ 30) ^ 3 := by
  exact Nat.add_le_add hgeneric hexceptional

end ArkLib.ProximityGap.Frontier.G93DepthFiveExceptionalSlackWeld

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G93DepthFiveExceptionalSlackWeld.production_zero_through_five_with_exception_fit
#print axioms
  ArkLib.ProximityGap.Frontier.G93DepthFiveExceptionalSlackWeld.production_generic_ninefold_fails
#print axioms
  ArkLib.ProximityGap.Frontier.G93DepthFiveExceptionalSlackWeld.depthFive_count_le_calibrated_of_split
