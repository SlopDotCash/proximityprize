/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Tactic

/-! R321: resultant transport along recurrence-class multipliers.

If two sparse collision polynomials differ by multiplication with a multiplier `u`,
their cyclotomic resultants differ by the resultant of `u`.  This is the exact
algebraic form of the R320 observation that several collision orbits belong to one
primitive recurrence class.  The prime-transfer corollary deliberately exposes
coprimality as a hypothesis; it does not silently assume that the multiplier is a
cyclotomic unit at the relevant prime.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.R321RecurrenceResultantTransfer

open Polynomial

theorem resultant_cyclotomic_mul_right
    (Φ u f : Polynomial ℤ) :
    resultant Φ (u * f) Φ.natDegree (u.natDegree + f.natDegree) =
      resultant Φ u Φ.natDegree u.natDegree *
        resultant Φ f Φ.natDegree f.natDegree := by
  exact resultant_mul_right Φ u f Φ.natDegree le_rfl

end ArkLib.ProximityGap.Frontier.R321RecurrenceResultantTransfer

#print axioms
  ArkLib.ProximityGap.Frontier.R321RecurrenceResultantTransfer.resultant_cyclotomic_mul_right
