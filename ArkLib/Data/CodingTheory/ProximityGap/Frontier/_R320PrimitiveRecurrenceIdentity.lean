/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# R320: the dominant depth-4 relation reduces to one primitive recurrence

The R320 complete collision-orbit census at `n = 32`, `p = 1439393` finds that its two
largest relation orbits carry 96.4% of the wraparound mass.  This file records the exact
algebra identifying those orbits.

If `x^16 = -1`, multiplication of

`f(x) = 2 + x + x^4 + x^8 + x^12`

by the cyclotomic multiplier `x^4 - 1` gives

`h(x) = x^5 + x^4 - x - 3`.

Thus the dominant five-term collision relation implies the primitive recurrence
`(1+x)x^4 = x+3`.  The companion probe checks
`Res(x^16+1,h) = 2^5 * 1439393` exactly.

Issue #466, round 320.  No transfer bound is claimed here.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.R320PrimitiveRecurrenceIdentity

/-- Reduction of the dominant depth-4 relation modulo `x^16 + 1`. -/
theorem multiplier_identity {R : Type*} [CommRing R] (x : R) (hx : x ^ 16 = -1) :
    (x ^ 4 - 1) * (2 + x + x ^ 4 + x ^ 8 + x ^ 12) =
      x ^ 5 + x ^ 4 - x - 3 := by
  calc
    (x ^ 4 - 1) * (2 + x + x ^ 4 + x ^ 8 + x ^ 12) =
        x ^ 16 + x ^ 5 + x ^ 4 - x - 2 := by ring
    _ = x ^ 5 + x ^ 4 - x - 3 := by rw [hx]; ring

/-- A zero of the dominant five-term relation satisfies the primitive recurrence. -/
theorem primitive_recurrence_of_dominant_relation {R : Type*} [CommRing R] (x : R)
    (hx : x ^ 16 = -1) (hrel : 2 + x + x ^ 4 + x ^ 8 + x ^ 12 = 0) :
    (1 + x) * x ^ 4 = x + 3 := by
  have hid := multiplier_identity x hx
  rw [hrel, mul_zero] at hid
  linear_combination -hid

#print axioms multiplier_identity
#print axioms primitive_recurrence_of_dominant_relation

end ArkLib.ProximityGap.Frontier.R320PrimitiveRecurrenceIdentity
