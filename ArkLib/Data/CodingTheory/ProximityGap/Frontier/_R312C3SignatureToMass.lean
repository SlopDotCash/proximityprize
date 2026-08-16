/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# R312 (#466): `c = 3` signature histogram ⇒ relation-web mass

R311 sharpened the `c = 3` relation-web target from a delta histogram to three
fiber-count signatures:

* `(3n-3, 3, 1)`, appearing `n` times;
* `(6, 3, 3)`, appearing `2n` times;
* `(6, 3)`, appearing `n(n-7)` times.

This file proves the arithmetic bridge from those signatures to the R309 mass formula.
The missing hard statement remains the finite-combinatorial classification saying these
are exactly the positive collision fibers under the nondegenerate `g^21 = 3` relation.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.R312C3SignatureToMass

/-- The L² merge delta of three counts. -/
def delta3 (a b c : ℤ) : ℤ :=
  (a + b + c) ^ 2 - (a ^ 2 + b ^ 2 + c ^ 2)

/-- The L² merge delta of two counts. -/
def delta2 (a b : ℤ) : ℤ :=
  (a + b) ^ 2 - (a ^ 2 + b ^ 2)

/-- The large `c=3` signature `(3n-3,3,1)` has delta `24n-18`. -/
theorem delta_large_signature (n : ℤ) :
    delta3 (3 * n - 3) 3 1 = 24 * n - 18 := by
  unfold delta3
  ring

/-- The middle `c=3` signature `(6,3,3)` has delta `90`. -/
theorem delta_middle_signature :
    delta3 6 3 3 = 90 := by
  unfold delta3
  norm_num

/-- The small `c=3` signature `(6,3)` has delta `36`. -/
theorem delta_small_signature :
    delta2 6 3 = 36 := by
  unfold delta2
  norm_num

/-- The R311 signature multiplicities imply total mass `60n² - 90n`. -/
theorem c3SignatureMass_eq (n : ℤ) :
    n * delta3 (3 * n - 3) 3 1 + (2 * n) * delta3 6 3 3
      + (n * (n - 7)) * delta2 6 3 = 60 * n * n - 90 * n := by
  rw [delta_large_signature, delta_middle_signature, delta_small_signature]
  ring

/-- The R311 signature mass beats exact-Wick depth-3 headroom for every `n >= 4`. -/
theorem depth3Headroom_lt_c3SignatureMass {n : ℤ} (hn : 4 ≤ n) :
    45 * n * n - 40 * n
      < n * delta3 (3 * n - 3) 3 1 + (2 * n) * delta3 6 3 3
        + (n * (n - 7)) * delta2 6 3 := by
  rw [c3SignatureMass_eq]
  nlinarith

end ArkLib.ProximityGap.Frontier.R312C3SignatureToMass

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R312C3SignatureToMass.delta_large_signature
#print axioms ArkLib.ProximityGap.Frontier.R312C3SignatureToMass.delta_middle_signature
#print axioms ArkLib.ProximityGap.Frontier.R312C3SignatureToMass.delta_small_signature
#print axioms ArkLib.ProximityGap.Frontier.R312C3SignatureToMass.c3SignatureMass_eq
#print axioms ArkLib.ProximityGap.Frontier.R312C3SignatureToMass.depth3Headroom_lt_c3SignatureMass
