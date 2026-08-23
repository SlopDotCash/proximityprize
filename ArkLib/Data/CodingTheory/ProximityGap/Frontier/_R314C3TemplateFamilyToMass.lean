/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# R314 (#466): c=3 template-family totals imply the mass bridge

R313/R314 refine the c=3 relation-web target from a raw signature histogram to
normalized template families.  The hard missing theorem is the finite
classification/counting statement saying those families have occurrence totals

* large: `n`;
* middle: `2n`;
* small: `n(n-7)`.

This file is the consumer socket: once those occurrence totals are proved, the
R312 mass formula and depth-3 headroom refutation follow immediately.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.R314C3TemplateFamilyToMass

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

/-- Template-family occurrence totals imply the R312 c=3 mass formula. -/
theorem c3TemplateFamilyMass_eq
    (n largeOcc middleOcc smallOcc : ℤ)
    (hLarge : largeOcc = n)
    (hMiddle : middleOcc = 2 * n)
    (hSmall : smallOcc = n * (n - 7)) :
    largeOcc * delta3 (3 * n - 3) 3 1 + middleOcc * delta3 6 3 3
      + smallOcc * delta2 6 3 = 60 * n * n - 90 * n := by
  subst largeOcc
  subst middleOcc
  subst smallOcc
  rw [delta_large_signature, delta_middle_signature, delta_small_signature]
  ring

/-- The same template-family totals beat depth-3 exact-Wick headroom for `n >= 4`. -/
theorem depth3Headroom_lt_c3TemplateFamilyMass
    {n largeOcc middleOcc smallOcc : ℤ}
    (hn : 4 ≤ n)
    (hLarge : largeOcc = n)
    (hMiddle : middleOcc = 2 * n)
    (hSmall : smallOcc = n * (n - 7)) :
    45 * n * n - 40 * n
      < largeOcc * delta3 (3 * n - 3) 3 1 + middleOcc * delta3 6 3 3
        + smallOcc * delta2 6 3 := by
  subst largeOcc
  subst middleOcc
  subst smallOcc
  rw [delta_large_signature, delta_middle_signature, delta_small_signature]
  nlinarith

end ArkLib.ProximityGap.Frontier.R314C3TemplateFamilyToMass

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R314C3TemplateFamilyToMass.delta_large_signature
#print axioms ArkLib.ProximityGap.Frontier.R314C3TemplateFamilyToMass.delta_middle_signature
#print axioms ArkLib.ProximityGap.Frontier.R314C3TemplateFamilyToMass.delta_small_signature
#print axioms ArkLib.ProximityGap.Frontier.R314C3TemplateFamilyToMass.c3TemplateFamilyMass_eq
#print axioms ArkLib.ProximityGap.Frontier.R314C3TemplateFamilyToMass.depth3Headroom_lt_c3TemplateFamilyMass
