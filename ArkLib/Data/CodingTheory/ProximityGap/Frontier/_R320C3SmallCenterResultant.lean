/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FS3AnnihilatorHeightBound
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FS4Depth3PatternDecomposition

/-!
# R320 (#466): every nontrivial small-center collision owns a bounded resultant

R319 reduces equality of two raw small-fiber centers to

```text
ζ^a - ζ^b - 2ζ^c + 2ζ^d = 0.
```

This is a depth-3 pattern after duplicating the coefficient-two terms:

```text
ζ^a + ζ^d + ζ^d = ζ^b + ζ^c + ζ^c.
```

This file packages that observation through FS3.  Therefore every collision
whose reduced integer pattern is nonzero has a nonzero cyclotomic resultant of
explicit dyadic height, and every characteristic realizing that collision
divides the resultant.  The missing nonzero-pattern and global counting inputs
remain explicit; no center-injectivity claim is made here.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace ArkLib.ProximityGap.Frontier.R320C3SmallCenterResultant

open ArkLib.ProximityGap.Frontier.FS3AnnihilatorHeightBound
open ArkLib.ProximityGap.Frontier.FS4Depth3PatternDecomposition

/-- The six-slot depth-3 pattern encoding a four-term small-center collision. -/
noncomputable def c3SmallCenterPattern (m leftOffset rightOffset leftComplement rightComplement : ℕ) :
    ℤ[X] :=
  patternPoly m leftOffset rightComplement rightComplement rightOffset leftComplement leftComplement

/-- The four-term collision pattern has degree below the dyadic half-basis bound. -/
theorem c3SmallCenterPattern_natDegree_lt
    {m leftOffset rightOffset leftComplement rightComplement : ℕ} (hm : 0 < m)
    (hleftOffset : leftOffset < 2 * m) (hrightOffset : rightOffset < 2 * m)
    (hleftComplement : leftComplement < 2 * m) (hrightComplement : rightComplement < 2 * m) :
    (c3SmallCenterPattern m leftOffset rightOffset leftComplement rightComplement).natDegree < m := by
  unfold c3SmallCenterPattern
  exact patternPoly_natDegree_lt hm hleftOffset hrightComplement hrightComplement hrightOffset
    hleftComplement hleftComplement

/-- Its reduced coefficients have absolute value at most `8`. -/
theorem c3SmallCenterPattern_coeff_abs_le
    (m leftOffset rightOffset leftComplement rightComplement coefficientIndex : ℕ) :
    |(c3SmallCenterPattern m leftOffset rightOffset leftComplement rightComplement).coeff coefficientIndex|
      ≤ 2 ^ 3 := by
  unfold c3SmallCenterPattern
  exact patternPoly_coeff_abs_le m leftOffset rightComplement rightComplement rightOffset
    leftComplement leftComplement coefficientIndex

/-- Evaluation of the six-slot pattern is exactly the four-term center-collision relation. -/
theorem aeval_c3SmallCenterPattern_iff
    {F : Type*} [Field F] {ζ : F} {m leftOffset rightOffset leftComplement rightComplement : ℕ}
    (hhalfTurn : ζ ^ m = -1)
    (hleftOffset : leftOffset < 2 * m) (hrightOffset : rightOffset < 2 * m)
    (hleftComplement : leftComplement < 2 * m) (hrightComplement : rightComplement < 2 * m) :
    aeval ζ (c3SmallCenterPattern m leftOffset rightOffset leftComplement rightComplement) = 0
      ↔ ζ ^ leftOffset - ζ ^ rightOffset - (2 : F) * ζ ^ leftComplement
          + (2 : F) * ζ ^ rightComplement = 0 := by
  unfold c3SmallCenterPattern
  rw [← sum_eq_iff_aeval_patternPoly hhalfTurn hleftOffset hrightComplement
    hrightComplement hrightOffset hleftComplement hleftComplement]
  constructor <;> intro hrelation <;> linear_combination hrelation

/-- Every nonzero reduced small-center collision pattern has a bounded natural
annihilator divisible by every characteristic in which the four-term collision occurs. -/
theorem c3SmallCenterPattern_annihilator_exists_with_height
    {k leftOffset rightOffset leftComplement rightComplement : ℕ}
    (hpattern :
      c3SmallCenterPattern (2 ^ k) leftOffset rightOffset leftComplement rightComplement ≠ 0)
    (hleftOffset : leftOffset < 2 * 2 ^ k) (hrightOffset : rightOffset < 2 * 2 ^ k)
    (hleftComplement : leftComplement < 2 * 2 ^ k)
    (hrightComplement : rightComplement < 2 * 2 ^ k) :
    ∃ N : ℕ, N ≠ 0 ∧ N ≤ 2 ^ ((k + 1 + 3) * 2 ^ (k + 1)) ∧
      ∀ (F : Type) (_ : Field F) (prime : ℕ) (_ : CharP F prime) (ζ : F),
        ζ ^ (2 ^ k) = -1 →
          ζ ^ leftOffset - ζ ^ rightOffset - (2 : F) * ζ ^ leftComplement
              + (2 : F) * ζ ^ rightComplement = 0 → prime ∣ N := by
  obtain ⟨N, hN, hheight, hdivides⟩ := pattern_annihilator_exists_with_height
    (k := k) (b := 3) hpattern
      (c3SmallCenterPattern_natDegree_lt (by positivity) hleftOffset hrightOffset
        hleftComplement hrightComplement)
      (fun coefficientIndex => c3SmallCenterPattern_coeff_abs_le (2 ^ k) leftOffset rightOffset
        leftComplement rightComplement coefficientIndex)
  refine ⟨N, hN, hheight, ?_⟩
  intro F _ prime _ ζ hhalfTurn hcollision
  apply hdivides F inferInstance prime inferInstance ζ hhalfTurn
  exact (aeval_c3SmallCenterPattern_iff hhalfTurn hleftOffset hrightOffset
    hleftComplement hrightComplement).mpr hcollision

end ArkLib.ProximityGap.Frontier.R320C3SmallCenterResultant

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R320C3SmallCenterResultant.c3SmallCenterPattern_natDegree_lt
#print axioms ArkLib.ProximityGap.Frontier.R320C3SmallCenterResultant.aeval_c3SmallCenterPattern_iff
#print axioms
  ArkLib.ProximityGap.Frontier.R320C3SmallCenterResultant.c3SmallCenterPattern_annihilator_exists_with_height
