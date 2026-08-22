/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BGKDepthREnergyLaw
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumMoment
import ArkLib.Data.CodingTheory.ProximityGap.DCEnergyCorrection

/-!
# Bridge between the two ordered-energy representations used by the BGK and census lanes

The repository contains two extensionally equal definitions of ordered `r`-fold additive energy:

* `BGKDepthREnergyLaw.rEnergy`, as the cardinality of a filtered product;
* `SubgroupGaussSumMoment.rEnergy`, as a nested sum of equality indicators.

They are not definitionally equal.  This file supplies the missing unconditional bridge so a
residual proved in the G121--G145 census language can feed the BGK depth ladder without relying on
namespace resolution or a primitive-character detour.  Issue #466.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.Frontier.BGKRenergyRepresentationBridge

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The filtered-cardinality and nested-indicator representations count the same ordered
equal-sum tuple pairs. -/
theorem rEnergy_eq_standard (G : Finset F) (r : ℕ) :
    BGKDepthREnergyLaw.rEnergy G r =
      ArkLib.ProximityGap.SubgroupGaussSumMoment.rEnergy G r := by
  classical
  unfold BGKDepthREnergyLaw.rEnergy ArkLib.ProximityGap.SubgroupGaussSumMoment.rEnergy
  rw [Finset.card_filter, Finset.sum_product]

/-- The two lanes therefore have literally the same DC-subtracted real-valued energy. -/
theorem dcExcess_eq_standard (G : Finset F) (r : ℕ) :
    (Fintype.card F : ℝ) * (BGKDepthREnergyLaw.rEnergy G r : ℝ) -
        (G.card : ℝ) ^ (2 * r) =
      (Fintype.card F : ℝ) *
          (ArkLib.ProximityGap.SubgroupGaussSumMoment.rEnergy G r : ℝ) -
        (G.card : ℝ) ^ (2 * r) := by
  rw [rEnergy_eq_standard]

/-- The established standard `DCEnergyBound` at depth seven is stronger than the corrected BGK
coefficient-`2^18` residual: `13!! = 135135 < 2^18`.  This is the exact bridge by which the
G121--G145 census lane can feed the repaired BGK consumer. -/
theorem depthSeven_relaxed_of_dcEnergyBound (G : Finset F)
    (h : ArkLib.ProximityGap.DCEnergyCorrection.DCEnergyBound G 7) :
    (Fintype.card F : ℝ) * (BGKDepthREnergyLaw.rEnergy G 7 : ℝ) -
        (G.card : ℝ) ^ 14
      ≤ (Fintype.card F : ℝ) * ((2 : ℝ) ^ 18 * (G.card : ℝ) ^ 7) := by
  unfold ArkLib.ProximityGap.DCEnergyCorrection.DCEnergyBound at h
  rw [rEnergy_eq_standard]
  have hq : (0 : ℝ) ≤ (Fintype.card F : ℝ) := by positivity
  calc
    (Fintype.card F : ℝ) *
          (ArkLib.ProximityGap.SubgroupGaussSumMoment.rEnergy G 7 : ℝ) -
        (G.card : ℝ) ^ 14
        = (Fintype.card F : ℝ) *
            (ArkLib.ProximityGap.SubgroupGaussSumMoment.rEnergy G 7 : ℝ) -
          (G.card : ℝ) ^ (2 * 7) := by norm_num
    _ ≤ (Fintype.card F : ℝ) *
          ((Nat.doubleFactorial (2 * 7 - 1) : ℝ) * (G.card : ℝ) ^ 7) := h
    _ ≤ (Fintype.card F : ℝ) * ((2 : ℝ) ^ 18 * (G.card : ℝ) ^ 7) := by
      apply mul_le_mul_of_nonneg_left _ hq
      gcongr
      norm_num

end ArkLib.ProximityGap.Frontier.BGKRenergyRepresentationBridge

#print axioms
  ArkLib.ProximityGap.Frontier.BGKRenergyRepresentationBridge.rEnergy_eq_standard
#print axioms
  ArkLib.ProximityGap.Frontier.BGKRenergyRepresentationBridge.dcExcess_eq_standard
#print axioms
  ArkLib.ProximityGap.Frontier.BGKRenergyRepresentationBridge.depthSeven_relaxed_of_dcEnergyBound
