/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R362KernelShellWickWeld
import ArkLib.Data.CodingTheory.ProximityGap.DCEnergyCorrection

/-!
# R365: the centered shadow mass is exactly the deep-wall numerator

The raw shell census of R362 is useful only before the DC crossover.  This file records the
correct deep object.  The characteristic-zero shadow energy plus all realized relation mass is
the finite-field energy; subtracting the uniform term after multiplying by the field size gives
exactly `DCEnergyBound`'s numerator.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.Frontier.R365CenteredShadowMassWeld

open ArkLib.ProximityGap.DCEnergyCorrection
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.Frontier.R306Depth3CharZeroFloor
open ArkLib.ProximityGap.Frontier.R308DepthUniformShadowFloor
open ArkLib.ProximityGap.Frontier.R310ShadowFloorToRFoldEnergy
open ArkLib.ProximityGap.Frontier.R312ShadowCollisionMassIdentity
open ArkLib.ProximityGap.Frontier.R314KernelRelationMassDecomposition
open ArkLib.ProximityGap.Frontier.R324KernelRelationLengthStratification

/-- The DC-centered shadow collision expression, in the real normalization used by the prize. -/
noncomputable def centeredShadowMass
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (n m r : ℕ) : ℝ :=
  (Fintype.card F : ℝ) *
      ((shadowEnergy n m r : ℝ) + (shadowCollisionMass g n m r : ℝ)) -
    (n : ℝ) ^ (2 * r)

/-- Exact identification with the field-level DC-subtracted energy numerator. -/
theorem centeredShadowMass_eq_dcNumerator
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (n m r : ℕ) (hg0 : g ≠ 0) (hord : orderOf g = n)
    (hm : 0 < m) (hn : n = 2 * m) (hg : g ^ m = -1) :
    centeredShadowMass g n m r =
      (Fintype.card F : ℝ) * (rEnergy (powerRootSet g n) r : ℝ) -
        ((powerRootSet g n).card : ℝ) ^ (2 * r) := by
  have henergy := rEnergy_powerRootSet_eq_shadowEnergy_add_collisionMass_of_orderOf
    g n m r hg0 hord hm hn hg
  have hcard : (powerRootSet g n).card = n := by
    classical
    unfold powerRootSet
    rw [Finset.card_image_of_injective _
      (power_index_injective_of_orderOf g n hg0 hord), Finset.card_univ, Fintype.card_fin]
  unfold centeredShadowMass
  rw [henergy, hcard]
  rw [Nat.cast_add]

/-- The deep prize hypothesis is exactly a centered shadow-mass bound. -/
theorem dcEnergyBound_iff_centeredShadowMass_le
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (n m r : ℕ) (hg0 : g ≠ 0) (hord : orderOf g = n)
    (hm : 0 < m) (hn : n = 2 * m) (hg : g ^ m = -1) :
    DCEnergyBound (powerRootSet g n) r ↔
      centeredShadowMass g n m r ≤
        (Fintype.card F : ℝ) *
          ((Nat.doubleFactorial (2 * r - 1) : ℝ) *
            ((powerRootSet g n).card : ℝ) ^ r) := by
  unfold DCEnergyBound
  rw [centeredShadowMass_eq_dcNumerator g n m r hg0 hord hm hn hg]

end ArkLib.ProximityGap.Frontier.R365CenteredShadowMassWeld

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R365CenteredShadowMassWeld.centeredShadowMass_eq_dcNumerator
#print axioms
  ArkLib.ProximityGap.Frontier.R365CenteredShadowMassWeld.dcEnergyBound_iff_centeredShadowMass_le
