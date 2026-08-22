/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R312ShadowCollisionMassIdentity
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._WallCapstone

/-!
# LANE B2 (#466 round 317): the exact deep shadow-collision residual

R312 gives, for an exact-order antipodal power-root set,

```text
rEnergy = shadowEnergy + shadowCollisionMass.
```

The prize wall is DC-subtracted, so the collision term is not required to fit the full Wick
budget by itself.  The characteristic-zero shadow has already consumed part of that budget, while
the DC term `n^(2r)` gives headroom back.  The exact remaining one-rung obligation is therefore

```text
q * shadowCollisionMass
  <= q * ((2r-1)!! * n^r) + n^(2r) - q * shadowEnergy.
```

This file names that obligation and proves that it is *equivalent* to the existing
`DCEnergyBound` on the concrete power-root set.  Quantifying it over every `r` is likewise
equivalent to the existing `WallCapstone.WallHolds`; it is not asserted here.  Thus the new
`DeepShadowCollisionResidual` is an honest re-expression of the open deep arithmetic input, with
neither a dummy conclusion nor an extra loss.

Issue #466, round 317, LANE B2.  Axiom-clean
(`propext`, `Classical.choice`, `Quot.sound`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R317DeepShadowCollisionHeadroom

open ArkLib.ProximityGap.DCEnergyCorrection
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance
open ArkLib.ProximityGap.Frontier.R306Depth3CharZeroFloor
open ArkLib.ProximityGap.Frontier.R308DepthUniformShadowFloor
open ArkLib.ProximityGap.Frontier.R310ShadowFloorToRFoldEnergy
open ArkLib.ProximityGap.Frontier.R312ShadowCollisionMassIdentity
open ArkLib.ProximityGap.Frontier.WallCapstone

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- An injective indexing by the first `n` powers makes the concrete power-root set have exactly
`n` elements. -/
theorem card_powerRootSet_of_injective (g : F) (n : ℕ)
    (hinj : Function.Injective (fun i : Fin n => (g ^ (i : ℕ) : F))) :
    (powerRootSet g n).card = n := by
  classical
  unfold powerRootSet
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

/-- Exact-order specialization of `card_powerRootSet_of_injective`. -/
theorem card_powerRootSet_of_orderOf (g : F) (n : ℕ) (hg0 : g ≠ 0)
    (hord : orderOf g = n) :
    (powerRootSet g n).card = n :=
  card_powerRootSet_of_injective g n
    (power_index_injective_of_orderOf g n hg0 hord)

/-- **The exact DC-corrected collision headroom at rung `r`.**

The Wick allowance is augmented by the DC term `n^(2r)` and depleted by the already-present
characteristic-zero shadow energy.  All quantities are kept in the cleared-denominator form used
by `DCEnergyBound`. -/
def DCShadowCollisionHeadroomAt (g : F) (n m r : ℕ) : Prop :=
  (Fintype.card F : ℝ) * (shadowCollisionMass g n m r : ℝ)
    ≤ (Fintype.card F : ℝ)
          * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (n : ℝ) ^ r)
        + (n : ℝ) ^ (2 * r)
        - (Fintype.card F : ℝ) * (shadowEnergy n m r : ℝ)

/-- **One-rung exact reduction.**  For an exact-order antipodal power-root set, the existing
DC-subtracted Wick bound is equivalent, with no slack, to the R317 collision-headroom bound. -/
theorem dcEnergyBound_powerRootSet_iff_dcShadowCollisionHeadroomAt
    (g : F) (n m r : ℕ) (hg0 : g ≠ 0) (hord : orderOf g = n)
    (hm : 0 < m) (hn : n = 2 * m) (hg : g ^ m = -1) :
    DCEnergyBound (powerRootSet g n) r ↔ DCShadowCollisionHeadroomAt g n m r := by
  have henergyNat :=
    rEnergy_powerRootSet_eq_shadowEnergy_add_collisionMass_of_orderOf
      g n m r hg0 hord hm hn hg
  have henergy :
      (rEnergy (powerRootSet g n) r : ℝ) =
        (shadowEnergy n m r : ℝ) + (shadowCollisionMass g n m r : ℝ) := by
    exact_mod_cast henergyNat
  have hcard := card_powerRootSet_of_orderOf g n hg0 hord
  unfold DCEnergyBound DCShadowCollisionHeadroomAt
  rw [henergy, hcard]
  constructor <;> intro h <;> linarith

/-- **The deep shadow-collision residual.**  This is the exact all-rung arithmetic obligation
left after the R312 characteristic-zero-shadow decomposition.  No theorem in this file asserts
that it holds. -/
def DeepShadowCollisionResidual (g : F) (n m : ℕ) : Prop :=
  ∀ r : ℕ, DCShadowCollisionHeadroomAt g n m r

/-- **All-rung exact reduction to the existing wall.**  On an exact-order antipodal power-root
set, R317's deep residual is equivalent to `WallCapstone.WallHolds`, not merely sufficient for a
new surrogate wall. -/
theorem wallHolds_powerRootSet_iff_deepShadowCollisionResidual
    (g : F) (n m : ℕ) (hg0 : g ≠ 0) (hord : orderOf g = n)
    (hm : 0 < m) (hn : n = 2 * m) (hg : g ^ m = -1) :
    WallHolds (powerRootSet g n) ↔ DeepShadowCollisionResidual g n m := by
  unfold WallHolds DeepShadowCollisionResidual
  constructor
  · intro hwall r
    exact (dcEnergyBound_powerRootSet_iff_dcShadowCollisionHeadroomAt
      g n m r hg0 hord hm hn hg).mp (hwall r)
  · intro hcollision r
    exact (dcEnergyBound_powerRootSet_iff_dcShadowCollisionHeadroomAt
      g n m r hg0 hord hm hn hg).mpr (hcollision r)

/-- Forward consumer form: proving the named deep collision residual discharges the project's
existing `WallHolds` hypothesis for the concrete power-root set. -/
theorem wallHolds_powerRootSet_of_deepShadowCollisionResidual
    (g : F) (n m : ℕ) (hg0 : g ≠ 0) (hord : orderOf g = n)
    (hm : 0 < m) (hn : n = 2 * m) (hg : g ^ m = -1)
    (hcollision : DeepShadowCollisionResidual g n m) :
    WallHolds (powerRootSet g n) :=
  (wallHolds_powerRootSet_iff_deepShadowCollisionResidual
    g n m hg0 hord hm hn hg).mpr hcollision

end ArkLib.ProximityGap.Frontier.R317DeepShadowCollisionHeadroom

/-! ## Axiom audit (must contain no `sorryAx`) -/
#print axioms
  ArkLib.ProximityGap.Frontier.R317DeepShadowCollisionHeadroom.card_powerRootSet_of_orderOf
#print axioms
  ArkLib.ProximityGap.Frontier.R317DeepShadowCollisionHeadroom.dcEnergyBound_powerRootSet_iff_dcShadowCollisionHeadroomAt
#print axioms
  ArkLib.ProximityGap.Frontier.R317DeepShadowCollisionHeadroom.wallHolds_powerRootSet_iff_deepShadowCollisionResidual
#print axioms
  ArkLib.ProximityGap.Frontier.R317DeepShadowCollisionHeadroom.wallHolds_powerRootSet_of_deepShadowCollisionResidual
