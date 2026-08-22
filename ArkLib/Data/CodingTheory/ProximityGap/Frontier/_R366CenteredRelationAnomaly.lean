/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R365CenteredShadowMassWeld

/-!
# R366: isolate the centered relation anomaly

For a random map into a field of size `q`, the expected weighted off-diagonal collision numerator
is `n^(2r) - shadowEnergy`.  The quantity that the deep wall must control is therefore

```text
q * shadowCollisionMass - (n^(2r) - shadowEnergy),
```

not the raw number or raw mass of kernel relations.  This file proves that the full DC-centered
numerator is exactly `(q-1) * shadowEnergy` plus this relation anomaly, and rewrites
`DCEnergyBound` as the corresponding anomaly budget.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.Frontier.R366CenteredRelationAnomaly

open ArkLib.ProximityGap.DCEnergyCorrection
open ArkLib.ProximityGap.Frontier.R308DepthUniformShadowFloor
open ArkLib.ProximityGap.Frontier.R310ShadowFloorToRFoldEnergy
open ArkLib.ProximityGap.Frontier.R312ShadowCollisionMassIdentity
open ArkLib.ProximityGap.Frontier.R365CenteredShadowMassWeld

/-- Weighted excess of realized relation mass above the uniform `1/q` collision baseline. -/
noncomputable def relationAnomaly
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (n m r : ℕ) : ℝ :=
  (Fintype.card F : ℝ) * (shadowCollisionMass g n m r : ℝ) -
    ((n : ℝ) ^ (2 * r) - (shadowEnergy n m r : ℝ))

/-- The exact floor/anomaly split of the DC-centered numerator. -/
theorem centeredShadowMass_eq_floor_add_relationAnomaly
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (n m r : ℕ) :
    centeredShadowMass g n m r =
      ((Fintype.card F : ℝ) - 1) * (shadowEnergy n m r : ℝ) +
        relationAnomaly g n m r := by
  unfold centeredShadowMass relationAnomaly
  ring

/-- **Exact deep-wall target.** `DCEnergyBound` is equivalent to saying that the centered
relation anomaly fits in the Wick budget left after paying the characteristic-zero floor. -/
theorem dcEnergyBound_iff_relationAnomaly_le
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (n m r : ℕ) (hg0 : g ≠ 0) (hord : orderOf g = n)
    (hm : 0 < m) (hn : n = 2 * m) (hg : g ^ m = -1) :
    DCEnergyBound (powerRootSet g n) r ↔
      relationAnomaly g n m r ≤
        (Fintype.card F : ℝ) *
            ((Nat.doubleFactorial (2 * r - 1) : ℝ) *
              ((powerRootSet g n).card : ℝ) ^ r) -
          ((Fintype.card F : ℝ) - 1) * (shadowEnergy n m r : ℝ) := by
  rw [dcEnergyBound_iff_centeredShadowMass_le g n m r hg0 hord hm hn hg,
    centeredShadowMass_eq_floor_add_relationAnomaly]
  constructor <;> intro h <;> linarith

end ArkLib.ProximityGap.Frontier.R366CenteredRelationAnomaly

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R366CenteredRelationAnomaly.centeredShadowMass_eq_floor_add_relationAnomaly
#print axioms
  ArkLib.ProximityGap.Frontier.R366CenteredRelationAnomaly.dcEnergyBound_iff_relationAnomaly_le
