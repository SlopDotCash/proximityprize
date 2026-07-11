/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G134ProductionCrossoverPin

/-!
# G135: census family ⟹ per-frequency sup bound — the end-to-end weld

Composes the G133 census tower with the in-tree per-frequency consumer
`eta_pow_le_of_dcEnergyBound`: under the disjoint-census family (rungs `11..110`) and the
low-rung anchors (`t ≤ 10`), every nontrivial Gauss-period frequency of the production
subgroup obeys the rung-`110` moment bound

```text
‖η_b‖^220 ≤ q · (219!! · n^110)      (b ≠ 0).
```

This is the #507-shaped end-to-end statement on this face: from the wall-hypothesis family
(census + anchors — finite, per-prime, counting-flavored) to the analytic sup-norm control
that the prize threshold chain consumes, with every intermediate step axiom-clean.
Numerically the rung-110 bound gives `M ≤ 2^19.7` versus the trivial `M ≤ n = 2^30`; the
in-tree moment-order optimization can then tune the rung.

**Honest scope.**  Conditional composition; the census family and anchors are the wall.
CORE remains OPEN.  Issue #466/#507.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G135CensusToSupBound

open Finset
open ArkLib.ProximityGap.Frontier.G95CardinalityDeepCapNoGo
open ArkLib.ProximityGap.Frontier.G133CensusTower
open ArkLib.ProximityGap.DCEnergyCorrection
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Census family ⟹ per-frequency sup bound at rung 110.**  Under the disjoint-census
family and the low-rung anchors, every nontrivial frequency obeys the rung-110 moment
bound. -/
theorem eta_pow_le_of_census_family
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (hcard : G.card = 2 ^ 30)
    (hq : Fintype.card F ≤ 2 ^ 160)
    (hanchor : ∀ s, s ≤ 10 → DCShape F G s)
    (hcensus : ∀ t, 11 ≤ t → t ≤ 110 →
      2 * (Fintype.card F * depthFiber G t t)
        ≤ 2 * (Fintype.card F *
            (Nat.doubleFactorial (2 * t - 1) * (2 ^ 30) ^ t))
          + (2 ^ 30) ^ (2 * t)) :
    ∀ b : F, b ≠ 0 →
      ‖eta ψ G b‖ ^ (2 * 110)
        ≤ (Fintype.card F : ℝ) *
            ((Nat.doubleFactorial (2 * 110 - 1) : ℝ) * (G.card : ℝ) ^ 110) := by
  intro b hb
  have hdc : DCEnergyBound G 110 :=
    dcEnergyBound_of_census_family G hcard hq hanchor hcensus 110
      (by norm_num) (by norm_num)
  exact eta_pow_le_of_dcEnergyBound hψ hdc hb

end ArkLib.ProximityGap.Frontier.G135CensusToSupBound

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G135CensusToSupBound.eta_pow_le_of_census_family
