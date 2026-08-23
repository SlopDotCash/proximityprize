/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R114DemandFloorClosedPrefixGeneralBudget

/-!
# Tail reduction for the general-r demand budget

R114 packages the checked r=3,4,5 prefix in the workbench's `deepBandBudgetR` coordinates.
This file turns that into a small reducer for future uniform bad-count families: if a candidate
general-r counter agrees with the already-formalized counts at r=3,4,5, then only the tail
`r ≥ 6` remains.

This is deliberately an interface theorem, not a closure claim for the prize.  The tail hypothesis
is exactly where the still-open general-r combinatorics must enter.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R115DemandFloorTailReduction

open ArkLib.ProximityGap.Frontier.R109DemandFloorGeneralBudgetBridge
open ArkLib.ProximityGap.Frontier.R114DemandFloorClosedPrefixGeneralBudget

/-- A uniform bad-count family has the checked closed prefix when it agrees with the existing
r=3,4,5 formalizations in the `n = 4g` coordinate. -/
def AgreesWithClosedDemandPrefix (Bad : ℕ → ℕ → ℕ) (g : ℕ) : Prop :=
  Bad 3 (4 * g) = ArkLib.ProximityGap.DeepBandR3.deepBandBadCount g ∧
    Bad 4 (4 * g) = ArkLib.ProximityGap.DeepBandR4.deepBandBadCount4 g ∧
      Bad 5 (4 * g) = ArkLib.ProximityGap.DeepBandR5.deepBandBadCount5 g

/-- Once a family agrees with the closed prefix, a proof of the `r ≥ 6` tail gives every
`r ≥ 3` rung at the same `n = 4g`. -/
theorem demand_floor_all_r_ge_three_of_closed_prefix_and_tail
    (Bad : ℕ → ℕ → ℕ) (g r : ℕ)
    (hg : 3 ≤ g)
    (hprefix : AgreesWithClosedDemandPrefix Bad g)
    (htail : ∀ s : ℕ, 6 ≤ s → Bad s (4 * g) ≤ deepBandBudgetR s (4 * g))
    (hr : 3 ≤ r) :
    Bad r (4 * g) ≤ deepBandBudgetR r (4 * g) := by
  rcases hprefix with ⟨h3, h4, h5⟩
  have hclosed := closed_prefix_r3_r4_r5_deepBandBudgetR g hg
  rcases hclosed with ⟨hr3, hr4, hr5⟩
  rcases lt_or_ge r 6 with hlt | hge
  · interval_cases r <;> simpa [h3, h4, h5]
  · exact htail r hge

/-- The same reducer for positive rungs only: if `r = 0,1,2` are excluded explicitly, then
the prefix/tail split covers all remaining r. -/
theorem demand_floor_positive_rung_of_closed_prefix_and_tail
    (Bad : ℕ → ℕ → ℕ) (g r : ℕ)
    (hg : 3 ≤ g)
    (hr0 : r ≠ 0)
    (hr1 : r ≠ 1)
    (hr2 : r ≠ 2)
    (hprefix : AgreesWithClosedDemandPrefix Bad g)
    (htail : ∀ s : ℕ, 6 ≤ s → Bad s (4 * g) ≤ deepBandBudgetR s (4 * g)) :
    Bad r (4 * g) ≤ deepBandBudgetR r (4 * g) := by
  have hr : 3 ≤ r := by omega
  exact demand_floor_all_r_ge_three_of_closed_prefix_and_tail Bad g r hg hprefix htail hr

end ArkLib.ProximityGap.Frontier.R115DemandFloorTailReduction

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R115DemandFloorTailReduction.AgreesWithClosedDemandPrefix
#print axioms
  ArkLib.ProximityGap.Frontier.R115DemandFloorTailReduction.demand_floor_all_r_ge_three_of_closed_prefix_and_tail
#print axioms
  ArkLib.ProximityGap.Frontier.R115DemandFloorTailReduction.demand_floor_positive_rung_of_closed_prefix_and_tail
