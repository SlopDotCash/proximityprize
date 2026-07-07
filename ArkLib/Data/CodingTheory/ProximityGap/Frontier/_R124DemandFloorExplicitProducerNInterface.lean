/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R122DemandFloorExplicitOrbitProducer
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R123DemandFloorDivFourInterface

/-!
# n-coordinate consumers for explicit demand-tail producers

R122 lowers the remaining demand-side theorem to an explicit orbit-count producer `OP g r`.
R123 exposes the final budget in divisibility-form `(r,n)` coordinates.  This file composes those
interfaces so a future explicit `OP` proof can be consumed directly by workbench-shaped goals.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R124DemandFloorExplicitProducerNInterface

open ArkLib.ProximityGap.Frontier.R109DemandFloorGeneralBudgetBridge
open ArkLib.ProximityGap.Frontier.R115DemandFloorTailReduction
open ArkLib.ProximityGap.Frontier.R121DemandFloorTailTheoremInterface
open ArkLib.ProximityGap.Frontier.R122DemandFloorExplicitOrbitProducer
open ArkLib.ProximityGap.Frontier.R123DemandFloorDivFourInterface

/-- Explicit orbit producer, consumed directly in divisibility-form `(r,n)` coordinates. -/
theorem demand_floor_of_dvd_four_explicit_orbit_producer
    (Bad : ℕ → ℕ → ℕ) (OP : ℕ → ℕ → ℕ)
    (hprefix : ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g)
    (hOP : ExplicitNaturalTailOrbitProducer Bad OP)
    (r n : ℕ)
    (hn : 4 ∣ n)
    (hg : 3 ≤ n / 4)
    (hr : 3 ≤ r)
    (hrg : r ≤ n / 4) :
    Bad r n ≤ deepBandBudgetR r n := by
  exact demand_floor_of_dvd_four_natural_demand_theorem Bad
    (natural_demand_theorem_of_explicit_orbit_producer Bad OP hprefix hOP)
    r n hn hg hr hrg

/-- Positive-rung divisibility-form consumer for an explicit orbit producer. -/
theorem demand_floor_positive_of_dvd_four_explicit_orbit_producer
    (Bad : ℕ → ℕ → ℕ) (OP : ℕ → ℕ → ℕ)
    (hprefix : ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g)
    (hOP : ExplicitNaturalTailOrbitProducer Bad OP)
    (r n : ℕ)
    (hn : 4 ∣ n)
    (hg : 3 ≤ n / 4)
    (hr0 : r ≠ 0)
    (hr1 : r ≠ 1)
    (hr2 : r ≠ 2)
    (hrg : r ≤ n / 4) :
    Bad r n ≤ deepBandBudgetR r n := by
  exact demand_floor_positive_of_dvd_four_natural_demand_theorem Bad
    (natural_demand_theorem_of_explicit_orbit_producer Bad OP hprefix hOP)
    r n hn hg hr0 hr1 hr2 hrg

end ArkLib.ProximityGap.Frontier.R124DemandFloorExplicitProducerNInterface

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R124DemandFloorExplicitProducerNInterface.demand_floor_of_dvd_four_explicit_orbit_producer
#print axioms
  ArkLib.ProximityGap.Frontier.R124DemandFloorExplicitProducerNInterface.demand_floor_positive_of_dvd_four_explicit_orbit_producer
