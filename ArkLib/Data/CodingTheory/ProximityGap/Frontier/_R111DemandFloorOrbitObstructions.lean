/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R110DemandFloorClosedRungBudgetConsumers

/-!
# Obstructions to the demand-side orbit certificates

R109/R110 package the positive direction: an orbit-count bound plus the honest zero-orbit identity
implies the workbench deep-band budget.  This file records the matching audit-facing
contrapositives: if a computed bad-scalar count exceeds the relevant budget, then those orbit
certificate hypotheses could not have simultaneously held.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R111DemandFloorOrbitObstructions

open ArkLib.ProximityGap.Frontier.R109DemandFloorGeneralBudgetBridge
open ArkLib.ProximityGap.Frontier.R110DemandFloorClosedRungBudgetConsumers

/-- General workbench-coordinate obstruction: a count above `deepBandBudgetR r n` rules out the
orbit-count certificate plus honest zero-orbit identity. -/
theorem not_general_orbit_certificate_of_budget_lt_bad
    (r n OP bad : ℕ)
    (hn : 2 ∣ n)
    (hr : 4 ≤ r)
    (hm : 2 * r ≤ n / 2)
    (hgt : deepBandBudgetR r n < bad) :
    ¬ (OP ≤ (n / 2).choose (r - 1) ∧ bad ≤ n * OP + 1) := by
  rintro ⟨hOP, hbad⟩
  exact (Nat.not_le.mpr hgt)
    (demand_floor_general_budget_of_orbit_bound_plus_one r n OP bad hn hr hm hOP hbad)

/-- r=4 named-budget obstruction. -/
theorem not_r4_orbit_certificate_of_budget_lt_bad
    (g OP bad : ℕ)
    (hg : 4 ≤ g)
    (hgt : ArkLib.ProximityGap.DeepBandR4.deepBandBudget4 g < bad) :
    ¬ (OP ≤ (2 * g).choose 3 ∧ bad ≤ (4 * g) * OP + 1) := by
  rintro ⟨hOP, hbad⟩
  exact (Nat.not_le.mpr hgt)
    (demand_floor_r4_budget_of_orbit_bound_plus_one g OP bad hg hOP hbad)

/-- r=5 named-budget obstruction. -/
theorem not_r5_orbit_certificate_of_budget_lt_bad
    (g OP bad : ℕ)
    (hg : 5 ≤ g)
    (hgt : ArkLib.ProximityGap.DeepBandR5.deepBandBudget5 g < bad) :
    ¬ (OP ≤ (2 * g).choose 4 ∧ bad ≤ (4 * g) * OP + 1) := by
  rintro ⟨hOP, hbad⟩
  exact (Nat.not_le.mpr hgt)
    (demand_floor_r5_budget_of_orbit_bound_plus_one g OP bad hg hOP hbad)

end ArkLib.ProximityGap.Frontier.R111DemandFloorOrbitObstructions

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R111DemandFloorOrbitObstructions.not_general_orbit_certificate_of_budget_lt_bad
#print axioms
  ArkLib.ProximityGap.Frontier.R111DemandFloorOrbitObstructions.not_r4_orbit_certificate_of_budget_lt_bad
#print axioms
  ArkLib.ProximityGap.Frontier.R111DemandFloorOrbitObstructions.not_r5_orbit_certificate_of_budget_lt_bad
