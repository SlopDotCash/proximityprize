/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R108DemandFloorPlusOneBridge

/-!
# Demand-side bridge in the workbench's `(r,n)` budget coordinates

The workbench states the general deep-band budget as

`deepBandBudget_r r n = 2^r * C(n/2, r)`.

R108 proves the strengthened orbit bridge in the half-domain coordinate `m = n/2`.  This file
packages the same theorem directly in `(r,n)` form, including the zero-orbit `+1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R109DemandFloorGeneralBudgetBridge

open ArkLib.ProximityGap.Frontier.R108DemandFloorPlusOneBridge

/-- The general-r deep-band budget `K(r,n) = 2^r * C(n/2,r)`, matching the workbench notation. -/
def deepBandBudgetR (r n : ℕ) : ℕ := 2 ^ r * (n / 2).choose r

/-- The general budget in the `g = n/4` coordinate used by the r=4/r=5 closed-rung files. -/
theorem deepBandBudgetR_four_mul (r g : ℕ) :
    deepBandBudgetR r (4 * g) = 2 ^ r * (2 * g).choose r := by
  unfold deepBandBudgetR
  have hdiv : 4 * g / 2 = 2 * g := by omega
  rw [hdiv]

/-- Workbench-coordinate strengthened bridge.  If `n` is even, the actual count is bounded by
the honest orbit identity `bad ≤ n*OP + 1`, and the orbit count satisfies
`OP ≤ C(n/2,r-1)`, then the full general-r budget follows. -/
theorem demand_floor_general_budget_of_orbit_bound_plus_one
    (r n OP bad : ℕ)
    (hn : 2 ∣ n)
    (hr : 4 ≤ r)
    (hm : 2 * r ≤ n / 2)
    (hOP : OP ≤ (n / 2).choose (r - 1))
    (hbad : bad ≤ n * OP + 1) :
    bad ≤ deepBandBudgetR r n := by
  rcases hn with ⟨m, rfl⟩
  unfold deepBandBudgetR at *
  have hdiv : 2 * m / 2 = m := by omega
  rw [hdiv] at hm hOP ⊢
  have hbad' : bad ≤ 2 * m * OP + 1 := by
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hbad
  exact demand_floor_count_of_orbit_bound_plus_one m r OP bad hr hm hOP hbad'

/-- Workbench-coordinate bridge without the possible zero orbit. -/
theorem demand_floor_general_budget_of_orbit_bound
    (r n OP bad : ℕ)
    (hn : 2 ∣ n)
    (hr : 4 ≤ r)
    (hm : 2 * r ≤ n / 2)
    (hOP : OP ≤ (n / 2).choose (r - 1))
    (hbad : bad ≤ n * OP) :
    bad ≤ deepBandBudgetR r n :=
  demand_floor_general_budget_of_orbit_bound_plus_one r n OP bad hn hr hm hOP (by omega)

/-- Same bridge for the closed-rung `n = 4g` coordinate. -/
theorem demand_floor_four_mul_budget_of_orbit_bound_plus_one
    (r g OP bad : ℕ)
    (hr : 4 ≤ r)
    (hm : 2 * r ≤ 2 * g)
    (hOP : OP ≤ (2 * g).choose (r - 1))
    (hbad : bad ≤ (4 * g) * OP + 1) :
    bad ≤ deepBandBudgetR r (4 * g) := by
  rw [deepBandBudgetR_four_mul]
  have hbad' : bad ≤ 2 * (2 * g) * OP + 1 := by
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hbad
  exact demand_floor_count_of_orbit_bound_plus_one (2 * g) r OP bad hr hm hOP hbad'

/-- Same bridge for the closed-rung `n = 4g` coordinate, without the possible zero orbit. -/
theorem demand_floor_four_mul_budget_of_orbit_bound
    (r g OP bad : ℕ)
    (hr : 4 ≤ r)
    (hm : 2 * r ≤ 2 * g)
    (hOP : OP ≤ (2 * g).choose (r - 1))
    (hbad : bad ≤ (4 * g) * OP) :
    bad ≤ deepBandBudgetR r (4 * g) :=
  demand_floor_four_mul_budget_of_orbit_bound_plus_one r g OP bad hr hm hOP (by omega)

end ArkLib.ProximityGap.Frontier.R109DemandFloorGeneralBudgetBridge

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R109DemandFloorGeneralBudgetBridge.deepBandBudgetR_four_mul
#print axioms
  ArkLib.ProximityGap.Frontier.R109DemandFloorGeneralBudgetBridge.demand_floor_general_budget_of_orbit_bound_plus_one
#print axioms
  ArkLib.ProximityGap.Frontier.R109DemandFloorGeneralBudgetBridge.demand_floor_general_budget_of_orbit_bound
#print axioms
  ArkLib.ProximityGap.Frontier.R109DemandFloorGeneralBudgetBridge.demand_floor_four_mul_budget_of_orbit_bound_plus_one
#print axioms
  ArkLib.ProximityGap.Frontier.R109DemandFloorGeneralBudgetBridge.demand_floor_four_mul_budget_of_orbit_bound
