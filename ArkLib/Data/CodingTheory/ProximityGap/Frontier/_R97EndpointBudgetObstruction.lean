/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R96IterConvEndpointBudgetConsumers

/-!
# LANE B2 (#466 round 97): endpoint-budget obstruction

R95/R96 make the Cauchy successor-recursion route convenient to consume, but they also expose its
main limitation.  If the propagation starts at depth `r`, the endpoint budget

`(m : ℝ) ≤ C * (r+1)`

already forces `C ≥ m/(r+1)`.  Thus a bounded public Wick constant cannot use this bare recursion
once `m` is large compared with `r`.  This file records that obstruction uniformly in `r`, so
future prize-facing attempts do not accidentally hide the linear-in-`m` cost inside the endpoint
consumer.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R97EndpointBudgetObstruction

variable {m : ℕ} [NeZero m]

/-- Any endpoint budget at start depth `r` forces the internal Wick constant to be at least
`m/(r+1)`. -/
theorem le_const_of_endpoint_budget {r : ℕ} {C : ℝ}
    (hbudget : (m : ℝ) ≤ C * ((r + 1 : ℕ) : ℝ)) :
    (m : ℝ) / ((r + 1 : ℕ) : ℝ) ≤ C := by
  have hpos : 0 < ((r + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_pos r
  rwa [div_le_iff₀ hpos]

/-- A public upper bound `C ≤ K` cannot pay the endpoint budget when `K*(r+1) < m`. -/
theorem not_endpoint_budget_of_const_lt {r : ℕ} {C K : ℝ}
    (hCK : C ≤ K)
    (hK : K * ((r + 1 : ℕ) : ℝ) < (m : ℝ)) :
    ¬ (m : ℝ) ≤ C * ((r + 1 : ℕ) : ℝ) := by
  intro hbudget
  nlinarith

/-- The r = 2 obstruction used by the lag-correlation endpoint consumers, recovered from the
uniform form. -/
theorem le_const_of_two_endpoint_budget {C : ℝ}
    (hbudget₂ : (m : ℝ) ≤ C * 3) :
    (m : ℝ) / 3 ≤ C := by
  simpa using
    (le_const_of_endpoint_budget (m := m) (r := 2) (C := C) (by simpa using hbudget₂))

/-- A bounded public constant below `m/3` cannot satisfy the r = 2 endpoint budget. -/
theorem not_two_endpoint_budget_of_const_lt {C K : ℝ}
    (hCK : C ≤ K) (hK : K * 3 < (m : ℝ)) :
    ¬ (m : ℝ) ≤ C * 3 := by
  simpa using
    (not_endpoint_budget_of_const_lt (m := m) (r := 2) (C := C) (K := K)
      hCK (by simpa using hK))

/-- The r = 3 obstruction used by the Jacobi-head consumers, recovered from the uniform form. -/
theorem le_const_of_three_endpoint_budget {C : ℝ}
    (hbudget₃ : (m : ℝ) ≤ C * 4) :
    (m : ℝ) / 4 ≤ C := by
  simpa using
    (le_const_of_endpoint_budget (m := m) (r := 3) (C := C) (by simpa using hbudget₃))

/-- A bounded public constant below `m/4` cannot satisfy the r = 3 endpoint budget. -/
theorem not_three_endpoint_budget_of_const_lt {C K : ℝ}
    (hCK : C ≤ K) (hK : K * 4 < (m : ℝ)) :
    ¬ (m : ℝ) ≤ C * 4 := by
  simpa using
    (not_endpoint_budget_of_const_lt (m := m) (r := 3) (C := C) (K := K)
      hCK (by simpa using hK))

end ArkLib.ProximityGap.Frontier.R97EndpointBudgetObstruction

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R97EndpointBudgetObstruction.le_const_of_endpoint_budget
#print axioms
  ArkLib.ProximityGap.Frontier.R97EndpointBudgetObstruction.not_endpoint_budget_of_const_lt
#print axioms
  ArkLib.ProximityGap.Frontier.R97EndpointBudgetObstruction.le_const_of_two_endpoint_budget
#print axioms
  ArkLib.ProximityGap.Frontier.R97EndpointBudgetObstruction.not_two_endpoint_budget_of_const_lt
#print axioms
  ArkLib.ProximityGap.Frontier.R97EndpointBudgetObstruction.le_const_of_three_endpoint_budget
#print axioms
  ArkLib.ProximityGap.Frontier.R97EndpointBudgetObstruction.not_three_endpoint_budget_of_const_lt
