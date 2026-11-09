/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Lattice

/-!
# Bridge B03 — binding depth `m* ≥ 1` (target E1) (#444)

`δ*` is pinned (E1) by `δ* = 1 − ρ − (m*−1)/n`, where `m* = s − k` at binding is the
**binding depth**: the least over-determination depth `m` whose worst far-line over-determined
incidence `D*(m)` drops to budget `D*(m) ≤ budget`.

This bridge isolates the elementary structural fact the empirical cascade asserts at depth 0:

* SPEC B03 CLAIM: `m* ≥ 1`. At `s = k` (depth `m = 0`) the linear system is NOT
  over-determined — every direction `γ` agrees, so the far-line incidence `D*(0)` is the full
  count, which exceeds the budget. Hence the first depth that crosses the budget is `≥ 1`, i.e.
  the binding depth is positive.

We model the cascade as a budget-crossing predicate over depths `m : ℕ`. The binding depth is the
least `m` satisfying the budget. The only INPUT specific to the cascade is the *empirical* depth-0
over-budget fact `¬ budgetMet 0` (= E2: `D*(0) > budget`; e.g. `n=8`: `D*(0)` saturates at the
full 40, budget `≈ n`). Given that single fact (taken as an honest hypothesis, since the precise
value of `D*(0)` is the empirical cascade datum, not an abstract theorem), `m* ≥ 1` is forced.

This is the depth-0 anchor of the E1 master gap identity; it is axiom-clean and free of the heavy
MCA substrate (the budget-crossing it abstracts is exactly `OpenCoreConverse`'s
`WorstCaseIncidenceBounded` at the over-determination depth `m`).

## Honesty
The over-budget-at-depth-0 fact `¬ budgetMet 0` is an EXPLICIT hypothesis (the empirical E2 datum).
Everything else (`m* ≥ 1`, and that `m*` is genuinely the least budget-meeting depth) is proven
with no `sorry`, no `axiom`, no `native_decide`.

Issue #444.
-/

namespace ProximityGap.BridgeB03

/-- A cascade of budget-crossing predicates over over-determination depths `m : ℕ`.
`budgetMet m` says the worst far-line over-determined incidence `D*(m)` is `≤ budget`. -/
structure Cascade where
  /-- `budgetMet m ↔ D*(m) ≤ budget`. -/
  budgetMet : ℕ → Prop
  [decMet : DecidablePred budgetMet]
  /-- Some depth eventually crosses the budget (binding exists). -/
  bindingExists : ∃ m, budgetMet m

attribute [instance] Cascade.decMet

variable (c : Cascade)

/-- The **binding depth** `m*`: the least over-determination depth meeting the budget. -/
noncomputable def bindingDepth : ℕ := Nat.find c.bindingExists

/-- `m*` meets the budget. -/
theorem budgetMet_bindingDepth : c.budgetMet (bindingDepth c) :=
  Nat.find_spec c.bindingExists

/-- `m*` is the LEAST budget-meeting depth: nothing below it meets the budget. -/
theorem not_budgetMet_of_lt_bindingDepth {m : ℕ} (h : m < bindingDepth c) :
    ¬ c.budgetMet m :=
  Nat.find_min c.bindingExists h

/-- **SPEC B03 (target E1 depth-0 anchor): `m* ≥ 1`.**
At depth `0` (`s = k`) the system is not over-determined and `D*(0) > budget`, i.e.
`¬ budgetMet 0` (the empirical E2 datum). Then the least budget-meeting depth is `≥ 1`. -/
theorem one_le_bindingDepth (h0 : ¬ c.budgetMet 0) : 1 ≤ bindingDepth c := by
  rcases Nat.eq_zero_or_pos (bindingDepth c) with hz | hpos
  · exact absurd (hz ▸ budgetMet_bindingDepth c) h0
  · exact hpos

/-- Equivalent phrasing: `m* ≠ 0`. -/
theorem bindingDepth_ne_zero (h0 : ¬ c.budgetMet 0) : bindingDepth c ≠ 0 :=
  Nat.one_le_iff_ne_zero.mp (one_le_bindingDepth c h0)

end ProximityGap.BridgeB03

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ProximityGap.BridgeB03.budgetMet_bindingDepth
#print axioms ProximityGap.BridgeB03.not_budgetMet_of_lt_bindingDepth
#print axioms ProximityGap.BridgeB03.one_le_bindingDepth
#print axioms ProximityGap.BridgeB03.bindingDepth_ne_zero
