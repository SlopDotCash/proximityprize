/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Lattice

/-!
# Bridge B03 (saturation form) — binding depth `m* ≥ 1` from depth-0 saturation (target E1) (#444)

`δ*` is pinned (E1) by `δ* = 1 − ρ − (m*−1)/n`, with `m* = s − k` at binding the **binding depth**:
the least over-determination depth `m` whose worst far-line over-determined incidence `D*(m)`
drops to budget, `D*(m) ≤ budget`.

SPEC B03 CLAIM: `m* ≥ 1`. APPROACH: at `s = k` (depth `m = 0`) the system is NOT
over-determined — every direction `γ` agrees — so `D*(0)` is the **full / saturated** count
`Dfull`, which exceeds the budget. Hence depth `0` does not meet the budget and the first
budget-meeting (binding) depth is `≥ 1`.

This version IMPROVES on the bald-hypothesis form: instead of assuming `¬ budgetMet 0`, we model the
cascade by its actual incidence values `Dstar : ℕ → ℕ` against a `budget : ℕ`, encode the depth-0
saturation as `Dstar 0 = Dfull` with `Dfull > budget` (the genuine geometric content: at `s = k`
every γ agrees so the count saturates to the full `Dfull > budget`), and DERIVE `¬ budgetMet 0`.
So the empirical E2 datum enters only as the inequality `budget < Dfull` (budget below the full
saturated count), which is the honest structural fact, and `m* ≥ 1` is then a theorem.

## Honesty
The only inputs are: `Dstar 0 = Dfull` (depth-0 saturation: full agreement count), `budget < Dfull`
(budget strictly below the saturated full count — the geometric over-budget fact), and that some
depth meets the budget (binding exists). From these `m* ≥ 1` is proven with no `sorry`, no `axiom`,
no `native_decide`.

Issue #444.
-/

namespace ProximityGap.BridgeB03sat

/-- An over-determination cascade given by its worst far-line incidence values `Dstar m = D*(m)`
against a fixed `budget`. `Dfull` is the full / saturated count at depth `0` (full agreement at
`s = k`), and the structural fact `budget < Dfull` records that the budget is below saturation. -/
structure SatCascade where
  /-- `D*(m)` = worst far-line over-determined incidence at over-determination depth `m`. -/
  Dstar : ℕ → ℕ
  /-- The budget `≈ n` (the prize incidence budget `q·ε*`). -/
  budget : ℕ
  /-- The full / saturated incidence count at depth `0` (`s = k`, every γ agrees). -/
  Dfull : ℕ
  /-- Depth-0 saturation: at `s = k` the system is not over-determined, so `D*(0)` is the full
  count. -/
  satZero : Dstar 0 = Dfull
  /-- The budget lies strictly below the saturated full count (the empirical E2 over-budget fact). -/
  budget_lt_Dfull : budget < Dfull
  /-- Binding exists: some depth's incidence drops to budget. -/
  bindingExists : ∃ m, Dstar m ≤ budget

variable (c : SatCascade)

/-- `budgetMet m ↔ D*(m) ≤ budget`. -/
def budgetMet (m : ℕ) : Prop := c.Dstar m ≤ c.budget

instance moduleInstance_BridgeB03sat_1 : DecidablePred (budgetMet c) := fun _ => Nat.decLe _ _

/-- The **binding depth** `m*`: the least over-determination depth meeting the budget. -/
noncomputable def bindingDepth : ℕ := Nat.find c.bindingExists

/-- `m*` meets the budget. -/
theorem budgetMet_bindingDepth : budgetMet c (bindingDepth c) :=
  Nat.find_spec c.bindingExists

/-- `m*` is the LEAST budget-meeting depth. -/
theorem not_budgetMet_of_lt_bindingDepth {m : ℕ} (h : m < bindingDepth c) :
    ¬ budgetMet c m :=
  Nat.find_min c.bindingExists h

/-- **Depth-0 is over budget (DERIVED from saturation).** `D*(0) = Dfull > budget`. -/
theorem not_budgetMet_zero : ¬ budgetMet c 0 := by
  unfold budgetMet
  rw [c.satZero]
  exact Nat.not_le.mpr c.budget_lt_Dfull

/-- **SPEC B03 (target E1 depth-0 anchor): `m* ≥ 1`.**
At depth `0` the system is not over-determined and saturates, `D*(0) = Dfull > budget`, so the
least budget-meeting depth is `≥ 1`. -/
theorem one_le_bindingDepth : 1 ≤ bindingDepth c := by
  rcases Nat.eq_zero_or_pos (bindingDepth c) with hz | hpos
  · exact absurd (hz ▸ budgetMet_bindingDepth c) (not_budgetMet_zero c)
  · exact hpos

/-- Equivalent phrasing: `m* ≠ 0`. -/
theorem bindingDepth_ne_zero : bindingDepth c ≠ 0 :=
  Nat.one_le_iff_ne_zero.mp (one_le_bindingDepth c)

end ProximityGap.BridgeB03sat

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ProximityGap.BridgeB03sat.not_budgetMet_zero
#print axioms ProximityGap.BridgeB03sat.one_le_bindingDepth
#print axioms ProximityGap.BridgeB03sat.bindingDepth_ne_zero
