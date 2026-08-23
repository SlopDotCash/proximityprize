/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BchksF6_ExplicitDeltaStarLower
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-!
# BCHKS F6 — the crossing-fold MONOTONICITY constraint (#444)

**Context.** `_BchksF6_ExplicitDeltaStarLower` assembles the explicit `δ*` lower bound

> `δ* ≥ 1 − ρ − (M_cross − 1) / n`,

and its prose **defines** the crossing fold as

> `M_cross` := the **least** depth `r` with `poly · chooseCH s r ≤ ε*·|F|`
> (the char-free worst bad count drops within the soundness budget).

F6's own theorem `chooseCH_mono` proves `chooseCH s r = C(s+r−1, r)` is **monotone INCREASING**
in the depth `r`. This file discharges the structural consequence of that monotonicity, which the
F6 prose leaves implicit and (as a "least-`r`" identification) gets backwards.

## The constraint (probe `scripts/probes/probe_f6_crossing_monotonicity.py`, 0 fails / 16)

Because `chooseCH s ·` is monotone increasing, the budget predicate
`poly · chooseCH s r ≤ budget` is a **down-set in `r`** (an initial segment `{0, 1, …, R}`):
once the increasing dominator leaves the budget it never returns. Three sharp consequences:

* **(1) the *least* `r` in budget is DEGENERATE.** For any `budget ≥ poly` (e.g. `poly = 1`,
  `budget ≥ 1`) the predicate already holds at `r = 0` (`chooseCH s 0 = 1`). So the *least* `r` is
  `0` — NOT the binding depth `m*`. F6's prose "least depth `r` with `poly·chooseCH ≤ budget`" is
  the empty-multiset rung, not a meaningful crossing.

* **(2) the correct crossing fold is the *greatest* `r` in budget**, i.e. a `Nat.findGreatest`,
  with a **hard upper edge**: above the edge the predicate is FALSE and stays false (monotone
  failure). This matches the in-tree decreasing over-determination edge
  (`DecouplingDecayCrossingDepth.crossingDepth = m − 1`, LINEAR), which is the genuine binder.

* **(3) F6's `mStar_le_cross` is SOUND but over a DIFFERENT object.** `mStar` is a `Nat.find` of a
  cascade `D` whose nonvacuity witness `modelD` is *decreasing*-to-budget (least-`r` `Nat.find` is
  meaningful there). The prose identification `D := poly·chooseCH` carries the OPPOSITE
  monotonicity, so the "least-`r` crossing of `poly·chooseCH`" is not the object `mStar_le_cross`
  caps. We record this as the precise monotonicity mismatch — F6's theorems are unaffected; only
  the prose semantics of `M_cross` are corrected.

This is a NON-MOMENT, char-free, structural constraint on the F6 reduction. It does NOT prove or
refute CORE; it pins the correct (findGreatest, hard-edged) semantics of the F6 crossing fold and
its relation to the increasing complete-homogeneous count.

## Honesty (the contract)

EXTEND-proven on F6's `chooseCH` / `chooseCH_mono`. Pure `Nat` monotonicity + `Nat.findGreatest`
arithmetic; no field/thinness content, so it CANNOT (and does not) prove CORE. The increasing
`chooseCH` is a per-subset DIRECTION-count (a `Sym`-cardinality object), NOT a `δ*`/incidence
object — the asymptotic-guard cliff-at-`n/2` is UNTOUCHED, and we make NO capacity / beyond-Johnson
claim (we CONFIRM the binding crossing is a hard upper edge, consistent with the cliff guard).
Axiom audit must show a subset of `{propext, Classical.choice, Quot.sound}` — no `sorryAx`.

Issue #444, constraint on F6 (`_BchksF6_ExplicitDeltaStarLower`). Builds on `chooseCH`,
`chooseCH_mono`.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.BchksF6

/-! ## 1. `chooseCH s ·` is monotone increasing across the whole depth range (not just one step) -/

/-- **Full monotonicity of `chooseCH` in the depth `r`** (for `s ≥ 1`): `r₁ ≤ r₂ → chooseCH s r₁ ≤
chooseCH s r₂`. The one-step `chooseCH_mono` lifted to the whole range — the complete-homogeneous
count never decreases as the over-determination depth grows. -/
theorem chooseCH_mono_le {s : ℕ} (hs : 1 ≤ s) {r₁ r₂ : ℕ} (h : r₁ ≤ r₂) :
    chooseCH s r₁ ≤ chooseCH s r₂ := by
  induction h with
  | refl => exact le_refl _
  | step _ ih => exact le_trans ih (chooseCH_mono hs _)

/-! ## 2. The budget predicate is a DOWN-SET in `r` (an initial segment) -/

/-- **The budget predicate is downward-closed in the depth.** If the increasing complete-homogeneous
dominator `poly · chooseCH s r` is within `budget` at depth `r₂`, then it is within `budget` at
every SHALLOWER depth `r₁ ≤ r₂`. Hence `{r : poly · chooseCH s r ≤ budget}` is an initial segment. -/
theorem budget_predicate_downward_closed
    {s poly budget : ℕ} (hs : 1 ≤ s) {r₁ r₂ : ℕ} (h : r₁ ≤ r₂)
    (hr₂ : poly * chooseCH s r₂ ≤ budget) :
    poly * chooseCH s r₁ ≤ budget :=
  le_trans (Nat.mul_le_mul_left poly (chooseCH_mono_le hs h)) hr₂

/-! ## 3. (1) The LEAST-`r` crossing is DEGENERATE — it is `0` -/

/-- **The least depth in budget is `0` — degenerate.** Since `chooseCH s 0 = 1`, the predicate
`poly · chooseCH s r ≤ budget` already holds at `r = 0` as soon as `poly ≤ budget` (e.g.
`poly = 1`, `budget ≥ 1`). So the *least* `r` satisfying F6's prose crossing is `0`, the
empty-multiset rung — NOT the binding depth. This is the precise sense in which "least depth `r`
with `poly · chooseCH s r ≤ budget`" cannot be the binder. -/
theorem least_crossing_degenerate {s poly budget : ℕ} (hpb : poly ≤ budget) :
    poly * chooseCH s 0 ≤ budget := by
  rw [chooseCH_zero, Nat.mul_one]; exact hpb

/-- **`r = 0` is THE least element of the in-budget set** (it is in the set and is `≤` everything).
Combined with `least_crossing_degenerate`: the `Nat.find` "least depth in budget" of F6's prose is
exactly `0`, independent of `s`, `budget` (for `poly ≤ budget`). -/
theorem least_in_budget_is_zero
    {s poly budget : ℕ} (hpb : poly ≤ budget)
    (hex : ∃ r, poly * chooseCH s r ≤ budget) :
    Nat.find hex = 0 :=
  Nat.eq_zero_of_le_zero (Nat.find_min' hex (least_crossing_degenerate hpb))

/-! ## 4. (2) The CORRECT crossing fold is the GREATEST `r` in budget, with a HARD upper edge -/

/-- **The hard upper edge of the crossing fold.** If at some depth `r` the dominator exceeds the
budget (`budget < poly · chooseCH s r`), then it exceeds the budget at EVERY deeper depth `r' ≥ r`
(monotone failure — the increasing dominator never re-enters). So the in-budget set has a hard
ceiling: once out, always out. This is the `findGreatest`-edge that the binding fold actually has,
the opposite of a `Nat.find` least element. -/
theorem budget_fails_above_edge
    {s poly budget : ℕ} (hs : 1 ≤ s) {r r' : ℕ} (hrr : r ≤ r')
    (hfail : budget < poly * chooseCH s r) :
    budget < poly * chooseCH s r' :=
  lt_of_lt_of_le hfail (Nat.mul_le_mul_left poly (chooseCH_mono_le hs hrr))

/-- **`Nat.findGreatest` is the correct crossing fold.** With the predicate
`P r := poly · chooseCH s r ≤ budget`, the greatest in-budget depth `≤ B` is
`Nat.findGreatest P B`. Whenever the predicate holds at some `r ≤ B`, that `r` is `≤` the fold
(`Nat.le_findGreatest`) — i.e. the fold dominates every in-budget depth, the defining property of
the binder's hard upper edge (NOT a least element). -/
theorem findGreatest_is_crossing_fold
    {s poly budget : ℕ} {B r : ℕ}
    (hrB : r ≤ B) (hr : poly * chooseCH s r ≤ budget) :
    r ≤ Nat.findGreatest (fun t => poly * chooseCH s t ≤ budget) B :=
  Nat.le_findGreatest hrB hr

/-- **The crossing fold IS in budget (from any in-budget witness).** Given a witness depth `r ≤ B`
with the dominator within budget, the `findGreatest` crossing fold is ALSO within budget — so the
fold is a genuine in-budget binder, not a vacuous index. (`Nat.findGreatest_spec`.) -/
theorem findGreatest_crossing_in_budget
    {s poly budget : ℕ} {B r : ℕ}
    (hrB : r ≤ B) (hr : poly * chooseCH s r ≤ budget) :
    poly * chooseCH s (Nat.findGreatest (fun t => poly * chooseCH s t ≤ budget) B) ≤ budget :=
  Nat.findGreatest_spec (P := fun t => poly * chooseCH s t ≤ budget) hrB hr

/-! ## 5. (3) The monotonicity MISMATCH with F6's abstract-cascade `mStar` -/

/-- **F6's `modelD` (its nonvacuity cascade) is DECREASING-to-budget — the opposite monotonicity to
`chooseCH`.** `modelD 16 j = 200` for `j ≤ 2` and `0` after, so it is over budget (`200 > 120`)
on an INITIAL segment and within budget (`0 ≤ 120`) on the COMPLEMENT — exactly the shape for which
a *least*-`r` `Nat.find` binder (`m* = 3`) is meaningful. The increasing `chooseCH` has the reverse
shape (in budget on an initial segment), so its least-`r` crossing is degenerate
(`least_in_budget_is_zero`). The two `Nat.find` objects are NOT the same: F6's `mStar_le_cross`
caps the decreasing-`D` binder; the prose identification `D := poly · chooseCH` is the mismatch. -/
theorem modelD_decreasing_to_budget :
    (modelD 16 0 > 120 ∧ modelD 16 1 > 120 ∧ modelD 16 2 > 120) ∧
    (modelD 16 3 ≤ 120 ∧ modelD 16 4 ≤ 120) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩ <;> (unfold modelD; decide)

/-- **The mismatch, made explicit at the F6 nonvacuity scale `s = 8`, `poly = 1`, `budget = 120`.**
The least-`r` crossing of the INCREASING dominator `chooseCH 8 ·` is `0` (degenerate), whereas the
binding depth of the DECREASING cascade `modelD` is `3`. So F6's binder (`m* = 3`, the decreasing
`modelD` `Nat.find`) and the prose "least-`r` of `poly·chooseCH`" (`= 0`) are DIFFERENT objects;
the explicit lower bound's `M_cross` must be read as the `findGreatest` edge of the increasing
dominator (also `3` here, `findGreatest_is_crossing_fold`), not a least element. -/
theorem crossing_fold_mismatch
    (hex : ∃ r, (1 : ℕ) * chooseCH 8 r ≤ 120) :
    Nat.find hex = 0 ∧
    (3 : ℕ) ≤ Nat.findGreatest (fun t => (1 : ℕ) * chooseCH 8 t ≤ 120) 3 := by
  refine ⟨least_in_budget_is_zero (by decide) hex, ?_⟩
  exact findGreatest_is_crossing_fold (le_refl 3) (by unfold chooseCH; decide)

end ArkLib.ProximityGap.BchksF6

/-! ## Axiom audit (expected: a subset of `propext, Classical.choice, Quot.sound` — no `sorryAx`) -/
#print axioms ArkLib.ProximityGap.BchksF6.chooseCH_mono_le
#print axioms ArkLib.ProximityGap.BchksF6.budget_predicate_downward_closed
#print axioms ArkLib.ProximityGap.BchksF6.least_in_budget_is_zero
#print axioms ArkLib.ProximityGap.BchksF6.budget_fails_above_edge
#print axioms ArkLib.ProximityGap.BchksF6.findGreatest_is_crossing_fold
#print axioms ArkLib.ProximityGap.BchksF6.findGreatest_crossing_in_budget
#print axioms ArkLib.ProximityGap.BchksF6.modelD_decreasing_to_budget
#print axioms ArkLib.ProximityGap.BchksF6.crossing_fold_mismatch
