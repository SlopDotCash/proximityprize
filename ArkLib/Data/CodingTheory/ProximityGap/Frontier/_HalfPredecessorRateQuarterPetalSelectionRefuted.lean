/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-!
# Rate-quarter petal selection: a sharp abstract obstruction

The fresh-petal argument and the determinant union-growth argument do not by
themselves force a global iteration.  This file gives a finite, executable
countermodel to that purely cardinal inference.

At `k = 7` on 28 coordinates, take four intermediate cores forming a
sunflower.  Their common kernel has size `k - 1 = 6`, and their four disjoint
petals each have size

```text
  floor(k / 3) + 2 = 4.
```

Every core has size 10, hence lies in the saturated intermediate band
`[k+2, 2k-1]`.  Every three-core weighted overlap is exactly `2(k-1)`, so the
determinant root budget permits the triple to remain noncollapsed.  Moreover,
the two-petal, three-petal, one-companion, and two-companion inequalities all
hold with equality.  After choosing three companions, their union still uses
only 12 of the 18 coordinates outside the source core.

The model also records a label set of size `4k+1 = 29`.  It deliberately does
not claim an RS realization or attach those labels to secant lines: it refutes
only the implication from the currently proved *cardinal conclusions* to a
fresh-core selection or complement-exhaustion conclusion.  A closing argument
must therefore use additional polynomial incidence structure, or prove that
new pruning witnesses cannot remain in such a sunflower.
-/

set_option autoImplicit false

open Finset

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterPetalSelectionRefuted

abbrev Coordinate := Fin 28

def k : Nat := 7

def h : Nat := 14

/-- The common `k-1`-coordinate kernel. -/
def kernel : Finset Coordinate :=
  {0, 1, 2, 3, 4, 5}

/-- Four pairwise-disjoint four-coordinate petals. -/
def petal : Fin 4 → Finset Coordinate :=
  ![{6, 7, 8, 9},
    {10, 11, 12, 13},
    {14, 15, 16, 17},
    {18, 19, 20, 21}]

/-- The four intermediate cores in the sunflower. -/
def core (i : Fin 4) : Finset Coordinate := kernel ∪ petal i

/-- A minimal-overflow set of abstract rich-point labels. -/
def labels : Finset (Fin 29) := Finset.univ

theorem labels_card_eq_four_mul_k_add_one :
    labels.card = 4 * k + 1 := by
  decide

theorem kernel_card_eq_pred :
    kernel.card = k - 1 := by
  decide

theorem petal_card_eq_third_add_two (i : Fin 4) :
    (petal i).card = k / 3 + 2 := by
  fin_cases i <;> decide

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
theorem petal_pairwise_disjoint {i j : Fin 4} (hne : i ≠ j) :
    Disjoint (petal i) (petal j) := by
  fin_cases i <;> fin_cases j <;> simp_all [petal] <;> decide

theorem core_card_eq_ten (i : Fin 4) :
    (core i).card = 10 := by
  fin_cases i <;> decide

/-- Every modeled core lies in the exact saturated intermediate band and
below the counterexample core ceiling. -/
theorem core_in_saturated_intermediate_band (i : Fin 4) :
    k + 2 ≤ (core i).card ∧
      (core i).card < h ∧
      (core i).card ≤ 3 * k - 4 := by
  fin_cases i <;> decide

/-- The reduced-universe budget used by fresh-petal pruning is available at
every core in the model. -/
theorem fresh_pruning_budget (i : Fin 4) :
    (2 * h - (core i).card) * (k / 3 + 1) ≤
      (h + 1 - (k - 1)) ^ 2 - 1 := by
  fin_cases i <;> decide

set_option linter.flexible false in
/-- Switching to any other core supplies exactly the petal size forced by
the one-third pruning theorem. -/
theorem every_other_core_has_forced_petal {i j : Fin 4} (hne : i ≠ j) :
    k / 3 + 1 < (core j \ core i).card := by
  fin_cases i <;> fin_cases j <;>
    simp_all [core, kernel, petal] <;> decide

set_option linter.flexible false in
/-- Distinct cores meet in exactly the full determinant-budget kernel. -/
theorem core_inter_card_eq_pred {i j : Fin 4} (hne : i ≠ j) :
    (core i ∩ core j).card = k - 1 := by
  fin_cases i <;> fin_cases j <;>
    simp_all [core, kernel, petal] <;> decide

/-- Every three distinct cores exactly saturate, but do not violate, the
`2(k-1)` weighted-overlap bound. -/
theorem weighted_overlap_eq_two_mul_pred
    : (((core 0 ∩ core 1) ∪ (core 0 ∩ core 2) ∪
          (core 1 ∩ core 2)).card +
        ((core 0 ∩ core 1) ∩ core 2).card) =
      2 * (k - 1) := by
  decide

/-- The two-petal union-growth recurrence is an equality in the sunflower. -/
theorem two_petal_growth_is_exact
    : (core 1 \ core 0).card + (core 2 \ core 0).card +
          (core 0 ∩ core 1).card + (core 0 ∩ core 2).card =
      ((core 1 \ core 0) ∪ (core 2 \ core 0)).card +
        2 * (k - 1) := by
  decide

/-- Removing an anchor does not improve the one-companion inequality: it too
is exactly saturated. -/
theorem one_companion_increment_is_exact
    : (core 2 \ core 0).card +
          (core 0 ∩ core 1).card + (core 0 ∩ core 2).card =
      ((core 2 \ core 0) \ (core 1 \ core 0)).card +
        2 * (k - 1) := by
  decide

/-- With all four cores selected, the three-petal recurrence is also an exact
equality. -/
theorem three_petal_growth_is_exact
    : (core 1 \ core 0).card + (core 2 \ core 0).card +
          (core 3 \ core 0).card +
        2 * ((core 0 ∩ core 1).card + (core 0 ∩ core 2).card +
          (core 0 ∩ core 3).card) =
      ((core 1 \ core 0) ∪ (core 2 \ core 0) ∪
          (core 3 \ core 0)).card +
        6 * (k - 1) := by
  decide

/-- The anchored two-companion recurrence remains exact as well. -/
theorem two_companion_increment_is_exact
    : (core 2 \ core 0).card + (core 3 \ core 0).card +
        2 * ((core 0 ∩ core 1).card + (core 0 ∩ core 2).card +
          (core 0 ∩ core 3).card) =
      ((((core 2 \ core 0) ∪ (core 3 \ core 0)) \
          (core 1 \ core 0)).card + 6 * (k - 1)) := by
  decide

/-- Even after selecting all three possible companion petals, six coordinates
of the source-core complement remain unused. -/
theorem three_companion_petals_do_not_exhaust
    : ((core 1 \ core 0) ∪ (core 2 \ core 0) ∪
        (core 3 \ core 0)).card <
      (Finset.univ \ core 0).card := by
  decide

set_option linter.flexible false in
/-- The complementary-core closure is also unavailable: every pair of
sunflower cores misses fourteen coordinates, far more than the critical two. -/
theorem two_cores_miss_at_least_three {i j : Fin 4} (hne : i ≠ j) :
    3 ≤ (Finset.univ \ (core i ∪ core j)).card := by
  fin_cases i <;> fin_cases j <;>
    simp_all [core, kernel, petal] <;> decide

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterPetalSelectionRefuted

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterPetalSelectionRefuted
#print axioms labels_card_eq_four_mul_k_add_one
#print axioms core_in_saturated_intermediate_band
#print axioms fresh_pruning_budget
#print axioms every_other_core_has_forced_petal
#print axioms weighted_overlap_eq_two_mul_pred
#print axioms two_petal_growth_is_exact
#print axioms one_companion_increment_is_exact
#print axioms three_petal_growth_is_exact
#print axioms two_companion_increment_is_exact
#print axioms three_companion_petals_do_not_exhaust
