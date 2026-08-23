/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ConstantWeightPlotkinBound

/-!
# Multi-line ownership and Plotkin barriers at rate one quarter

This file isolates two architecture-level facts needed to audit attempts to
improve the three-line common-factor amplifier by adding more decoded lines.

For `ell + 1` cores, a one-fresh ownership scheme charges one label to every
owned coordinate outside the all-line core and `ell + 1` labels to every
hole.  Its exact capacity is

```text
budget + all-line-core = |U| + ell * holes.
```

Thus an excess of `e` labels over the universe requires

```text
all-line-core + e <= ell * holes.
```

This is the general common-factor/hole exchange rate.  In particular, a
saturated common factor of `m - 2` roots with the prize construction's
two-label excess requires `m <= ell * holes`.

The second result disposes of all line counts at least six before any LP is
run.  If every pair core has size at most `4m` in a `16m`-point universe,
six equal-size cores satisfy `6z <= 53m`.  Consequently no six-or-more-line
split-cubic/common-factor construction can strictly beat the three-line
asymptotic core `53m/6`.  Only four and five lines remain genuine finite
partition-LP cases.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.RateQuarterMultiLineOwnershipBarrier

attribute [local instance] Classical.propDecidable

variable {U : Type} [Fintype U] [DecidableEq U]

/-! ## The exact `ell + 1` line ownership ledger -/

/-- Union of an `ell + 1`-line core family. -/
def coreUnion {ell : Nat} (S : Fin (ell + 1) → Finset U) : Finset U :=
  Finset.univ.biUnion S

/-- Coordinates missed by every decoded-line core. -/
def hole {ell : Nat} (S : Fin (ell + 1) → Finset U) : Finset U :=
  Finset.univ \ coreUnion S

/-- Coordinates contained in every decoded-line core.  These coordinates
are dead for a one-fresh ownership map. -/
noncomputable def allCore {ell : Nat}
    (S : Fin (ell + 1) → Finset U) : Finset U :=
  Finset.univ.filter fun x => ∀ i, x ∈ S i

/-- One label per nondead owned coordinate and `ell + 1` labels per hole. -/
noncomputable def freshOwnershipBudget {ell : Nat}
    (S : Fin (ell + 1) → Finset U) : Nat :=
  (coreUnion S \ allCore S).card + (ell + 1) * (hole S).card

theorem allCore_subset_coreUnion {ell : Nat}
    (S : Fin (ell + 1) → Finset U) :
    allCore S ⊆ coreUnion S := by
  intro x hx
  simp only [allCore, mem_filter, mem_univ, true_and] at hx
  simp only [coreUnion, mem_biUnion]
  exact ⟨0, mem_univ _, hx 0⟩

/-- **General ownership identity.**  The dead all-line core exactly consumes
the `ell` extra copies supplied by holes. -/
theorem freshOwnershipBudget_add_allCore_card {ell : Nat}
    (S : Fin (ell + 1) → Finset U) :
    freshOwnershipBudget S + (allCore S).card =
      Fintype.card U + ell * (hole S).card := by
  have hnondead := Finset.card_sdiff_add_card_eq_card
    (allCore_subset_coreUnion S)
  have hunion : coreUnion S ⊆ (Finset.univ : Finset U) :=
    Finset.subset_univ _
  have hhole := Finset.card_sdiff_add_card_eq_card hunion
  simp only [freshOwnershipBudget, hole, Finset.card_univ,
    Nat.add_mul, one_mul] at hnondead hhole ⊢
  omega

/-- Any `e`-label excess over the universe requires enough holes to pay both
for the all-line core and for the excess. -/
theorem allCore_add_excess_le_hole_capacity {ell e : Nat}
    (S : Fin (ell + 1) → Finset U)
    (hbudget : Fintype.card U + e ≤ freshOwnershipBudget S) :
    (allCore S).card + e ≤ ell * (hole S).card := by
  have hledger := freshOwnershipBudget_add_allCore_card S
  omega

/-- Strictly more labels than coordinates are impossible unless the hole
capacity strictly exceeds the dead all-line core. -/
theorem allCore_card_lt_hole_capacity_of_beats_universe {ell : Nat}
    (S : Fin (ell + 1) → Finset U)
    (hbudget : Fintype.card U < freshOwnershipBudget S) :
    (allCore S).card < ell * (hole S).card := by
  have hledger := freshOwnershipBudget_add_allCore_card S
  omega

/-- At the common-factor endpoint `m - 2`, retaining the construction's
two-label excess forces at least `m` units of total hole capacity.  For three
lines this reads `m <= 2H`; for four lines, `m <= 3H`. -/
theorem saturated_excess_two_forces_hole_burden
    {ell m : Nat} (S : Fin (ell + 1) → Finset U)
    (hall : m - 2 ≤ (allCore S).card)
    (hbudget : Fintype.card U + 2 ≤ freshOwnershipBudget S) :
    m ≤ ell * (hole S).card := by
  have hcapacity := allCore_add_excess_le_hole_capacity S hbudget
  omega

/-- The primitive-direction degree budget itself limits a common factor to
at most `m - 2` roots. -/
theorem commonFactor_degree_le_m_sub_two
    {m g : Nat} (hdegree : 3 * m + g + 1 < 4 * m) :
    g ≤ m - 2 := by
  omega

/-! ## Six-line Plotkin cutoff -/

open ConstantWeightPlotkinBound

/-- Six cores with pair intersections at most `4m` cannot all have size
strictly above `53m/6`.  This is the exact arithmetic cutoff relevant to a
split-cubic base (three root fibres per pair) plus a common factor of degree
less than one fibre. -/
theorem six_core_le_three_line_amplifier
    {m z : Nat} (hm : 0 < m)
    (hU : Fintype.card U = 16 * m)
    (S : Fin 6 → Finset U)
    (hsize : ∀ i, z ≤ (S i).card)
    (hpair : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 4 * m) :
    6 * z ≤ 53 * m := by
  let T : Fin 6 → Finset U := fun i =>
    Classical.choose (Finset.exists_subset_card_eq (hsize i))
  have hTsub : ∀ i, T i ⊆ S i := by
    intro i
    exact (Classical.choose_spec
      (Finset.exists_subset_card_eq (hsize i))).1
  have hTcard : ∀ i, (T i).card = z := by
    intro i
    exact (Classical.choose_spec
      (Finset.exists_subset_card_eq (hsize i))).2
  have hTpair : ∀ i j, i ≠ j → (T i ∩ T j).card ≤ 4 * m := by
    intro i j hij
    exact (Finset.card_le_card
      (Finset.inter_subset_inter (hTsub i) (hTsub j))).trans
        (hpair i j hij)
  have hJ := constantWeight_johnson T z (4 * m) hTcard hTpair
  rw [Fintype.card_fin, hU] at hJ
  norm_num at hJ
  have htwenty : 5 * (4 * m) = 20 * m := by omega
  rw [htwenty] at hJ
  by_contra hnot
  push Not at hnot
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hbadR : (53 : ℝ) * m < 6 * z := by exact_mod_cast hnot
  have hJR : (6 : ℝ) * z ^ 2 ≤
      16 * m * (z + 20 * m) := by
    exact_mod_cast hJ
  have hprod : (0 : ℝ) ≤
      (6 * z - 53 * m) * (6 * z + 37 * m) := by
    exact mul_nonneg (le_of_lt (sub_pos.mpr hbadR)) (by positivity)
  nlinarith

/-- Consumer form for any family of at least six cores: restrict to its
first six members and apply the exact six-core cutoff. -/
theorem multi_core_le_three_line_amplifier
    {L m z : Nat} (hL : 6 ≤ L) (hm : 0 < m)
    (hU : Fintype.card U = 16 * m)
    (S : Fin L → Finset U)
    (hsize : ∀ i, z ≤ (S i).card)
    (hpair : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 4 * m) :
    6 * z ≤ 53 * m := by
  let embed : Fin 6 → Fin L := fun i =>
    ⟨i, lt_of_lt_of_le i.isLt hL⟩
  have hembed : Function.Injective embed := by
    intro i j hij
    apply Fin.ext
    simpa only [embed] using congrArg (fun x : Fin L => x.val) hij
  apply six_core_le_three_line_amplifier hm hU (fun i => S (embed i))
  · intro i
    exact hsize (embed i)
  · intro i j hij
    exact hpair (embed i) (embed j) fun heq => hij (hembed heq)

end ArkLib.ProximityGap.Frontier.RateQuarterMultiLineOwnershipBarrier

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.RateQuarterMultiLineOwnershipBarrier

#print axioms freshOwnershipBudget_add_allCore_card
#print axioms allCore_add_excess_le_hole_capacity
#print axioms saturated_excess_two_forces_hole_burden
#print axioms commonFactor_degree_le_m_sub_two
#print axioms six_core_le_three_line_amplifier
#print axioms multi_core_le_three_line_amplifier
