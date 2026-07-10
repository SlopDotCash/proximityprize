/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ConstantWeightPlotkinBound

/-!
# Rate-quarter next lattice: ownership and dead-coordinate ledger

This file isolates the exact three-core set-system bookkeeping behind a
one-fresh, determinant-collapsed construction.

* A coordinate in one or two cores is owned but not dead.  The primitive
  direction invariant assigns at most one coordinate-determined scalar to it.
* A coordinate outside all three cores is a hole.  It can contribute at most
  one isolated scalar for each of the three source lines.
* A coordinate in all three cores is dead: no source core misses it, so it
  cannot serve as a fresh point.

Consequently the abstract one-fresh ownership budget is

```text
nondead-owned + 3*holes = n + 2*holes - triple.
```

At the next-lattice core threshold `8m+r+1 = 25r+9`, with `m=3r+1`, a budget
strictly larger than `n` forces one of two outcomes:

1. one **proper** pair cell (coordinates in exactly those two cores) has size
   at least `3m+1`, giving genuinely new split-locator overlap; or
2. the precise `multiHoleTripleTradeResidual`: there are at least two holes,
   and if `H` is the hole size and `A` the all-three intersection size, then
   `H+2 ≤ 2A` while `A < 2H`.

The second branch is honest: cardinal bookkeeping alone does not refute it.
It describes exactly how extra isolated-hole capacity could pay for dead
common-factor coordinates.  No constant-coefficient locator collinearity is
asserted here.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.RateQuarterNextLatticeOwnershipLedger

attribute [local instance] Classical.propDecidable

variable {U : Type} [Fintype U] [DecidableEq U]

/-- Union of the three decoded-line cores. -/
def coreUnion (S : Fin 3 → Finset U) : Finset U :=
  S 0 ∪ S 1 ∪ S 2

/-- Coordinates missed by all three decoded-line cores. -/
def hole (S : Fin 3 → Finset U) : Finset U :=
  Finset.univ \ coreUnion S

/-- Coordinates contained in all three decoded-line cores.  These are dead
for a one-fresh construction. -/
def tripleCore (S : Fin 3 → Finset U) : Finset U :=
  (S 0 ∩ S 1) ∩ S 2

/-- Coordinates contained in cores zero and one, but not core two. -/
def properPair01 (S : Fin 3 → Finset U) : Finset U :=
  (S 0 ∩ S 1) \ S 2

/-- Coordinates contained in cores zero and two, but not core one. -/
def properPair02 (S : Fin 3 → Finset U) : Finset U :=
  (S 0 ∩ S 2) \ S 1

/-- Coordinates contained in cores one and two, but not core zero. -/
def properPair12 (S : Fin 3 → Finset U) : Finset U :=
  (S 1 ∩ S 2) \ S 0

/-- Abstract scalar capacity of the three-line one-fresh ownership scheme:
one label per nondead owned coordinate and three labels per hole. -/
def freshOwnershipBudget (S : Fin 3 → Finset U) : Nat :=
  (coreUnion S \ tripleCore S).card + 3 * (hole S).card

/-- The all-three core is contained in the three-core union. -/
theorem tripleCore_subset_coreUnion (S : Fin 3 → Finset U) :
    tripleCore S ⊆ coreUnion S := by
  intro x hx
  simp only [tripleCore, coreUnion, mem_inter, mem_union] at hx ⊢
  exact Or.inl (Or.inl hx.1.1)

/-- **Ownership/dead-coordinate identity.**  Adding the dead triple-core
coordinates back to the usable one-fresh budget gives the universe plus two
extra copies of every hole. -/
theorem freshOwnershipBudget_add_tripleCore_card
    (S : Fin 3 → Finset U) :
    freshOwnershipBudget S + (tripleCore S).card =
      Fintype.card U + 2 * (hole S).card := by
  have hnondead := Finset.card_sdiff_add_card_eq_card
    (tripleCore_subset_coreUnion S)
  have hunion : coreUnion S ⊆ (Finset.univ : Finset U) := Finset.subset_univ _
  have hhole := Finset.card_sdiff_add_card_eq_card hunion
  simp only [freshOwnershipBudget, hole, Finset.card_univ] at hnondead hhole ⊢
  omega

/-- Exact incidence decomposition of three cores.  A singleton-core
coordinate contributes one incidence, a proper-pair coordinate two, and a
triple-core coordinate three. -/
theorem three_core_incidence_ledger (S : Fin 3 → Finset U) :
    (S 0).card + (S 1).card + (S 2).card =
      (coreUnion S).card +
        (properPair01 S).card + (properPair02 S).card +
          (properPair12 S).card +
        (tripleCore S).card + (tripleCore S).card := by
  have hpoint : ∀ x : U,
      (if x ∈ S 0 then (1 : Nat) else 0) +
          (if x ∈ S 1 then (1 : Nat) else 0) +
        (if x ∈ S 2 then (1 : Nat) else 0) =
      (if x ∈ coreUnion S then (1 : Nat) else 0) +
          (if x ∈ properPair01 S then (1 : Nat) else 0) +
          (if x ∈ properPair02 S then (1 : Nat) else 0) +
          (if x ∈ properPair12 S then (1 : Nat) else 0) +
          (if x ∈ tripleCore S then (1 : Nat) else 0) +
        (if x ∈ tripleCore S then (1 : Nat) else 0) := by
    intro x
    by_cases h0 : x ∈ S 0 <;>
      by_cases h1 : x ∈ S 1 <;>
        by_cases h2 : x ∈ S 2 <;>
          simp [coreUnion, properPair01, properPair02, properPair12,
            tripleCore, h0, h1, h2]
  have hsum := Finset.sum_congr rfl fun x
    (_hx : x ∈ (Finset.univ : Finset U)) => hpoint x
  simp only [Finset.sum_add_distrib] at hsum
  have hcard (T : Finset U) :
      (∑ x : U, if x ∈ T then (1 : Nat) else 0) = T.card := by
    simpa using (Finset.card_filter (fun x : U => x ∈ T) Finset.univ).symm
  rw [hcard (S 0), hcard (S 1), hcard (S 2), hcard (coreUnion S),
    hcard (properPair01 S), hcard (properPair02 S),
    hcard (properPair12 S), hcard (tripleCore S)] at hsum
  exact hsum

/-- The exact named residual left by the ownership ledger when no proper pair
cell grows beyond the old `3m` smooth-locator size. -/
def MultiHoleTripleTradeResidual (S : Fin 3 → Finset U) : Prop :=
  2 ≤ (hole S).card ∧
    (hole S).card + 2 ≤ 2 * (tripleCore S).card ∧
    (tripleCore S).card < 2 * (hole S).card

/-- **Sharp three-line next-lattice obstruction.**  Suppose all three cores
have the one-fresh next-lattice size `8m+r+1`, where `m=3r+1`, in a universe
of size `16m`.  If their abstract ownership budget beats the `n`-scalar
challenge, then either a proper pair cell has size at least `3m+1`, or the
precise multi-hole/triple-core trade residual holds. -/
theorem proper_pair_growth_or_multiHoleTripleTradeResidual
    {m r : Nat} (hm : m = 3 * r + 1)
    (hU : Fintype.card U = 16 * m)
    (S : Fin 3 → Finset U)
    (hsize : ∀ i, 8 * m + r + 1 ≤ (S i).card)
    (hbudget : Fintype.card U < freshOwnershipBudget S) :
    3 * m + 1 ≤ (properPair01 S).card ∨
      3 * m + 1 ≤ (properPair02 S).card ∨
      3 * m + 1 ≤ (properPair12 S).card ∨
      MultiHoleTripleTradeResidual S := by
  by_cases h01 : 3 * m + 1 ≤ (properPair01 S).card
  · exact Or.inl h01
  by_cases h02 : 3 * m + 1 ≤ (properPair02 S).card
  · exact Or.inr (Or.inl h02)
  by_cases h12 : 3 * m + 1 ≤ (properPair12 S).card
  · exact Or.inr (Or.inr (Or.inl h12))
  right
  right
  right
  have h01cap : (properPair01 S).card ≤ 3 * m := by omega
  have h02cap : (properPair02 S).card ≤ 3 * m := by omega
  have h12cap : (properPair12 S).card ≤ 3 * m := by omega
  have hincidence := three_core_incidence_ledger S
  have hownership := freshOwnershipBudget_add_tripleCore_card S
  have hunion : coreUnion S ⊆ (Finset.univ : Finset U) := Finset.subset_univ _
  have hhole : (hole S).card + (coreUnion S).card = 16 * m := by
    simpa only [hole, Finset.card_univ, hU] using
      (Finset.card_sdiff_add_card_eq_card hunion)
  have hsize0 := hsize 0
  have hsize1 := hsize 1
  have hsize2 := hsize 2
  have hlower : (hole S).card + 2 ≤ 2 * (tripleCore S).card := by
    omega
  have hupper : (tripleCore S).card < 2 * (hole S).card := by
    omega
  have hholes : 2 ≤ (hole S).card := by omega
  exact ⟨hholes, hlower, hupper⟩

/-- Consumer form for an actual charged scalar family.  Any family larger
than the universe whose one-fresh ownership map is bounded by
`freshOwnershipBudget` enters the same proper-pair-growth/residual dichotomy. -/
theorem proper_pair_growth_or_residual_of_charged_bad_family
    {Gamma : Type} [DecidableEq Gamma]
    {m r : Nat} (hm : m = 3 * r + 1)
    (hU : Fintype.card U = 16 * m)
    (S : Fin 3 → Finset U)
    (hsize : ∀ i, 8 * m + r + 1 ≤ (S i).card)
    (G : Finset Gamma) (hbad : Fintype.card U < G.card)
    (hcharge : G.card ≤ freshOwnershipBudget S) :
    3 * m + 1 ≤ (properPair01 S).card ∨
      3 * m + 1 ≤ (properPair02 S).card ∨
      3 * m + 1 ≤ (properPair12 S).card ∨
      MultiHoleTripleTradeResidual S := by
  apply proper_pair_growth_or_multiHoleTripleTradeResidual hm hU S hsize
  omega

/-- **Sharpness red team.**  The named residual is arithmetically feasible.
Take two holes, two triple-core coordinates, three proper pair cells of size
exactly `3m`, and three singleton cells of size `7r+1`.  Disjoint cells with
these sizes have universe size `16m`; every core has exactly the next-lattice
size `8m+r+1`; and the ownership budget is `16m+2`, although no proper pair
cell exceeds the old `3m` cap.

Thus no strengthening based only on the eight Venn-cell cardinalities can
remove `MultiHoleTripleTradeResidual`.  Polynomial split-locator structure is
genuinely required. -/
theorem twoHole_twoTriple_cell_ledger_is_sharp
    {m r : Nat} (hm : m = 3 * r + 1) :
    2 + 3 * (7 * r + 1) + 3 * (3 * m) + 2 = 16 * m ∧
      (7 * r + 1) + 2 * (3 * m) + 2 = 8 * m + r + 1 ∧
      3 * (7 * r + 1) + 3 * (3 * m) + 3 * 2 = 16 * m + 2 ∧
      3 * m = 3 * m ∧
      2 + 2 ≤ 2 * 2 ∧
      2 < 2 * 2 := by
  omega

end ArkLib.ProximityGap.Frontier.RateQuarterNextLatticeOwnershipLedger

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.RateQuarterNextLatticeOwnershipLedger
#print axioms freshOwnershipBudget_add_tripleCore_card
#print axioms three_core_incidence_ledger
#print axioms proper_pair_growth_or_multiHoleTripleTradeResidual
#print axioms proper_pair_growth_or_residual_of_charged_bad_family
#print axioms twoHole_twoTriple_cell_ledger_is_sharp
