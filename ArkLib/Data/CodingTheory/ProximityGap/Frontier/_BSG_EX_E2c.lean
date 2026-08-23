/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BSG_DRC1

/-!
# BareDRCExtract sub-lemma E2c — good-pair cherry mass is at most `#goodPairs · #A`

This file proves the **count-from-mass** step of the dependent-random-choice extraction.

`commonNeighbors A G a a'` is the cardinality of a `Finset` filter of `A`, hence is at most
`#A`. Summing this pointwise bound over the *good* pairs
`{p ∈ A ×ˢ A | t ≤ commonNeighbors A G p.1 p.2}` gives that the good-pair cherry mass is at
most `#goodPairs · #A`.

Combined with `Finset.BSG.sum_commonNeighbors_goodPairs_ge` (E2b: the good-pair mass is
`≥ #A² · t` once the cherry-richness hypothesis holds at threshold `t`), this converts the
*weighted* good-pair statement into the *count* statement `#goodPairs ≥ #A · t` needed for the
row-pigeonhole step E3.
-/

open Finset
open scoped BigOperators Pointwise

namespace Finset.BSG

variable {α : Type*} [AddCommGroup α] [DecidableEq α]

/-- `commonNeighbors A G a a'` counts a subset of `A`, so it is at most `#A`. -/
lemma commonNeighbors_le_card (A : Finset α) (G : Finset (α × α)) (a a' : α) :
    commonNeighbors A G a a' ≤ #A := by
  rw [commonNeighbors]
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- **E2c — good-pair cherry mass is at most `#goodPairs · #A`.**

Each common-neighbour count `cn(a, a')` is at most `#A` (it filters `A`), so summing the
constant bound over the good pairs yields the stated inequality. Together with E2b this gives
the COUNT `#goodPairs ≥ #A · t`. -/
theorem card_goodPairs_count_le_total_and_mass (A : Finset α) (G : Finset (α × α)) (t : ℕ) :
    (∑ p ∈ {p ∈ A ×ˢ A | t ≤ commonNeighbors A G p.1 p.2}, commonNeighbors A G p.1 p.2)
      ≤ #({p ∈ A ×ˢ A | t ≤ commonNeighbors A G p.1 p.2} : Finset (α × α)) * #A := by
  calc (∑ p ∈ {p ∈ A ×ˢ A | t ≤ commonNeighbors A G p.1 p.2}, commonNeighbors A G p.1 p.2)
      ≤ ∑ _p ∈ {p ∈ A ×ˢ A | t ≤ commonNeighbors A G p.1 p.2}, #A := by
        apply Finset.sum_le_sum
        intro p _
        exact commonNeighbors_le_card A G p.1 p.2
    _ = #({p ∈ A ×ˢ A | t ≤ commonNeighbors A G p.1 p.2} : Finset (α × α)) * #A := by
        rw [Finset.sum_const, smul_eq_mul]

end Finset.BSG

#print axioms Finset.BSG.commonNeighbors_le_card
#print axioms Finset.BSG.card_goodPairs_count_le_total_and_mass
