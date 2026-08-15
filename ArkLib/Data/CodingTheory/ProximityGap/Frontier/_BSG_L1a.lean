/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Combinatorics.Additive.Energy
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option linter.style.longLine false
set_option autoImplicit false

/-!
# `BSG L1a`: representation-function normalization `∑ r(x) = |A|²`

This is the L1a layer of the in-tree Balog–Szemerédi–Gowers attack. It proves the
*normalization identity* for the difference representation function `repCount` (the same `def`
as in `_BSG_L0`, reproduced here so this scratch file iterates against Mathlib alone):
$$ \sum_{x \in A - A} r(x) = |A|^2, \qquad r(x) = \#\{(a,b) \in A \times A : a - b = x\}. $$

This is the total ordered-pair count `|A|²`, partitioned by the difference of each pair, and is
the normalization used by L2 to bound the "unpopular" mass (`∑_{x unpopular} r(x)² < |A|³/(2K)`).

The proof is pure double counting: `Finset.sum_card_fiberwise_eq_card_filter` partitions
`A ×ˢ A` over the fibers of the difference map `(a,b) ↦ a - b` into `A - A`; every pair's
difference lies in `A - A` (`Finset.sub_mem_sub`), so the resulting filter is the whole product
`A ×ˢ A`, of cardinality `|A| · |A| = |A|²`.
-/

namespace ArkLib.BSG.L1a

open Finset
open scoped Pointwise

variable {α : Type*} [AddCommGroup α] [DecidableEq α]

/-- The difference representation function: `repCount A x = r(x)` counts ordered pairs
`(a, b) ∈ A × A` with `a - b = x`. (Same definition as `_BSG_L0.repCount`.) -/
def repCount (A : Finset α) (x : α) : ℕ :=
  #{p ∈ A ×ˢ A | p.1 - p.2 = x}

/-- **L1a (representation-function normalization).** `∑_{x ∈ A - A} repCount A x = |A|²`.

The total number of ordered pairs in `A × A`, partitioned by their difference `a - b`. Each
pair contributes to exactly one fiber (its difference, which lies in `A - A`), so the sum of the
fiber sizes is the size of the whole product `A ×ˢ A`. -/
theorem repCount_sum_eq_card_sq (A : Finset α) :
    ∑ x ∈ A - A, repCount A x = #A ^ 2 := by
  unfold repCount
  -- Partition `A ×ˢ A` over the fibers of the difference map into `A - A`.
  rw [Finset.sum_card_fiberwise_eq_card_filter (A ×ˢ A) (A - A) (fun p => p.1 - p.2)]
  -- Every pair's difference lands in `A - A`, so the filter selects the whole product.
  have hfilter : {p ∈ A ×ˢ A | p.1 - p.2 ∈ A - A} = A ×ˢ A := by
    apply Finset.filter_true_of_mem
    intro p hp
    rw [Finset.mem_product] at hp
    exact Finset.sub_mem_sub hp.1 hp.2
  rw [hfilter, Finset.card_product, sq]

end ArkLib.BSG.L1a
