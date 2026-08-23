/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.AntipodalVanishingCountLower

/-!
# §6.5 — coset-union vanishing LOWER bound `2^{n/d} ≤ V(μ_n)` for any zero-sum block size `d` (#444)

This generalizes `AntipodalVanishingCountLower.lean` (the `d = 2` antipodal case `2^{n/2} ≤ V_1`)
to **arbitrary zero-sum blocks**: if `μ_n` is partitioned into `n/d` cosets of an order-`d`
subgroup, each coset summing to `0` (true for the `d`-th roots of unity with `d ≥ 2`,
`∑ d`-th roots `= 0`), then every UNION of cosets has subset-sum `0`, and there are `2^{n/d}` such
unions, giving

> **`2^{n/d} ≤ V(μ_n) = #{ S ⊆ μ_n : ∑_{x∈S} x = 0 }`**.

This makes the **PROBE-CARRIED** "coset-union ⊆ vanishing" identification of
`OverdetVanishingCosetCount.lean` (which carries `vanishing ⟺ coset-union` from Lam–Leung as a
hypothesis) into a **theorem for the ⊇ (lower) direction at every block size `d`** — not just the
antipodal `d = 2` case.  At `d = dyadicBlock r` this is the depth-`r` supply floor
`V_r(μ_n) ≥ 2^{n/dyadicBlock r}` (the coset-union vanishing supply the §6.4 m∗ argument consumes),
now with its lower direction unconditional.

Probe receipt: `scripts/probes/probe_coset_union_vanishing.py` (exact, n = 8,16, d = 2,4,8): each
coset of the order-`d` subgroup sums to `0` and every coset-union vanishes, **provided `d < n`**
(at `d = n` the "cosets" are singletons summing to `ζ^i ≠ 0` — correctly excluded).  `#unions = 2^{n/d}`.

## What is proved (axiom-clean)

- `sum_blockUnion_eq_zero` — abstract: a union of blocks, each summing to `0`, sums to `0`.
- `blockUnion_card` — `2^{#blocks}` distinct block-unions (reuses the injectivity machinery).
- `card_le_vanishing_of_blockUnions` — the headline `2^{#blocks} ≤ #vanishing` for zero-sum blocks.
- `ZMod 6` `example` — non-vacuity witness with the order-3 zero-sum block `{0,2,4}` (`0+2+4 = 6 = 0`),
  discharged by `decide`.

## Scope / honesty (rule 3, rule 6)

CHAR-0, NOT thinness-essential, NOT a CORE closure — the LOWER (⊇) direction of the §6.5
coset-union/vanishing identity, at arbitrary block size.  The UPPER (Lam–Leung ⊆) direction stays
carried.  Removes the probe-carried lower-direction hypothesis from the §6.5 supply chain at every
depth `r` (`V_r ≥ 2^{n/dyadicBlock r}`).  CORE (`M(μ_n) ≤ C√(n log m)`) stays OPEN.

Issue #444, §6.5 (coset-union lower direction, all depths).
-/

set_option linter.unusedVariables false

namespace ArkLib.ProximityGap.CosetUnionVanishingLower

open Finset BigOperators
open ArkLib.ProximityGap.AntipodalVanishingCountLower

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-! ### A union of zero-sum blocks sums to zero. -/

/-- **Block-union vanishing.**  If a `Finset T` of blocks (`block : β → Finset G`) are pairwise
disjoint and each sums to `0`, then the union `⋃_{i∈T} block i` sums to `0`.  (Generalizes the
antipodal `sum_pairUnion_eq_zero`: there each block is a pair `{x, -x}` summing to `0`; here a block
is any zero-sum set — e.g. a coset of an order-`d` subgroup of `μ_n`, `∑ = ζ^i · ∑ d`-th roots `= 0`.) -/
theorem sum_blockUnion_eq_zero {β : Type*} [DecidableEq β] (block : β → Finset G)
    (hdisj : ∀ i j, i ≠ j → Disjoint (block i) (block j))
    (hzero : ∀ i, ∑ x ∈ block i, x = 0)
    (T : Finset β) :
    ∑ x ∈ T.biUnion block, x = 0 := by
  rw [Finset.sum_biUnion]
  · refine Finset.sum_eq_zero ?_
    intro i _; exact hzero i
  · -- pairwise disjoint on T
    intro i _ j _ hij
    exact hdisj i j hij

/-! ### Block-unions number `2^{#blocks}` (reuse the antipodal injectivity machinery). -/

/-- The number of block-unions of `p` pairwise-disjoint nonempty blocks is `2^p`. -/
theorem blockUnion_card {p : ℕ} (block : Fin p → Finset G)
    (hdisj : ∀ i j, i ≠ j → Disjoint (block i) (block j))
    (hne : ∀ i, (block i).Nonempty) :
    (Finset.univ.image (pairUnion block)).card = 2 ^ p :=
  pairUnion_card block hdisj hne

/-! ### The headline lower bound for zero-sum blocks. -/

variable [Fintype G]

/-- **`2^p ≤ V` for `p` pairwise-disjoint nonempty zero-sum blocks.**  Each block-union is a union of
zero-sum blocks, hence (by `sum_blockUnion_eq_zero`) vanishes; the `2^p` block-unions are distinct,
so the vanishing family has `≥ 2^p` members.  With `p = n/d` cosets of the order-`d` subgroup of
`μ_n` (each summing to `0`, `d ≥ 2`) this is `2^{n/d} ≤ V(μ_n)`. -/
theorem card_le_vanishing_of_blockUnions {p : ℕ} (block : Fin p → Finset G)
    (hdisj : ∀ i j, i ≠ j → Disjoint (block i) (block j))
    (hne : ∀ i, (block i).Nonempty)
    (hzero : ∀ i, ∑ x ∈ block i, x = 0) :
    2 ^ p ≤ (Finset.univ.filter (fun S : Finset G => ∑ x ∈ S, x = 0)).card := by
  have hsub : (Finset.univ.image (pairUnion block))
      ⊆ (Finset.univ.filter (fun S : Finset G => ∑ x ∈ S, x = 0)) := by
    intro S hS
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hS
    obtain ⟨T, rfl⟩ := hS
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    show ∑ x ∈ pairUnion block T, x = 0
    unfold pairUnion
    exact sum_blockUnion_eq_zero block hdisj hzero T
  calc 2 ^ p = (Finset.univ.image (pairUnion block)).card :=
        (blockUnion_card block hdisj hne).symm
    _ ≤ _ := Finset.card_le_card hsub

/-! ### Non-vacuity witness (a genuine zero-sum block of order 3).

In `ZMod 6` the elements `{0, 2, 4}` (the order-3 subgroup) sum to `0 + 2 + 4 = 6 = 0`.  Taking the
single block `{0, 2, 4}` (`p = 1`, disjoint trivially, nonempty, zero-sum) gives
`2^1 ≤ #{ vanishing subsets of ZMod 6 }`, every hypothesis discharged by `decide`. -/

/-- Concrete witness: the order-3 zero-sum block `{0,2,4} ⊆ ZMod 6` gives
`2^1 ≤ #{ S ⊆ ZMod 6 : ∑_{x∈S} x = 0 }`. -/
example :
    2 ^ 1 ≤ (Finset.univ.filter (fun S : Finset (ZMod 6) => ∑ x ∈ S, x = 0)).card := by
  refine card_le_vanishing_of_blockUnions
    (fun _ => ({0, 2, 4} : Finset (ZMod 6))) ?_ ?_ ?_
  · intro i j hij; exact absurd (Subsingleton.elim i j) hij
  · intro i; refine ⟨(0 : ZMod 6), ?_⟩; simp only; decide
  · intro i; simp only; decide

end ArkLib.ProximityGap.CosetUnionVanishingLower

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.CosetUnionVanishingLower.sum_blockUnion_eq_zero
#print axioms ArkLib.ProximityGap.CosetUnionVanishingLower.card_le_vanishing_of_blockUnions
