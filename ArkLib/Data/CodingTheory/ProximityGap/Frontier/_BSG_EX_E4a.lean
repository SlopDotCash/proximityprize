/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BSG_DRC1
import Mathlib.Algebra.Group.Pointwise.Finset.Basic

/-!
# BSG / DRC — E4a: the difference-representation count identity

This file proves **E4a** (`diffReps_sum_eq_card_sq`), a building block of the `E4`
step of `BareDRCExtract`:

For a finite set `A''` in an additive commutative group, letting
`r d := #{p ∈ A'' ×ˢ A'' | p.1 - p.2 = d}` count the ordered pairs whose difference is `d`,
we have
`∑ d ∈ A'' - A'', r d = #A'' ^ 2`.

This is a pure fiberwise double-count of `A'' ×ˢ A''` over the difference map
`p ↦ p.1 - p.2`, whose image lands in the pointwise difference set `A'' - A''`. It supplies the
numerator `(#A'')²` that the per-difference lower bound `r d ≥ t` (E4b) divides into to yield
`#(A'' - A'') ≤ (#A'')² / t`.

It mirrors the cherry double-count `sum_rDeg_sq_eq_sum_commonNeighbors` already proven in
`_BSG_DRC1`.
-/

open Finset
open scoped BigOperators Pointwise

namespace Finset.BSG

variable {α : Type*} [AddCommGroup α] [DecidableEq α]

/-- **E4a — difference-representation count identity.** For a finite set `A''`, the number of
ordered pairs `(a, a') ∈ A'' ×ˢ A''` with `a - a' = d`, summed over all differences
`d ∈ A'' - A''`, equals `#A'' ^ 2` — the total number of ordered pairs.

Proof: a fiberwise double-count of `A'' ×ˢ A''` over the difference map `p ↦ p.1 - p.2`, which
maps into the pointwise difference set `A'' - A''` (`sub_mem_sub`). -/
theorem diffReps_sum_eq_card_sq (A'' : Finset α) :
    ∑ d ∈ A'' - A'', #{p ∈ A'' ×ˢ A'' | p.1 - p.2 = d} = #A'' ^ 2 := by
  classical
  -- The difference map sends every pair in `A'' ×ˢ A''` into `A'' - A''`.
  have hmaps : ((A'' ×ˢ A'' : Finset (α × α)) : Set (α × α)).MapsTo
      (fun p : α × α => p.1 - p.2) ((A'' - A'' : Finset α) : Set α) := by
    intro p hp
    rw [Finset.mem_coe, Finset.mem_product] at hp
    exact Finset.mem_coe.mpr (Finset.sub_mem_sub hp.1 hp.2)
  -- Fiberwise count: `#(A'' ×ˢ A'') = ∑_{d ∈ A''-A''} #{p | p.1 - p.2 = d}`.
  have hfib := Finset.card_eq_sum_card_fiberwise (f := fun p : α × α => p.1 - p.2)
    (s := A'' ×ˢ A'') (t := A'' - A'') hmaps
  rw [hfib.symm, Finset.card_product, sq]

#print axioms Finset.BSG.diffReps_sum_eq_card_sq

end Finset.BSG
