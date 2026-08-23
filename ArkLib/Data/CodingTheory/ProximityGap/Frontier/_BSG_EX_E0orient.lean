/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BSG_DRC1

/-!
# BSG `EX` E0-orient — the size datum of `BareDRCExtract`, restated on `leftNbhd`

This file proves the **size half** of the `BareDRCExtract` extraction (sub-lemma `E0/E1`): the
good-vertex hypothesis `#A ≤ 4K²·rDeg A G b₀` re-expressed on the **left-neighbourhood**
`N = leftNbhd A G b₀` as `#A ≤ 4K²·#N`. This is the datum the extraction stage consumes to set
`A' = N` and certify a size lower bound on `A'`.

## Why this is `rfl`-trivial

`Finset.BSG.card_leftNbhd : #(leftNbhd A G b) = rDeg A G b` holds by `rfl` (the neighbourhood is the
filter `{a ∈ A | (a,b) ∈ G}`, whose card is exactly `rDeg`). So the conclusion `#A ≤ 4K²·#N` is
*definitionally* the hypothesis `#A ≤ 4K²·rDeg A G b₀`; we `simpa [card_leftNbhd]`.

## Constant-tracking flag (resolved downstream, recorded here)

The `BareDRCExtract` conclusion demands `C₁ * K * #A' ≥ #A` for a **fixed** `ℕ` constant `C₁`.
With `A' = N` and `#A ≤ 4K²·#N` we obtain `#A ≤ (4K)·K·#N`, i.e. the bound holds with the
*`K`-dependent* coefficient `4K`, NOT a fixed `C₁`. Equivalently `#A' ≥ #A/(4K²)`, weaker by a
factor `K` than the `#A' ≥ #A/(C₁K)` a fixed `C₁` would give. This is the genuine constant-tracking
subtlety that `E5` (assembly) must resolve — either the downstream `bsgCore_of_bareDRC` tolerates
`#A' ≥ #A/(4K²)`, or the extraction refines differently. This file only certifies the raw size
datum; it makes no claim about a fixed-`C₁` size bound.

## Status

`E0-ORIENT-PROVEN` — builds axiom-clean (`propext, Classical.choice, Quot.sound`; no `sorryAx`).
The size datum of `BareDRCExtract`, restated on `leftNbhd`. This is `E0/E1` of the extraction DAG,
not the full extraction (the difference bound `#(A'-A') ≤ C₂K^c·#A'` is `E2`–`E5`).
-/

open Finset

namespace Finset.BSG

variable {α : Type*} [AddCommGroup α] [DecidableEq α]

/-- **E0-orient — the size datum of `BareDRCExtract`, restated on `leftNbhd`.**

The good-vertex hypothesis `#A ≤ 4K²·rDeg A G b₀` is *definitionally* `#A ≤ 4K²·#(leftNbhd A G b₀)`,
since `card_leftNbhd : #(leftNbhd A G b) = rDeg A G b` is `rfl`. This is the size half of the
extraction: with `A' = leftNbhd A G b₀`, it gives `#A ≤ 4K²·#A'`, hence `#A' ≥ #A/(4K²)`. -/
theorem card_leftNbhd_ge_of_good (A : Finset α) (K : ℕ) (G : Finset (α × α)) (b₀ : α)
    (hgood : #A ≤ 4 * K ^ 2 * rDeg A G b₀) :
    #A ≤ 4 * K ^ 2 * #(leftNbhd A G b₀) := by
  simpa [card_leftNbhd] using hgood

/-- **`leftNbhd ⊆ A`.** The left-neighbourhood is a filter on `A`, hence a subset of `A`. This is
the trivial subset datum the extraction uses to certify `A' ⊆ A`. -/
lemma leftNbhd_subset (A : Finset α) (G : Finset (α × α)) (b : α) :
    leftNbhd A G b ⊆ A :=
  Finset.filter_subset _ _

end Finset.BSG

-- Axiom audit (expected: propext, Classical.choice, Quot.sound — and NO sorryAx).
#print axioms Finset.BSG.card_leftNbhd_ge_of_good
#print axioms Finset.BSG.leftNbhd_subset
