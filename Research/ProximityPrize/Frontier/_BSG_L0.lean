/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Combinatorics.Additive.Energy
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Data.Rat.Cast.Defs

/-!
# `BSG L0`: definitional scaffold for Balog–Szemerédi–Gowers (additive-energy form)

This is the foundational (L0) layer of the in-tree BSG attack. It introduces the three
definitions every downstream BSG lemma references:

* `repCount A x` — the difference representation function `r(x) = #{(a,b) ∈ A × A : a - b = x}`.
* `popularDiffs A K` — the set `P` of *popular* differences, those `x ∈ A - A` whose
  representation count clears the threshold `|A| / (2K)`.
* `popularGraph A K` — the bipartite "popular" graph `H ⊆ A × A`, whose edges are exactly the
  pairs whose difference is popular.

These are pure `def`s (no proof obligation); they only require `DecidableEq α` to form the
`Finset.filter`s. The rational threshold `|A| / (2K)` is taken in `ℚ` to avoid `ℕ`-division
artefacts. A couple of trivially-true sanity `example`s are included to lock the membership
characterisations that downstream lemmas (L1a, L2, L3, …) unfold.
-/

set_option linter.style.longLine false
set_option autoImplicit false


namespace ArkLib.BSG

open Finset
open scoped Pointwise

variable {α : Type*} [AddCommGroup α] [DecidableEq α]

/-- The difference representation function: `repCount A x = r(x)` counts ordered pairs
`(a, b) ∈ A × A` with `a - b = x`. -/
def repCount (A : Finset α) (x : α) : ℕ :=
  #{p ∈ A ×ˢ A | p.1 - p.2 = x}

/-- The set of *popular* differences `P`: differences `x ∈ A - A` whose representation count
`repCount A x` clears the threshold `|A| / (2K)` (compared in `ℚ`). -/
def popularDiffs (A : Finset α) (K : ℚ) : Finset α :=
  {x ∈ (A - A) | (#A : ℚ) / (2 * K) ≤ (repCount A x : ℚ)}

/-- The *popular* bipartite graph `H ⊆ A × A`: an edge `(a, b)` is present iff its difference
`a - b` is a popular difference. -/
def popularGraph (A : Finset α) (K : ℚ) : Finset (α × α) :=
  {p ∈ A ×ˢ A | p.1 - p.2 ∈ popularDiffs A K}

/-- Membership in `repCount`'s underlying fiber, unfolded. -/
theorem mem_repCount_filter (A : Finset α) (x : α) (p : α × α) :
    p ∈ {p ∈ A ×ˢ A | p.1 - p.2 = x} ↔ (p.1 ∈ A ∧ p.2 ∈ A) ∧ p.1 - p.2 = x := by
  simp [Finset.mem_filter, Finset.mem_product, and_assoc]

/-- Characterisation of membership in `popularDiffs`. -/
theorem mem_popularDiffs (A : Finset α) (K : ℚ) (x : α) :
    x ∈ popularDiffs A K ↔ x ∈ A - A ∧ (#A : ℚ) / (2 * K) ≤ (repCount A x : ℚ) := by
  simp [popularDiffs, Finset.mem_filter]

/-- Characterisation of membership in `popularGraph`. -/
theorem mem_popularGraph (A : Finset α) (K : ℚ) (p : α × α) :
    p ∈ popularGraph A K ↔ (p.1 ∈ A ∧ p.2 ∈ A) ∧ p.1 - p.2 ∈ popularDiffs A K := by
  simp [popularGraph, Finset.mem_filter, Finset.mem_product, and_assoc]

/-- The popular graph is a subgraph of the complete bipartite graph `A × A`. -/
theorem popularGraph_subset (A : Finset α) (K : ℚ) :
    popularGraph A K ⊆ A ×ˢ A := by
  intro p hp
  rw [mem_popularGraph] at hp
  exact Finset.mem_product.mpr hp.1

/-- The popular differences are a subset of the difference set `A - A`. -/
theorem popularDiffs_subset (A : Finset α) (K : ℚ) :
    popularDiffs A K ⊆ A - A := by
  intro x hx
  exact ((mem_popularDiffs A K x).mp hx).1

end ArkLib.BSG
