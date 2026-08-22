/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Combinatorics.Additive.Energy
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import ArkLib.ToMathlib.Combinatorics.Additive.BalogSzemerediGowers

/-!
# BSG lemma L3 — popular-graph edge count equals the popular representation sum

Scratch file for the Balog–Szemerédi–Gowers (BSG) formalization (issue #334 / #444).

This file proves **L3** in the *difference form* of the BSG decomposition:

> `popularGraph_card_eq_sum_popular_repCount` —
> `#(popularGraph A K) = ∑ x ∈ popularDiffs A K, repCount A x`.

The popular graph `H = popularGraph A K` is the set of ordered pairs `(a, b) ∈ A × A` whose
*difference* `a - b` is a **popular difference** (one with many representations). Its edge set
fibers over the popular differences, and the fiber over `x` has exactly `repCount A x` elements (the
representation count of `x`). The lemma is therefore a pure double-count, discharged by Mathlib's
fiberwise-card identity `Finset.sum_card_fiberwise_eq_card_filter`.

## Scaffolding (the difference-form L0 defs)

* `repCount A x` — the **difference-representation count** `#{(a,b) ∈ A×A : a - b = x}`.
* `popularDiffs A K` — the **popular differences** `{x ∈ A - A : (#A : ℚ)/(2K) ≤ repCount A x}`.
* `popularGraph A K` — the **popular graph** `{(a,b) ∈ A×A : a - b ∈ popularDiffs A K}`.

## Status

`L3-FULLY-PROVEN` (axiom-clean: the file's only axioms are the Lean/Mathlib standard trio).
-/

open Finset
open scoped BigOperators Pointwise

namespace ArkLib.BSG.L3

variable {α : Type*} [AddCommGroup α] [DecidableEq α]

/-- The **difference-representation count** of `x` in `A`: the number of ordered pairs
`(a, b) ∈ A × A` with `a - b = x`. -/
noncomputable def repCount (A : Finset α) (x : α) : ℕ :=
  #{p ∈ A ×ˢ A | p.1 - p.2 = x}

lemma repCount_def (A : Finset α) (x : α) :
    repCount A x = #{p ∈ A ×ˢ A | p.1 - p.2 = x} := rfl

/-- The **popular differences**: differences `x ∈ A - A` whose representation count is at least
`#A / (2K)`. A rational threshold is used to avoid `ℕ`-division. -/
noncomputable def popularDiffs (A : Finset α) (K : ℚ) : Finset α :=
  {x ∈ A - A | (#A : ℚ) / (2 * K) ≤ (repCount A x : ℚ)}

lemma mem_popularDiffs {A : Finset α} {K : ℚ} {x : α} :
    x ∈ popularDiffs A K ↔ x ∈ A - A ∧ (#A : ℚ) / (2 * K) ≤ (repCount A x : ℚ) := by
  simp [popularDiffs]

/-- The **popular graph** `H`: the ordered pairs `(a, b) ∈ A × A` whose difference `a - b` is a
popular difference. -/
noncomputable def popularGraph (A : Finset α) (K : ℚ) : Finset (α × α) :=
  {p ∈ A ×ˢ A | p.1 - p.2 ∈ popularDiffs A K}

lemma mem_popularGraph {A : Finset α} {K : ℚ} {p : α × α} :
    p ∈ popularGraph A K ↔ p ∈ A ×ˢ A ∧ p.1 - p.2 ∈ popularDiffs A K := by
  simp [popularGraph]

/-- Popular differences lie in the difference set `A - A`. -/
lemma popularDiffs_subset (A : Finset α) (K : ℚ) : popularDiffs A K ⊆ A - A :=
  Finset.filter_subset _ _

/-- **L3 (edge-count identity).** The popular graph's edge set fibers over its popular differences,
the fiber over `x` having exactly `repCount A x` elements, so

`#(popularGraph A K) = ∑ x ∈ popularDiffs A K, repCount A x`.

Pure double-count via `Finset.sum_card_fiberwise_eq_card_filter` with the difference map
`p ↦ p.1 - p.2` fibering `A ×ˢ A` over `popularDiffs A K`. -/
theorem popularGraph_card_eq_sum_popular_repCount (A : Finset α) (K : ℚ) :
    #(popularGraph A K) = ∑ x ∈ popularDiffs A K, repCount A x := by
  classical
  -- Unfold `repCount` so each summand is a fiber-card of the difference map over `A ×ˢ A`.
  simp_rw [repCount]
  -- The fiberwise-card identity: ∑_{x ∈ t} #{p ∈ s | g p = x} = #{p ∈ s | g p ∈ t}.
  rw [Finset.sum_card_fiberwise_eq_card_filter (A ×ˢ A) (popularDiffs A K)
        (fun p : α × α => p.1 - p.2)]
  -- The right-hand filter is exactly the popular graph.
  rfl

/-! ## Sum form — the canonical L3 against the live BSG substrate

The lemma above is the *difference* form, with its own self-contained scaffolding. The BSG pipeline
in `ArkLib.ToMathlib.Combinatorics.Additive.BalogSzemerediGowers` is built on the *sum*-
representation count `Finset.rAdd A c = #{(a,b) ∈ A×A : a+b = c}` and the proven energy lemma
`Finset.popularSum_carries_half_energy`. The version below is the exact assigned L3 target
`popularGraph_edge_count_ge`, stated directly against that substrate: with the popular sums
`P = {c ∈ A+A | θ ≤ rAdd A c}` and the popular bipartite graph `G = {(a,b) ∈ A×A | a+b ∈ P}`,

`#G = ∑_{c ∈ P} rAdd A c`.

This is the bridge that connects `popularSum_carries_half_energy` (energy supported on `P`) to a
concrete dense graph the path-counting (L4) acts on. It is the same double-count as the in-file
`Finset.sum_rAdd_eq_card_sq`, fibering `A ×ˢ A` over the *popular* target `P` instead of all of
`A + A`. -/
theorem popularGraph_edge_count_ge (A : Finset α) (θ : ℕ) :
    #({p ∈ A ×ˢ A | (p.1 + p.2) ∈ ({c ∈ A + A | θ ≤ Finset.rAdd A c} : Finset α)})
      = ∑ c ∈ ({c ∈ A + A | θ ≤ Finset.rAdd A c} : Finset α), Finset.rAdd A c := by
  classical
  -- Each summand `rAdd A c` is, by definition, the fiber-card `#{p ∈ A×ˢA | p.1+p.2 = c}` of the
  -- sum map over `A ×ˢ A`. The fiberwise-card identity
  --   ∑_{c ∈ t} #{p ∈ s | g p = c} = #{p ∈ s | g p ∈ t}
  -- with `g = (·.1 + ·.2)`, `s = A ×ˢ A`, `t = P` is then exactly the (symmetric) goal — the
  -- LHS card `#G` is defeq to `#{p ∈ A×ˢA | p.1+p.2 ∈ P}`.
  simp only [Finset.rAdd]
  exact (Finset.sum_card_fiberwise_eq_card_filter (A ×ˢ A)
        {c ∈ A + A | θ ≤ #{p ∈ A ×ˢ A | p.1 + p.2 = c}} (fun p : α × α => p.1 + p.2)).symm

end ArkLib.BSG.L3

-- Axiom audit (expected: propext, Classical.choice, Quot.sound)
#print axioms ArkLib.BSG.L3.popularGraph_card_eq_sum_popular_repCount
#print axioms ArkLib.BSG.L3.popularGraph_edge_count_ge
