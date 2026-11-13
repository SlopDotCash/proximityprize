/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.Combinatorics.Additive.BalogSzemerediGowers
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# BSG `DRC0` — the averaging / second-moment pigeonhole substrate of dependent random choice

This file builds the **first half** of the bare dependent-random-choice (`BareDRC`) extraction
that the reduction `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_BSG_Reduce.lean` reduces
`Finset.BSGCore` to: the *averaging / expectation* setup and the *pigeonhole existence of a good
right-vertex*.

## Where this sits in DRC

`BareDRC` is handed a bipartite graph `G ⊆ A ×ˢ A` that is **edge-dense**
(`#A² ≤ 4K²·#G`) and **cherry-rich** (`#A⁴ ≤ 16K⁴·(#A·∑_b deg(b)²)`). The dependent-random-choice
proof selects a *good* right-vertex `b` whose neighbourhood `N(b) = {a ∈ A | (a,b) ∈ G}` is large,
using the **second moment** `∑_b deg(b)²` rather than the first moment `∑_b deg(b) = #G`. The whole
selection is a pigeonhole on the second moment.

This file proves the *graph-combinatorial backbone* of that selection, with **no additive-energy
content** and **no `sorry`**:

* `rDeg` — the right-degree `#{a ∈ A | (a,b) ∈ G}` (matching `_BSG_Reduce`).
* `card_eq_sum_rDeg` — first-moment identity `#G = ∑_{b∈A} deg(b)` (local re-proof of the
  `_BSG_Reduce` lemma so this file is import-light).
* `cherryCount` — the number of *cherries* (length-2 paths through a right vertex):
  `#{(a, a', b) ∈ A × A × A | (a,b) ∈ G ∧ (a',b) ∈ G}`.
* `cherryCount_eq_sum_rDeg_sq` — second-moment identity `cherryCount = ∑_{b∈A} deg(b)²`.
* `exists_good_vertex_deg` — **first-moment averaging pigeonhole**: there is `b ∈ A` with
  `#A · deg(b) ≥ #G` (a vertex of at-least-average degree).
* `exists_good_vertex_deg_sq` — **second-moment averaging pigeonhole** (the DRC selection rule):
  there is `b ∈ A` with `#A · deg(b)² ≥ ∑_{b'∈A} deg(b')²` (a vertex of at-least-average
  *squared* degree, i.e. the one DRC picks).
* `exists_good_vertex_drc` — the packaged DRC selection: under edge-density + cherry-richness,
  a right-vertex `b` whose squared degree dominates the average, hence (chaining the two density
  hypotheses) whose **degree is `≥ #A/(2K·…)`** scale — stated as the explicit lower bound on
  `#A · deg(b)²` that the *next* DRC stage (neighbourhood refinement, a separate residual)
  consumes.

The remaining DRC content — turning the good vertex's neighbourhood into the small-doubling subset
`A'` via Plünnecke — is **not** in this file; it is the second half of `BareDRC` and stays an open
named residual.

## Status

`DRC0-PROVEN` — all theorems below build axiom-clean (`propext, Classical.choice, Quot.sound`;
no `sorryAx`). This is the averaging/pigeonhole backbone of `BareDRC`, not the full extraction.
-/

open Finset
open scoped BigOperators Pointwise

namespace ArkLib.BSG.DRC0

variable {α : Type*} [AddCommGroup α] [DecidableEq α]

/-- The **right-degree** of a vertex `b` in a graph `G ⊆ A × A`: the number of `a ∈ A` with
`(a, b) ∈ G`. (Matches `Finset.BSG.rDeg` in `_BSG_Reduce`.) -/
noncomputable def rDeg (A : Finset α) (G : Finset (α × α)) (b : α) : ℕ :=
  #{a ∈ A | (a, b) ∈ G}

/-! ## First moment: `#G = ∑_b deg(b)` -/

/-- **First-moment identity.** The edge count of `G ⊆ A ×ˢ A` is the sum of right-degrees:
`#G = ∑_{b ∈ A} deg(b)`. Pure fiberwise double-count over the second-coordinate map `p ↦ p.2`.
(Local re-proof of `Finset.BSG.card_eq_sum_rDeg` to keep this file import-light.) -/
theorem card_eq_sum_rDeg (A : Finset α) (G : Finset (α × α)) (hG : G ⊆ A ×ˢ A) :
    #G = ∑ b ∈ A, rDeg A G b := by
  classical
  simp only [rDeg]
  rw [Finset.card_eq_sum_card_fiberwise (f := fun p : α × α => p.2) (s := G) (t := A)
        (fun p hp => (Finset.mem_product.1 (hG hp)).2)]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  refine Finset.card_bij' (fun p _ => p.1) (fun a _ => (a, b)) ?_ ?_ ?_ ?_
  · rintro ⟨x, y⟩ hp
    simp only [mem_filter] at hp ⊢
    obtain ⟨hxG, hyb⟩ := hp
    refine ⟨(Finset.mem_product.1 (hG hxG)).1, ?_⟩
    have hy : y = b := hyb
    subst hy
    exact hxG
  · intro a ha
    simp only [mem_filter] at ha ⊢
    refine ⟨ha.2, ?_⟩
    trivial
  · rintro ⟨x, y⟩ hp
    simp only [mem_filter] at hp
    obtain ⟨_, hyb⟩ := hp
    simp only [hyb]
  · intro a _; rfl

/-! ## Second moment: the cherry count -/

/-- The **cherry count** of `G ⊆ A × A`: the number of ordered length-2 paths through a right
vertex, i.e. triples `(a, a', b) ∈ A × A × A` with `(a, b) ∈ G` and `(a', b) ∈ G`. This is the
second-moment graph quantity that dependent random choice selects on. -/
noncomputable def cherryCount (A : Finset α) (G : Finset (α × α)) : ℕ :=
  #{t ∈ A ×ˢ A ×ˢ A | (t.1, t.2.2) ∈ G ∧ (t.2.1, t.2.2) ∈ G}

/-- **Second-moment identity.** The cherry count equals the sum of squared right-degrees:
`cherryCount A G = ∑_{b ∈ A} deg(b)²`. Fiberwise double-count of the cherry triples over their
centre `b = t.2.2`; the fiber over `b` is `N(b) ×ˢ N(b)` with card `deg(b)²`. -/
theorem cherryCount_eq_sum_rDeg_sq (A : Finset α) (G : Finset (α × α)) :
    cherryCount A G = ∑ b ∈ A, rDeg A G b ^ 2 := by
  classical
  unfold cherryCount
  -- Fiber the cherry-triples over their centre `b = t.2.2`.
  rw [Finset.card_eq_sum_card_fiberwise
        (f := fun t : α × α × α => t.2.2)
        (s := {t ∈ A ×ˢ A ×ˢ A | (t.1, t.2.2) ∈ G ∧ (t.2.1, t.2.2) ∈ G})
        (t := A)
        (fun t ht => by
          have ht' := (Finset.mem_filter.1 ht).1
          exact (Finset.mem_product.1 (Finset.mem_product.1 ht').2).2)]
  refine Finset.sum_congr rfl (fun b hbA => ?_)
  -- The fiber over `b` is in bijection with `N(b) ×ˢ N(b)`.
  simp only [rDeg, sq]
  -- goal: #(fiber over b) = #{a ∈ A | (a,b)∈G} * #{a' ∈ A | (a',b)∈G}, i.e. card of a product.
  rw [← Finset.card_product]
  refine Finset.card_bij'
    (fun t _ => (t.1, t.2.1))
    (fun p _ => (p.1, p.2, b))
    ?_ ?_ ?_ ?_
  · -- forward maps fiber-element into `N(b) ×ˢ N(b)`
    rintro ⟨x, y, z⟩ ht
    rw [Finset.mem_filter] at ht
    obtain ⟨hmem, hzb⟩ := ht
    -- `hzb : (x,y,z).2.2 = b`, i.e. `z = b`
    rw [Finset.mem_filter] at hmem
    obtain ⟨hprod, hxz, hyz⟩ := hmem
    rw [Finset.mem_product, Finset.mem_product] at hprod
    obtain ⟨hxA, hyA, _hzA⟩ := hprod
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter]
    simp only at hzb
    subst hzb
    exact ⟨⟨hxA, hxz⟩, ⟨hyA, hyz⟩⟩
  · -- backward maps `N(b) ×ˢ N(b)` into the fiber
    rintro ⟨x, y⟩ hp
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter] at hp
    obtain ⟨⟨hxA, hxz⟩, ⟨hyA, hyz⟩⟩ := hp
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_product, Finset.mem_product]
    exact ⟨⟨⟨hxA, hyA, hbA⟩, hxz, hyz⟩, rfl⟩
  · -- left inverse: `(t.1, t.2.1, b) = t` for `t` in the fiber (since `t.2.2 = b`)
    rintro ⟨x, y, z⟩ ht
    rw [Finset.mem_filter] at ht
    have hzb : z = b := ht.2
    simp only [hzb]
  · -- right inverse: `((p.1, p.2, b).1, (p.1, p.2, b).2.1) = p`
    intro p _; rfl

/-! ## Averaging pigeonhole: existence of a good right-vertex -/

/-- **First-moment averaging pigeonhole.** A graph `G ⊆ A ×ˢ A` over a nonempty `A` has a
right-vertex `b ∈ A` of at-least-average degree: `#A · deg(b) ≥ #G`.

Proof: if every `b` had `#A · deg(b) < #G`, summing over the `#A` vertices would give
`#A · ∑_b deg(b) < #A · #G`, i.e. `#A · #G < #A · #G` (using `∑_b deg(b) = #G`). -/
theorem exists_good_vertex_deg (A : Finset α) (G : Finset (α × α)) (hG : G ⊆ A ×ˢ A)
    (hA : A.Nonempty) :
    ∃ b ∈ A, #G ≤ #A * rDeg A G b := by
  classical
  by_contra hcon
  push_neg at hcon
  -- `∀ b ∈ A, #A * deg(b) < #G`. Sum the strict inequalities.
  have hsum : ∑ b ∈ A, #A * rDeg A G b < ∑ b ∈ A, #G :=
    Finset.sum_lt_sum_of_nonempty hA (fun b hb => hcon b hb)
  rw [← Finset.mul_sum, ← card_eq_sum_rDeg A G hG, Finset.sum_const, smul_eq_mul] at hsum
  -- `#A * #G < #A * #G`
  rw [mul_comm (#A) (#G)] at hsum
  exact lt_irrefl _ hsum

/-- **Second-moment averaging pigeonhole (the DRC selection rule).** A graph `G ⊆ A ×ˢ A` over a
nonempty `A` has a right-vertex `b ∈ A` whose *squared* degree is at least average:
`#A · deg(b)² ≥ ∑_{b' ∈ A} deg(b')² = cherryCount A G`.

This is the vertex that dependent random choice selects: maximizing the squared degree (equivalently
the number of cherries through `b`) is what makes the expected number of "bad" neighbourhood pairs
small. -/
theorem exists_good_vertex_deg_sq (A : Finset α) (G : Finset (α × α)) (hA : A.Nonempty) :
    ∃ b ∈ A, ∑ b' ∈ A, rDeg A G b' ^ 2 ≤ #A * rDeg A G b ^ 2 := by
  classical
  by_contra hcon
  push_neg at hcon
  have hsum : ∑ b ∈ A, #A * rDeg A G b ^ 2 < ∑ _b ∈ A, ∑ b' ∈ A, rDeg A G b' ^ 2 :=
    Finset.sum_lt_sum_of_nonempty hA (fun b hb => hcon b hb)
  rw [← Finset.mul_sum, Finset.sum_const, smul_eq_mul] at hsum
  exact lt_irrefl _ hsum

/-! ## The packaged DRC selection (averaging stage output) -/

/-- **The packaged averaging-stage output of `BareDRC`.** Under the two density hypotheses that
`BareDRC` is handed — edge-density `#A² ≤ 4K²·#G` and cherry-richness
`#A⁴ ≤ 16K⁴·(#A·∑_b deg(b)²)` — dependent random choice's second-moment pigeonhole produces a
right-vertex `b ∈ A` with a **quantitative squared-degree lower bound**:
`#A⁴ ≤ 16K⁴·#A²·deg(b)²`.

This is exactly the averaging/expectation conclusion the *next* DRC stage (neighbourhood
refinement → small-doubling subset, a separate residual) consumes: it certifies that the selected
vertex's neighbourhood `N(b)` has size `deg(b) ≳ #A/(4K²)` scale.

Proof: feed cherry-richness into `exists_good_vertex_deg_sq`. -/
theorem exists_good_vertex_drc (A : Finset α) (K : ℕ) (G : Finset (α × α)) (hA : A.Nonempty)
    (hcherry : #A ^ 4 ≤ 16 * K ^ 4 * (#A * ∑ b ∈ A, rDeg A G b ^ 2)) :
    ∃ b ∈ A, #A ^ 4 ≤ 16 * K ^ 4 * (#A * (#A * rDeg A G b ^ 2)) := by
  classical
  obtain ⟨b, hbA, hb⟩ := exists_good_vertex_deg_sq A G hA
  refine ⟨b, hbA, ?_⟩
  calc #A ^ 4 ≤ 16 * K ^ 4 * (#A * ∑ b' ∈ A, rDeg A G b' ^ 2) := hcherry
    _ ≤ 16 * K ^ 4 * (#A * (#A * rDeg A G b ^ 2)) := by
        apply Nat.mul_le_mul_left
        exact Nat.mul_le_mul_left _ hb

end ArkLib.BSG.DRC0

-- Axiom audit (expected: propext, Classical.choice, Quot.sound — and NO sorryAx).
#print axioms ArkLib.BSG.DRC0.card_eq_sum_rDeg
#print axioms ArkLib.BSG.DRC0.cherryCount_eq_sum_rDeg_sq
#print axioms ArkLib.BSG.DRC0.exists_good_vertex_deg
#print axioms ArkLib.BSG.DRC0.exists_good_vertex_deg_sq
#print axioms ArkLib.BSG.DRC0.exists_good_vertex_drc
