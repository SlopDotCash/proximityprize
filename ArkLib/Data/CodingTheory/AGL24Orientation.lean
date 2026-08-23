/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib

/-!
# [AGL24] Appendix A: the orientation-counting core of Corollary A.4 (issue #346, brick 19)

Corollary A.4 turns an orientation of a `k`-weakly-partition-connected hypergraph (Theorem
A.3 — Frank's orientation theorem, the appendix's deep combinatorial input) into a generic
zero pattern. The counting layer above the orientation is elementary and is proven here:

* `HeadOrientation` — an orientation assigns each hyperedge a head among its vertices;
  `HeadOrientation.updateHead` changes one edge head while preserving membership;
  `inDegree` counts heads;
* `HeadOrientation.updateHead` — a one-edge reheading primitive for the Frank
  reorientation campaign;
* `card_induced_le_card_heads` — edges induced by a vertex set have their heads inside it
  (the Case-2 count of (A.3));
* `card_induced_le_card_heads_sub` — **the Case-1 count**: with `k` crossing edges (heads
  inside `T`, vertex sets leaving `T` — supplied downstream by the `k` edge-disjoint paths
  to the root), the induced count drops by `k`;
* `sum_inDegree` — the in-degrees sum to the edge count (the `∑ δⱼ = n − k` bookkeeping).

Theorem A.3 itself (every `k`-weakly-partition-connected hypergraph has an orientation with
`k` edge-disjoint paths from every vertex to a root) remains the appendix's named deep input,
alongside GM-MDS (Theorem A.2).
-/

open Finset

namespace AGL24

variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [Fintype V] [DecidableEq V]

/-- An orientation of a hypergraph: each edge gets a head among its vertices. -/
structure HeadOrientation (e : ι → Finset V) where
  head : ι → V
  head_mem : ∀ i, (e i).Nonempty → head i ∈ e i

omit [Fintype ι] [DecidableEq ι] [Fintype V] [DecidableEq V] in
/-- Update one edge head to a chosen vertex of that edge. -/
noncomputable def HeadOrientation.updateHead {e : ι → Finset V} (O : HeadOrientation e)
    (i₀ : ι) (v : V) (hv : v ∈ e i₀) : HeadOrientation e := by
  letI : DecidableEq ι := Classical.decEq ι
  exact
    { head := fun i => if i = i₀ then v else O.head i
      head_mem := by
        intro i hne
        by_cases hi : i = i₀
        · subst hi
          simpa using hv
        · simp [hi, O.head_mem i hne] }

omit [Fintype ι] [DecidableEq ι] [Fintype V] [DecidableEq V] in
@[simp] theorem HeadOrientation.updateHead_head_self {e : ι → Finset V}
    (O : HeadOrientation e) (i₀ : ι) (v : V) (hv : v ∈ e i₀) :
    (O.updateHead i₀ v hv).head i₀ = v := by
  letI : DecidableEq ι := Classical.decEq ι
  simp [HeadOrientation.updateHead]

omit [Fintype ι] [DecidableEq ι] [Fintype V] [DecidableEq V] in
@[simp] theorem HeadOrientation.updateHead_head_of_ne {e : ι → Finset V}
    (O : HeadOrientation e) {i₀ j : ι} (v : V) (hv : v ∈ e i₀) (hji : j ≠ i₀) :
    (O.updateHead i₀ v hv).head j = O.head j := by
  letI : DecidableEq ι := Classical.decEq ι
  simp [HeadOrientation.updateHead, hji]

/-- The in-degree of a vertex: the number of edges oriented into it. -/
def HeadOrientation.inDegree {e : ι → Finset V} (O : HeadOrientation e) (j : V) : ℕ :=
  (Finset.univ.filter (fun i => O.head i = j)).card

/-- The in-degrees sum to the number of edges. -/
theorem HeadOrientation.sum_inDegree {e : ι → Finset V} (O : HeadOrientation e) :
    ∑ j, O.inDegree j = Fintype.card ι := by
  unfold HeadOrientation.inDegree
  rw [← Finset.card_univ (α := ι)]
  exact (Finset.card_eq_sum_card_fiberwise
    (f := O.head) (t := Finset.univ) (fun i _ => Finset.mem_univ _)).symm

/-- **The Case-2 count of (A.3)**: every nonempty edge induced by `T` has its head in `T`,
so the induced count is at most the head count. -/
theorem card_induced_le_card_heads {e : ι → Finset V} (O : HeadOrientation e)
    (T : Finset V) (hne : ∀ i, (e i).Nonempty) :
    (Finset.univ.filter (fun i => e i ⊆ T)).card
      ≤ (Finset.univ.filter (fun i => O.head i ∈ T)).card := by
  refine Finset.card_le_card ?_
  intro i hi
  rw [Finset.mem_filter] at hi ⊢
  exact ⟨Finset.mem_univ _, hi.2 (O.head_mem i (hne i))⟩

/-- **The Case-1 count of (A.3)**: if at least `k` edges have their head in `T` but vertex
set not contained in `T` (the crossing edges supplied by the `k` edge-disjoint paths to a
root outside `T`), then the induced count is at most the head count minus `k`. -/
theorem card_induced_le_card_heads_sub {e : ι → Finset V} (O : HeadOrientation e)
    (T : Finset V) (k : ℕ) (hne : ∀ i, (e i).Nonempty)
    (hcross : k ≤ (Finset.univ.filter (fun i => O.head i ∈ T ∧ ¬ e i ⊆ T)).card) :
    (Finset.univ.filter (fun i => e i ⊆ T)).card
      ≤ (Finset.univ.filter (fun i => O.head i ∈ T)).card - k := by
  classical
  -- The heads-in-T set splits into induced and crossing parts.
  have hsplit : (Finset.univ.filter (fun i => O.head i ∈ T ∧ e i ⊆ T)).card
      + (Finset.univ.filter (fun i => O.head i ∈ T ∧ ¬ e i ⊆ T)).card
      = (Finset.univ.filter (fun i => O.head i ∈ T)).card := by
    rw [← Finset.filter_filter, ← Finset.filter_filter]
    exact Finset.filter_card_add_filter_neg_card_eq_card (fun i => e i ⊆ T)
  -- Induced edges all have heads in T.
  have hsub : (Finset.univ.filter (fun i => e i ⊆ T)).card
      ≤ (Finset.univ.filter (fun i => O.head i ∈ T ∧ e i ⊆ T)).card := by
    refine Finset.card_le_card ?_
    intro i hi
    rw [Finset.mem_filter] at hi ⊢
    exact ⟨Finset.mem_univ _, hi.2 (O.head_mem i (hne i)), hi.2⟩
  omega

end AGL24

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms AGL24.HeadOrientation.updateHead
#print axioms AGL24.HeadOrientation.sum_inDegree
#print axioms AGL24.HeadOrientation.updateHead
#print axioms AGL24.card_induced_le_card_heads
#print axioms AGL24.card_induced_le_card_heads_sub
