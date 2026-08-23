/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib
import ArkLib.Data.CodingTheory.AGL24WeakPartition

/-!
# [AGL24] the vertex-degree consequence of weak partition connectivity
# (issue #346, brick 21)

The final step of the Appendix A proof uses: *since `H` is `k`-weakly-partition-connected,
considering the partition `{j} ⊔ ([t] \ {j})`, at least `k` hyperedges contain each vertex
`j`* — which is what lets the degree-`< k` agreement argument force `y = c⁽ʲ⁾`. This brick
proves that consequence on the in-tree WPC surface:

* `singletonPartition` — the two-cell partition `{{j}, univ \ {j}}`;
* `wpc_vertex_degree` — **the degree bound**: every vertex of a `k`-weakly-partition-
  connected family (on `≥ 2` vertices) lies in at least `k` edges.

(The same two-cell partition is the workhorse of several other [AGL24] arguments — the
root's in-degree bound in Corollary A.4 among them — so this is shared infrastructure.)
-/

open Finset

namespace AGL24

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The two-cell partition `{{j}, univ \ {j}}` of a type with at least two elements. -/
def singletonPartition (j : V) (h2 : 1 < Fintype.card V) :
    Finpartition (Finset.univ : Finset V) where
  parts := {{j}, Finset.univ.erase j}
  supIndep := by
    rw [Finset.supIndep_iff_pairwiseDisjoint]
    intro c₁ hc₁ c₂ hc₂ hne
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hc₁ hc₂
    rcases hc₁ with rfl | rfl <;> rcases hc₂ with rfl | rfl
    · exact absurd rfl hne
    · simp [Finset.disjoint_left]
    · simp [Finset.disjoint_right]
    · exact absurd rfl hne
  sup_parts := by
    rw [Finset.sup_insert, Finset.sup_singleton, id]
    ext x
    constructor
    · intro _
      exact Finset.mem_univ x
    · intro _
      rw [Finset.sup_eq_union, Finset.mem_union, Finset.mem_singleton]
      by_cases hx : x = j
      · exact Or.inl hx
      · exact Or.inr (by
          show x ∈ id (Finset.univ.erase j)
          rw [id, Finset.mem_erase]
          exact ⟨hx, Finset.mem_univ x⟩)
  bot_notMem := by
    rw [Finset.mem_insert, Finset.mem_singleton]
    push Not
    constructor
    · intro h
      exact absurd h.symm (Finset.singleton_ne_empty j)
    · intro h
      obtain ⟨x, hxj⟩ := Fintype.exists_ne_of_one_lt_card h2 j
      have : x ∈ Finset.univ.erase j := Finset.mem_erase.mpr ⟨hxj, Finset.mem_univ x⟩
      rw [← h] at this
      exact absurd this (Finset.notMem_empty x)

/-- **The vertex-degree bound** ([AGL24], the singleton-partition consequence): every vertex
of a `k`-weakly-partition-connected edge family on at least two vertices lies in at least `k`
edges. -/
theorem wpc_vertex_degree {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}
    (e : ι → Finset V) (h2 : 1 < Fintype.card V)
    (h : WeaklyPartitionConnected k (Finset.univ : Finset V) e) (j : V) :
    k ≤ (Finset.univ.filter (fun i => j ∈ e i)).card := by
  classical
  have hP := h (singletonPartition j h2)
  -- The partition has two parts.
  have hcard : (singletonPartition j h2).parts.card = 2 := by
    unfold singletonPartition
    rw [Finset.card_insert_of_notMem, Finset.card_singleton]
    rw [Finset.mem_singleton]
    intro heq
    obtain ⟨x, hxj⟩ := Fintype.exists_ne_of_one_lt_card h2 j
    have hx : x ∈ Finset.univ.erase j := Finset.mem_erase.mpr ⟨hxj, Finset.mem_univ x⟩
    rw [← heq, Finset.mem_singleton] at hx
    exact hxj hx
  rw [hcard] at hP
  -- Per edge: the touched-cell count exceeds one only if the edge contains j.
  have hper : ∀ i, (touchedCells (singletonPartition j h2) (e i ∩ Finset.univ)).card - 1
      ≤ (if j ∈ e i then 1 else 0) := by
    intro i
    by_cases hj : j ∈ e i
    · rw [if_pos hj]
      have : (touchedCells (singletonPartition j h2) (e i ∩ Finset.univ)).card ≤ 2 := by
        refine le_trans (Finset.card_le_card (Finset.filter_subset _ _)) ?_
        rw [hcard]
      omega
    · rw [if_neg hj]
      -- Only the erase-cell can be touched.
      have : touchedCells (singletonPartition j h2) (e i ∩ Finset.univ)
          ⊆ {Finset.univ.erase j} := by
        intro c hc
        unfold touchedCells at hc
        rw [Finset.mem_filter] at hc
        obtain ⟨hcparts, x, hx⟩ := hc
        unfold singletonPartition at hcparts
        rw [Finset.mem_insert, Finset.mem_singleton] at hcparts
        rcases hcparts with rfl | rfl
        · -- The singleton cell {j} touched: j ∈ e i, contradiction.
          rw [Finset.mem_inter, Finset.mem_inter] at hx
          obtain ⟨⟨hxe, -⟩, hxc⟩ := hx
          rw [Finset.mem_singleton] at hxc
          exact absurd (hxc ▸ hxe) hj
        · exact Finset.mem_singleton_self _
      have hle := Finset.card_le_card this
      rw [Finset.card_singleton] at hle
      omega
  calc k = k * (2 - 1) := by omega
  _ ≤ ∑ i, ((touchedCells (singletonPartition j h2) (e i ∩ Finset.univ)).card - 1) := hP
  _ ≤ ∑ i, (if j ∈ e i then 1 else 0) := Finset.sum_le_sum fun i _ => hper i
  _ = (Finset.univ.filter (fun i => j ∈ e i)).card := by
      rw [Finset.card_filter]

end AGL24

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms AGL24.wpc_vertex_degree
