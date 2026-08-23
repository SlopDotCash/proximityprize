/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib
import ArkLib.Data.CodingTheory.AGL24Orientation

/-!
# [AGL24] Corollary A.4 in full conditional form (issue #346, brick 20)

The generic-zero-pattern condition and its derivation from an orientation — the display
(A.3) arithmetic over brick 19's counting lemmas:

* `GZPCondition` — Definition A.1's condition (A.2) in multiplicity-function form, stated
  additively (`induced + ∑κ + k ≤ n`) to avoid ℕ-subtraction;
* `gzp_of_orientation` — **Corollary A.4, conditional**: a head orientation with root `r`
  (in-degree ≥ k) and the crossing supply (`k` crossing edges into every root-containing
  proper vertex subset — exactly what Theorem A.3's `k` edge-disjoint paths provide) yields
  the GZP condition with `δⱼ = indeg(j)` off the root and `δᵣ = indeg(r) − k`.

After this brick, Corollary A.4 rests solely on Theorem A.3 (Frank's orientation theorem),
completing the counting side of Appendix A.
-/

open Finset

namespace AGL24

variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [Fintype V] [DecidableEq V]

/-- **The generic-zero-pattern condition** ([AGL24] Definition A.1, condition (A.2)) in
multiplicity-function form, additively stated: for every multiplicity vector `κ ≤ δ` with
positive total, the number of edges induced by the zero set of `κ`, plus the total
multiplicity, plus `k`, is at most the edge count. -/
def GZPCondition (e : ι → Finset V) (δ : V → ℕ) (k : ℕ) : Prop :=
  ∀ κ : V → ℕ, (∀ j, κ j ≤ δ j) → 0 < ∑ j, κ j →
    (Finset.univ.filter (fun i => e i ⊆ Finset.univ.filter (fun j => κ j = 0))).card
      + ∑ j, κ j + k ≤ Fintype.card ι

/-- The in-degrees over the complement of `T` count the heads outside `T`. -/
theorem sum_inDegree_compl {e : ι → Finset V} (O : HeadOrientation e) (T : Finset V) :
    ∑ j ∈ Finset.univ.filter (fun j => j ∉ T), O.inDegree j
      = (Finset.univ.filter (fun i => O.head i ∉ T)).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise
    (f := O.head) (t := Finset.univ.filter (fun j => j ∉ T))
    (fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using hi⟩)]
  refine Finset.sum_congr rfl fun j hj => ?_
  unfold HeadOrientation.inDegree
  congr 1
  ext i
  rw [Finset.mem_filter] at hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hhead
    refine ⟨?_, hhead⟩
    rw [hhead]
    exact hj.2
  · exact fun h => h.2

/-- **[AGL24] Corollary A.4, conditional form**: a head orientation with a root of in-degree
at least `k` and the crossing supply (Theorem A.3's edge-disjoint paths) yields the
generic-zero-pattern condition. -/
theorem gzp_of_orientation {e : ι → Finset V} (O : HeadOrientation e) (r : V) (k : ℕ)
    (hne : ∀ i, (e i).Nonempty)
    (hroot : k ≤ O.inDegree r)
    (hcross : ∀ T : Finset V, r ∈ T → T ≠ Finset.univ →
      k ≤ (Finset.univ.filter (fun i => O.head i ∈ T ∧ ¬ e i ⊆ T)).card) :
    GZPCondition e (fun j => if j = r then O.inDegree j - k else O.inDegree j) k := by
  classical
  intro κ hκ hpos
  set T := Finset.univ.filter (fun j => κ j = 0) with hT
  -- κ is supported off T, bounded by δ there.
  have hκT : ∑ j, κ j ≤ ∑ j ∈ Finset.univ.filter (fun j => j ∉ T),
      (if j = r then O.inDegree j - k else O.inDegree j) := by
    calc ∑ j, κ j
        = ∑ j ∈ Finset.univ.filter (fun j => j ∉ T), κ j := by
          rw [eq_comm]
          refine Finset.sum_filter_of_ne fun j _ hj => ?_
          rw [hT]
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          omega
    _ ≤ ∑ j ∈ Finset.univ.filter (fun j => j ∉ T),
        (if j = r then O.inDegree j - k else O.inDegree j) :=
          Finset.sum_le_sum fun j _ => hκ j
  -- The head count over the complement.
  have hcompl := sum_inDegree_compl O T
  -- Heads split between T and its complement.
  have hheads : (Finset.univ.filter (fun i => O.head i ∈ T)).card
      + (Finset.univ.filter (fun i => O.head i ∉ T)).card = Fintype.card ι := by
    rw [← Finset.card_univ (α := ι)]
    exact Finset.filter_card_add_filter_neg_card_eq_card (fun i => O.head i ∈ T)
  by_cases hrT : r ∈ T
  · -- Case 1: the root is in T — the crossing supply applies; δ sums to indeg off the root.
    have hTne : T ≠ Finset.univ := by
      intro hTuniv
      obtain ⟨j, hj⟩ : ∃ j, 0 < κ j := by
        by_contra hall
        push Not at hall
        have : ∑ j, κ j = 0 := Finset.sum_eq_zero fun j _ => by
          have := hall j
          omega
        omega
      have : j ∈ T := hTuniv ▸ Finset.mem_univ j
      rw [hT, Finset.mem_filter] at this
      omega
    have hind := card_induced_le_card_heads_sub O T k hne (hcross T hrT hTne)
    -- δ agrees with indeg off T (r ∉ complement).
    have hδ : ∑ j ∈ Finset.univ.filter (fun j => j ∉ T),
        (if j = r then O.inDegree j - k else O.inDegree j)
        = ∑ j ∈ Finset.univ.filter (fun j => j ∉ T), O.inDegree j := by
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_filter] at hj
      rw [if_neg (fun h => hj.2 (by rw [h]; exact hrT))]
    rw [hδ, hcompl] at hκT
    -- Assemble: induced ≤ headsT − k; Σκ ≤ n − headsT; total ≤ n.
    have hheadk : k ≤ (Finset.univ.filter (fun i => O.head i ∈ T)).card := by
      refine le_trans (hcross T hrT hTne) (Finset.card_le_card ?_)
      intro i hi
      rw [Finset.mem_filter] at hi ⊢
      exact ⟨Finset.mem_univ _, hi.2.1⟩
    omega
  · -- Case 2: the root is off T — the plain count; δ's −k sits in the complement sum.
    have hind := card_induced_le_card_heads O T hne
    have hδ : ∑ j ∈ Finset.univ.filter (fun j => j ∉ T),
        (if j = r then O.inDegree j - k else O.inDegree j) + k
        ≤ ∑ j ∈ Finset.univ.filter (fun j => j ∉ T), O.inDegree j := by
      have hrmem : r ∈ Finset.univ.filter (fun j => j ∉ T) := by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hrT⟩
      rw [← Finset.sum_erase_add _ _ hrmem,
        ← Finset.sum_erase_add _ (fun j => O.inDegree j) hrmem]
      rw [if_pos rfl]
      have herase : ∑ j ∈ (Finset.univ.filter (fun j => j ∉ T)).erase r,
          (if j = r then O.inDegree j - k else O.inDegree j)
          = ∑ j ∈ (Finset.univ.filter (fun j => j ∉ T)).erase r, O.inDegree j := by
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [if_neg (Finset.ne_of_mem_erase hj)]
      rw [herase]
      omega
    rw [hcompl] at hδ
    omega

end AGL24

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms AGL24.sum_inDegree_compl
#print axioms AGL24.gzp_of_orientation
