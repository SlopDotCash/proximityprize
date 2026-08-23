/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib
import ArkLib.Data.CodingTheory.AGL24WeakPartition

/-!
# [AGL24] §2.5: deletion robustness — Lemma 2.14's combinatorial core (issue #346, brick 13)

The certificate machinery's well-definedness (Lemma 3.2) rests on **Lemma 2.14**: row-deleted
reduced intersection matrices of `(k + εn)`-weakly-partition-connected hypergraphs keep full
column rank. Its proof splits into (a) the *combinatorial* core — deleting `≤ m` edges from a
`(k+m)`-weakly-partition-connected hypergraph leaves it `k`-weakly-partition-connected — and
(b) the *algebraic* input (Theorem 2.11, the symbolic full-column-rank theorem from the
GM-MDS line, proven in the paper's Appendix A). This brick proves (a) and names the structure:

* `touchedCells_card_le` — each edge touches at most `|P|` cells;
* `weaklyPartitionConnected_delete` — **the deletion robustness**: emptying any `≤ m` edges
  (the indexed-family form of deletion; empty edges contribute no weight, no touched cells,
  and — structurally — no RIM rows) of a `(k+m)`-WPC family leaves a `k`-WPC family.

With (a) proven, the full Lemma 2.14 reduces to Theorem 2.11 alone — sharpening the
campaign's residual structure: the certificate combinatorics of §3 can be carried with the
symbolic rank theorem as the single deep algebraic input.
-/

open Finset

namespace AGL24

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Each edge touches at most `|P.parts|` cells. -/
theorem touchedCells_card_le {s : Finset V} (P : Finpartition s) (e : Finset V) :
    (touchedCells P e).card ≤ P.parts.card :=
  Finset.card_le_card (Finset.filter_subset _ _)

/-- **[AGL24] Lemma 2.14, combinatorial core (deletion robustness)**: emptying at most `m`
edges of a `(k + m)`-weakly-partition-connected family leaves a `k`-weakly-partition-connected
family. (Each deleted edge costs at most `|P| − 1` per partition; the slack `m(|P| − 1)`
absorbs it.) -/
theorem weaklyPartitionConnected_delete {ι : Type*} [Fintype ι] [DecidableEq ι]
    {k m : ℕ} (s : Finset V) (e : ι → Finset V) (B : Finset ι)
    (hB : B.card ≤ m)
    (h : WeaklyPartitionConnected (k + m) s e) :
    WeaklyPartitionConnected k s (fun i => if i ∈ B then ∅ else e i) := by
  classical
  intro P
  set p := P.parts.card with hp
  -- The deleted family's sum: the untouched edges keep their contribution; emptied edges
  -- contribute zero.
  have hsplit : ∑ i, ((touchedCells P ((if i ∈ B then ∅ else e i) ∩ s)).card - 1)
      = ∑ i ∈ Finset.univ.filter (fun i => i ∉ B),
          ((touchedCells P (e i ∩ s)).card - 1) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => i ∉ B)]
    rw [show ∑ i ∈ Finset.univ.filter (fun i => ¬ i ∉ B),
        ((touchedCells P ((if i ∈ B then ∅ else e i) ∩ s)).card - 1) = 0 from
      Finset.sum_eq_zero fun i hi => by
        rw [Finset.mem_filter] at hi
        have hiB : i ∈ B := not_not.mp hi.2
        rw [if_pos hiB]
        rw [show (∅ : Finset V) ∩ s = ∅ from Finset.empty_inter s]
        rw [show touchedCells P (∅ : Finset V) = ∅ from by
          unfold touchedCells
          rw [Finset.filter_eq_empty_iff]
          intro c _
          simp]
        simp]
    rw [add_zero]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_filter] at hi
    rw [if_neg hi.2]
  rw [hsplit]
  -- The full sum minus the deleted edges' contributions.
  have hfull := h P
  -- Each deleted edge contributed at most p − 1.
  have hdel : ∑ i ∈ Finset.univ.filter (fun i => i ∈ B),
      ((touchedCells P (e i ∩ s)).card - 1) ≤ m * (p - 1) := by
    calc ∑ i ∈ Finset.univ.filter (fun i => i ∈ B),
        ((touchedCells P (e i ∩ s)).card - 1)
        ≤ ∑ _i ∈ Finset.univ.filter (fun i => i ∈ B), (p - 1) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have := touchedCells_card_le P (e i ∩ s)
          omega
    _ = (Finset.univ.filter (fun i => i ∈ B)).card * (p - 1) := by
          rw [Finset.sum_const, smul_eq_mul]
    _ ≤ m * (p - 1) := by
          refine Nat.mul_le_mul_right _ ?_
          calc (Finset.univ.filter (fun i => i ∈ B)).card
              = B.card := by
                congr 1
                ext i
                simp
          _ ≤ m := hB
  -- Assemble: kept-sum = full-sum − deleted-sum ≥ (k+m)(p−1) − m(p−1) = k(p−1).
  have hsum : ∑ i ∈ Finset.univ.filter (fun i => i ∉ B),
        ((touchedCells P (e i ∩ s)).card - 1)
      + ∑ i ∈ Finset.univ.filter (fun i => i ∈ B),
        ((touchedCells P (e i ∩ s)).card - 1)
      = ∑ i, ((touchedCells P (e i ∩ s)).card - 1) := by
    rw [show Finset.univ.filter (fun i => i ∈ B)
        = Finset.univ.filter (fun i => ¬ i ∉ B) from by
      ext i
      simp]
    exact Finset.sum_filter_add_sum_filter_not Finset.univ _ _
  -- Atoms-for-omega: the product identity.
  have hprod : k * (p - 1) + m * (p - 1) = (k + m) * (p - 1) := by
    rw [← Nat.add_mul]
  set A := ∑ i, ((touchedCells P (e i ∩ s)).card - 1) with hA
  set K := ∑ i ∈ Finset.univ.filter (fun i => i ∉ B),
    ((touchedCells P (e i ∩ s)).card - 1) with hK
  set D := ∑ i ∈ Finset.univ.filter (fun i => i ∈ B),
    ((touchedCells P (e i ∩ s)).card - 1) with hD
  set x := k * (p - 1) with hx
  set z := m * (p - 1) with hz
  set w := (k + m) * (p - 1) with hw
  -- K + D = A, A ≥ w, D ≤ z, x + z = w ⟹ K ≥ x.
  omega

end AGL24

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms AGL24.touchedCells_card_le
#print axioms AGL24.weaklyPartitionConnected_delete
