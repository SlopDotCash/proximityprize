/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib
import ArkLib.Data.CodingTheory.AGL24WeakPartition

/-!
# [AGL24] §2: the agreement hypergraph and Lemma 2.3 (issue #346, brick 1)

On top of Lemma 2.4 (`AGL24WeakPartition.lean`), the bad-list-configuration entry point of
[AGL24] (arXiv 2304.09445):

* `agreementEdge` — Definition 2.1: the hypergraph on `[L+1]` whose edge at position `i` is
  `{j : c⁽ʲ⁾ᵢ = yᵢ}`;
* `sum_agreementEdge_card` — the double-count `∑ᵢ |eᵢ| = ∑ⱼ (n − d(y, c⁽ʲ⁾))`;
* `agreement_weight_lower_bound` — display (2.4): total edge weight `≥ Lk` whenever the
  total distance is `≤ L(n−k)`;
* `exists_wpc_subset_of_bad_list` — **Lemma 2.3**: a bad average-radius list configuration
  (`∑ⱼ d(y, c⁽ʲ⁾) ≤ L(n−k)`) yields `J ⊆ [L+1]`, `|J| ≥ 2`, whose restricted agreement
  hypergraph is `k`-weakly-partition-connected.

Next brick on the chain: the reduced intersection matrix (Definition 2.6) and its full-rank
implication for list-decodability.
-/

open Finset

namespace AGL24

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]

/-- **[AGL24] Definition 2.1 (agreement hypergraph).** The edge at position `i`: the set of
list indices whose codeword agrees with `y` at `i`. -/
def agreementEdge {L : ℕ} (y : ι → α) (c : Fin (L + 1) → ι → α) (i : ι) :
    Finset (Fin (L + 1)) :=
  Finset.univ.filter (fun j => c j i = y i)

/-- Per-codeword agreement count: `#{i : c⁽ʲ⁾ᵢ = yᵢ} = n − d(y, c⁽ʲ⁾)`. -/
theorem card_agree_eq_sub_hammingDist {y c : ι → α} :
    (Finset.univ.filter (fun i => c i = y i)).card
      = Fintype.card ι - hammingDist y c := by
  classical
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (Finset.univ : Finset ι)) (p := fun i => c i = y i)
  rw [Finset.card_univ] at hsplit
  have hdist : hammingDist y c
      = (Finset.univ.filter (fun i => ¬ c i = y i)).card := by
    unfold hammingDist
    congr 1
    ext i
    simp [ne_comm, eq_comm]
  omega

/-- **The agreement double count**: `∑ᵢ |eᵢ| = ∑ⱼ (n − d(y, c⁽ʲ⁾))`. -/
theorem sum_agreementEdge_card {L : ℕ} (y : ι → α) (c : Fin (L + 1) → ι → α) :
    ∑ i, (agreementEdge y c i).card
      = ∑ j, (Fintype.card ι - hammingDist y (c j)) := by
  classical
  -- Both sides count pairs (i, j) with c j i = y i.
  have hswap : ∑ i, (agreementEdge y c i).card
      = ∑ j : Fin (L + 1), (Finset.univ.filter (fun i : ι => c j i = y i)).card := by
    simp only [agreementEdge, Finset.card_filter]
    rw [Finset.sum_comm]
  rw [hswap]
  exact Finset.sum_congr rfl fun j _ => card_agree_eq_sub_hammingDist

/-- **[AGL24] display (2.4)**: a bad average-radius configuration has total agreement-edge
weight at least `Lk`. -/
theorem agreement_weight_lower_bound {L k : ℕ} (y : ι → α) (c : Fin (L + 1) → ι → α)
    (hk : k ≤ Fintype.card ι)
    (hdist : ∑ j, hammingDist y (c j) ≤ L * (Fintype.card ι - k)) :
    L * k ≤ ∑ i, edgeWeight (agreementEdge y c i) := by
  classical
  set n := Fintype.card ι with hn
  set A := ∑ i, edgeWeight (agreementEdge y c i) with hA
  set B := ∑ i, (agreementEdge y c i).card with hB
  set D := ∑ j, hammingDist y (c j) with hD
  -- Per-edge: wt(e) + 1 ≥ |e|.
  have hAB : B ≤ A + n := by
    rw [hA, hB, hn, ← Finset.card_univ, Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    unfold edgeWeight
    omega
  -- The double count, with the per-term complement: B + D = (L+1)·n.
  have hBD : B + D = (L + 1) * n := by
    rw [hB, hD, sum_agreementEdge_card]
    rw [← Finset.sum_add_distrib]
    rw [show ∑ j : Fin (L + 1), (n - hammingDist y (c j) + hammingDist y (c j))
        = ∑ _j : Fin (L + 1), n from Finset.sum_congr rfl fun j _ => by
      have := hammingDist_le_card_fintype (x := y) (y := c j)
      omega]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  -- The product identity, with the products as atoms.
  have hsplit : L * (n - k) + L * k = L * n := by
    rw [← Nat.mul_add]
    congr 1
    omega
  -- Assemble.
  set x := L * (n - k) with hx
  set z := L * k with hz
  set w := L * n with hw
  have : B + D = w + n := by rw [hBD]; ring
  omega

/-- **[AGL24] Lemma 2.3.** If `∑ⱼ d(y, c⁽ʲ⁾) ≤ L(n−k)` (a bad average-radius list
configuration), some `J ⊆ [L+1]` with `|J| ≥ 2` has its restricted agreement hypergraph
`k`-weakly-partition-connected. -/
theorem exists_wpc_subset_of_bad_list {L k : ℕ} (hL : 1 ≤ L)
    (y : ι → α) (c : Fin (L + 1) → ι → α)
    (hk : k ≤ Fintype.card ι)
    (hdist : ∑ j, hammingDist y (c j) ≤ L * (Fintype.card ι - k)) :
    ∃ J : Finset (Fin (L + 1)), 2 ≤ J.card ∧
      WeaklyPartitionConnected k J (agreementEdge y c) := by
  refine exists_weaklyPartitionConnected_subset k (agreementEdge y c) ?_ ?_
  · rw [Fintype.card_fin]
    omega
  · rw [Fintype.card_fin]
    calc k * (L + 1 - 1) = L * k := by
          rw [show L + 1 - 1 = L from rfl, Nat.mul_comm]
    _ ≤ ∑ i, edgeWeight (agreementEdge y c i) :=
        agreement_weight_lower_bound y c hk hdist

end AGL24

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms AGL24.sum_agreementEdge_card
#print axioms AGL24.agreement_weight_lower_bound
#print axioms AGL24.exists_wpc_subset_of_bad_list
