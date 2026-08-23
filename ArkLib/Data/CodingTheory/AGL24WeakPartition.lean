/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib

/-!
# [AGL24] §2: weak partition connectivity and Lemma 2.4 (issue #346, brick 0)

The hypergraph-combinatorics opening of [AGL24] (arXiv 2304.09445, *Random Reed–Solomon codes
achieve list-decoding capacity with linear-sized alphabets*), formalized against the paper:

* `edgeWeight` — `wt(e) = max{|e| − 1, 0}` (ℕ-truncated subtraction *is* the max);
* `WeaklyPartitionConnected` — Definition 2.2: for every partition `P` of the vertex set,
  `∑_e (|P(e)| − 1) ≥ k(|P| − 1)`, where `P(e)` is the set of cells `e` touches;
* `partition_weight_identity` — the per-edge bookkeeping identity
  `wt(e) = ∑_{c ∈ P} wt(e ∩ c) + (|P(e)| − 1)` behind display (2.3);
* `exists_weaklyPartitionConnected_subset` — **Lemma 2.4**: any edge family with total weight
  `≥ k(|V| − 1)` (`|V| ≥ 2`) admits a vertex subset `V'` (`|V'| ≥ 2`) on which the restricted
  hypergraph is `k`-weakly-partition-connected. Proof = the paper's: an inclusion-minimal
  `V'` among the `≥ 2`-element subsets satisfying the weight inequality (singletons satisfy
  it with equality, so minimality bounds *every* nonempty proper subset), then the per-edge
  identity + minimality give display (2.3).

Entry brick of the [AGL24] campaign scoped on issue #346 (the agreement-hypergraph
construction and Lemma 2.3 sit directly on top; the reduced intersection matrices follow).
-/

open Finset

namespace AGL24

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `wt(e) = max{|e| − 1, 0}` — truncated subtraction is exactly the paper's max. -/
def edgeWeight (e : Finset V) : ℕ := e.card - 1

/-- The set of cells of a partition that an edge touches. -/
def touchedCells {s : Finset V} (P : Finpartition s) (e : Finset V) : Finset (Finset V) :=
  P.parts.filter (fun c => (e ∩ c).Nonempty)

/-- **Definition 2.2 ([AGL24]).** The restriction to `s` of the edge family `e` is
`k`-weakly-partition-connected: every partition `P` of `s` satisfies
`∑_i (|P(eᵢ ∩ s)| − 1) ≥ k(|P| − 1)`. -/
def WeaklyPartitionConnected {ι : Type*} [Fintype ι] (k : ℕ) (s : Finset V)
    (e : ι → Finset V) : Prop :=
  ∀ P : Finpartition s,
    k * (P.parts.card - 1) ≤ ∑ i, ((touchedCells P (e i ∩ s)).card - 1)

/-- An edge inside `s` is the disjoint union of its cell intersections. -/
theorem card_eq_sum_inter_parts {s : Finset V} (P : Finpartition s)
    {e : Finset V} (he : e ⊆ s) :
    e.card = ∑ c ∈ P.parts, (e ∩ c).card := by
  classical
  have hbi : e = P.parts.biUnion (fun c => e ∩ c) := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_inter]
    constructor
    · intro hx
      obtain ⟨c, hc, hxc⟩ := P.exists_mem (he hx)
      exact ⟨c, hc, hx, hxc⟩
    · rintro ⟨c, _, hx, _⟩
      exact hx
  conv_lhs => rw [hbi]
  rw [Finset.card_biUnion]
  intro c hc c' hc' hne
  have hdisj := P.disjoint hc hc' hne
  exact Finset.disjoint_left.mpr fun x hx hx' =>
    (Finset.disjoint_left.mp hdisj) (Finset.mem_inter.mp hx).2 (Finset.mem_inter.mp hx').2

/-- The cell-weight sum collapses to `|e| − |P(e)|`. -/
theorem sum_cell_weights {s : Finset V} (P : Finpartition s)
    {e : Finset V} (he : e ⊆ s) :
    ∑ c ∈ P.parts, edgeWeight (e ∩ c) = e.card - (touchedCells P e).card := by
  classical
  -- Untouched cells contribute weight 0; restrict to touched cells.
  have hres : ∑ c ∈ P.parts, edgeWeight (e ∩ c)
      = ∑ c ∈ touchedCells P e, edgeWeight (e ∩ c) := by
    rw [touchedCells, Finset.sum_filter_of_ne]
    intro c _ hne
    by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty] at hcon
    rw [hcon] at hne
    exact hne rfl
  -- On touched cells the weight is exactly card − 1; distribute the subtraction.
  have hsub : ∑ c ∈ touchedCells P e, edgeWeight (e ∩ c)
      = (∑ c ∈ touchedCells P e, (e ∩ c).card) - (touchedCells P e).card := by
    unfold edgeWeight
    rw [← Finset.sum_attach (touchedCells P e) (fun c => (e ∩ c).card - 1),
      ← Finset.sum_attach (touchedCells P e) (fun c => (e ∩ c).card)]
    rw [show (touchedCells P e).card = ∑ _c ∈ (touchedCells P e).attach, 1 from by
      rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_attach]]
    rw [eq_comm, Nat.sub_eq_iff_eq_add ?hle]
    case hle =>
      refine Finset.sum_le_sum fun c _ => ?_
      have : (e ∩ c.val).Nonempty := (Finset.mem_filter.mp c.property).2
      exact Nat.one_le_iff_ne_zero.mpr (Finset.card_ne_zero.mpr this)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    have : (e ∩ c.val).Nonempty := (Finset.mem_filter.mp c.property).2
    have h1 : 1 ≤ (e ∩ c.val).card := Nat.one_le_iff_ne_zero.mpr (Finset.card_ne_zero.mpr this)
    omega
  -- The touched-cell card sum is the full card sum.
  have hfull : ∑ c ∈ touchedCells P e, (e ∩ c).card = e.card := by
    rw [card_eq_sum_inter_parts P he, touchedCells, eq_comm]
    rw [← Finset.sum_filter_add_sum_filter_not P.parts (fun c => (e ∩ c).Nonempty)]
    rw [show ∑ c ∈ P.parts.filter (fun c => ¬(e ∩ c).Nonempty), (e ∩ c).card = 0 from
      Finset.sum_eq_zero fun c hc => by
        rw [Finset.card_eq_zero, ← Finset.not_nonempty_iff_eq_empty]
        exact (Finset.mem_filter.mp hc).2]
    rw [add_zero]
  rw [hres, hsub, hfull]

/-- **The per-edge bookkeeping identity** behind [AGL24] display (2.3):
`wt(e) = ∑_{c ∈ P} wt(e ∩ c) + (|P(e)| − 1)` for `e ⊆ s`. -/
theorem partition_weight_identity {s : Finset V} (P : Finpartition s)
    {e : Finset V} (he : e ⊆ s) :
    edgeWeight e = (∑ c ∈ P.parts, edgeWeight (e ∩ c)) + ((touchedCells P e).card - 1) := by
  classical
  rw [sum_cell_weights P he]
  set h := (touchedCells P e).card with hh
  rcases Finset.eq_empty_or_nonempty e with rfl | hne
  · -- Empty edge: everything is 0.
    have h0 : h = 0 := by
      rw [hh, touchedCells, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro c _
      simp
    rw [h0]
    simp [edgeWeight]
  · -- Nonempty edge: 1 ≤ h ≤ |e|, pure arithmetic.
    have h1 : 1 ≤ h := by
      obtain ⟨x, hx⟩ := hne
      obtain ⟨c, hc, hxc⟩ := P.exists_mem (he hx)
      rw [hh]
      refine Finset.card_pos.mpr ⟨c, ?_⟩
      rw [touchedCells, Finset.mem_filter]
      exact ⟨hc, ⟨x, Finset.mem_inter.mpr ⟨hx, hxc⟩⟩⟩
    have hle : h ≤ e.card := by
      rw [hh]
      calc (touchedCells P e).card = ∑ _c ∈ touchedCells P e, 1 := by
            rw [Finset.sum_const, smul_eq_mul, mul_one]
      _ ≤ ∑ c ∈ touchedCells P e, (e ∩ c).card := by
            refine Finset.sum_le_sum fun c hc => ?_
            exact Nat.one_le_iff_ne_zero.mpr (Finset.card_ne_zero.mpr
              (Finset.mem_filter.mp hc).2)
      _ ≤ ∑ c ∈ P.parts, (e ∩ c).card :=
            Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ = e.card := (card_eq_sum_inter_parts P he).symm
    unfold edgeWeight
    omega

/-- **[AGL24] Lemma 2.4.** If the total edge weight is at least `k(|V| − 1)` (and `|V| ≥ 2`),
some vertex subset `V'` with `|V'| ≥ 2` makes the restricted hypergraph
`k`-weakly-partition-connected. -/
theorem exists_weaklyPartitionConnected_subset {ι : Type*} [Fintype ι]
    (k : ℕ) (e : ι → Finset V) (hV : 2 ≤ Fintype.card V)
    (hwt : k * (Fintype.card V - 1) ≤ ∑ i, edgeWeight (e i)) :
    ∃ V' : Finset V, 2 ≤ V'.card ∧ WeaklyPartitionConnected k V' e := by
  classical
  -- The candidate set: ≥2-element subsets satisfying the weight inequality.
  set S : Finset (Finset V) := Finset.univ.powerset.filter
    (fun W => 2 ≤ W.card ∧ k * (W.card - 1) ≤ ∑ i, edgeWeight (e i ∩ W)) with hS
  have hUnivS : (Finset.univ : Finset V) ∈ S := by
    rw [hS, Finset.mem_filter]
    refine ⟨Finset.mem_powerset.mpr (Finset.Subset.refl _), ?_, ?_⟩
    · rwa [Finset.card_univ]
    · rw [Finset.card_univ]
      calc k * (Fintype.card V - 1) ≤ ∑ i, edgeWeight (e i) := hwt
      _ = ∑ i, edgeWeight (e i ∩ Finset.univ) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.inter_univ]
  -- An inclusion-minimal member (Finsets are well-founded under ⊂).
  obtain ⟨V', hV'min⟩ := exists_minimal_of_wellFoundedLT (· ∈ S) ⟨Finset.univ, hUnivS⟩
  have hV'S := hV'min.prop
  have hmin : ∀ W ∈ S, ¬ W ⊂ V' := by
    intro W hW hWss
    exact hWss.not_subset (hV'min.le_of_le hW hWss.subset)
  rw [hS, Finset.mem_filter] at hV'S
  obtain ⟨-, hV'2, hV'wt⟩ := hV'S
  refine ⟨V', hV'2, ?_⟩
  -- Minimality consequence: every nonempty proper subset fails the weight inequality weakly.
  have hproper : ∀ W : Finset V, W ⊆ V' → W.Nonempty → W ≠ V' →
      ∑ i, edgeWeight (e i ∩ W) ≤ k * (W.card - 1) := by
    intro W hWsub hWne hWneq
    rcases Nat.lt_or_ge W.card 2 with hc | hc
    · -- Singleton: every restricted edge has weight 0.
      have : ∀ i, edgeWeight (e i ∩ W) = 0 := by
        intro i
        unfold edgeWeight
        have : (e i ∩ W).card ≤ W.card := Finset.card_le_card (Finset.inter_subset_right)
        omega
      rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_const_zero]
      exact Nat.zero_le _
    · -- ≥2 elements: W ∈ S would contradict minimality.
      by_contra hcon
      push_neg at hcon
      have hWS : W ∈ S := by
        rw [hS, Finset.mem_filter]
        exact ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), hc, le_of_lt hcon⟩
      exact hmin W hWS (Finset.ssubset_iff_subset_ne.mpr ⟨hWsub, hWneq⟩)
  -- The weak-partition-connectivity, via the per-edge identity.
  intro P
  set p := P.parts.card with hp
  rcases Nat.lt_or_ge p 2 with hp1 | hp2
  · -- Trivial partition: RHS is 0.
    have : k * (p - 1) = 0 := by
      have : p - 1 = 0 := by omega
      rw [this, mul_zero]
    rw [this]
    exact Nat.zero_le _
  -- Nontrivial: every cell is a proper nonempty subset.
  have hcell : ∀ c ∈ P.parts, ∑ i, edgeWeight (e i ∩ c) ≤ k * (c.card - 1) := by
    intro c hc
    refine hproper c (P.le hc) (P.nonempty_of_mem_parts hc) ?_
    -- c = V' would force p = 1: any other (nonempty) cell is disjoint from c = V' ⊇ it.
    intro hcV
    obtain ⟨c', hc', c'', hc'', hcc⟩ := Finset.one_lt_card.mp (by omega : 1 < P.parts.card)
    have hkill : ∀ d ∈ P.parts, d ≠ c → False := by
      intro d hd hdc
      have hdisj := P.disjoint hd hc hdc
      obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts hd
      exact (Finset.disjoint_left.mp hdisj) hx (hcV ▸ P.le hd hx)
    rcases eq_or_ne c' c with hceq | hcne
    · exact hkill c'' hc'' (fun h => hcc (hceq.trans h.symm))
    · exact hkill c' hc' hcne
  -- Sum the per-edge identity over all edges (with e i ∩ V' as the edge inside V').
  have hidentity : ∀ i, edgeWeight (e i ∩ V')
      = (∑ c ∈ P.parts, edgeWeight ((e i ∩ V') ∩ c))
        + ((touchedCells P (e i ∩ V')).card - 1) :=
    fun i => partition_weight_identity P (Finset.inter_subset_right)
  -- Cell intersections collapse: (e i ∩ V') ∩ c = e i ∩ c for cells c ⊆ V'.
  have hcollapse : ∀ i, ∀ c ∈ P.parts, (e i ∩ V') ∩ c = e i ∩ c := by
    intro i c hc
    ext x
    simp only [Finset.mem_inter]
    exact ⟨fun ⟨⟨h1, _⟩, h3⟩ => ⟨h1, h3⟩, fun ⟨h1, h3⟩ => ⟨⟨h1, P.le hc h3⟩, h3⟩⟩
  -- The three quantities.
  set A := ∑ i, edgeWeight (e i ∩ V') with hA
  set B := ∑ c ∈ P.parts, ∑ i, edgeWeight (e i ∩ c) with hB
  set C := ∑ i, ((touchedCells P (e i ∩ V')).card - 1) with hC
  have hABC : A = B + C := by
    rw [hA, hB, hC]
    rw [Finset.sum_comm]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hidentity i]
    congr 1
    exact Finset.sum_congr rfl fun c hc => by rw [hcollapse i c hc]
  -- The bounds.
  have hAlb : k * (V'.card - 1) ≤ A := hV'wt
  have hBub : B ≤ k * (V'.card - p) := by
    rw [hB]
    calc ∑ c ∈ P.parts, ∑ i, edgeWeight (e i ∩ c)
        ≤ ∑ c ∈ P.parts, k * (c.card - 1) := Finset.sum_le_sum hcell
    _ = k * ∑ c ∈ P.parts, (c.card - 1) := by rw [Finset.mul_sum]
    _ = k * (V'.card - p) := by
        congr 1
        have hsum : ∑ c ∈ P.parts, c.card = V'.card := P.sum_card_parts
        have hone : ∀ c ∈ P.parts, 1 ≤ c.card := fun c hc =>
          Finset.card_pos.mpr (P.nonempty_of_mem_parts hc)
        have := Finset.sum_tsub_distrib (s := P.parts) (f := fun c => c.card)
          (g := fun _ => 1) (fun c hc => hone c hc)
        rw [this, hsum, Finset.sum_const, smul_eq_mul, mul_one, hp]
  -- p ≤ |V'| (p nonempty cells partition V').
  have hpv : p ≤ V'.card := by
    have hsum : ∑ c ∈ P.parts, c.card = V'.card := P.sum_card_parts
    calc p = ∑ _c ∈ P.parts, 1 := by rw [Finset.sum_const, smul_eq_mul, mul_one, hp]
    _ ≤ ∑ c ∈ P.parts, c.card := Finset.sum_le_sum fun c hc =>
          Finset.card_pos.mpr (P.nonempty_of_mem_parts hc)
    _ = V'.card := hsum
  -- Assemble: k(p−1) ≤ C, treating the products as atoms.
  have hsplit : k * (V'.card - p) + k * (p - 1) = k * (V'.card - 1) := by
    rw [← Nat.mul_add]
    congr 1
    omega
  omega

end AGL24

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms AGL24.partition_weight_identity
#print axioms AGL24.exists_weaklyPartitionConnected_subset
