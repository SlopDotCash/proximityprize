/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Coverage selection — the node-selection double count

The combinatorial half of the [BCIKS20] Claim 5.7 pigeonhole: a family of scalars `C`
whose witness sets `S z` each miss at most `A` of the `N` candidate nodes admits, whenever
`C·A ≤ (N - n)·(C - B)`, a set of `n` nodes **each covered by more than `B` scalars** —
the `hcardNodes` requirement of the heavy-data interface
(`BCIKS20.Claim510Improve.improve_disjunct_of_heavy`).

Double count the non-incidences: each bad node (coverage `≤ B`) is missed by at least
`C - B` scalars, while total misses are at most `C·A`; so bad nodes number at most
`C·A/(C - B) ≤ N - n`, leaving `n` good nodes.

## Main results

* `exists_covered_nodes` — the selected node *set* of size `≥ n`.
* `exists_covered_nodes_emb` — the selection as an embedding `Fin n ↪ β`.
-/

namespace Finset

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

open Finset

/-- **Coverage selection (set form).**  If every scalar of `C` misses at most `A` of the
nodes `X`, and `C·A ≤ (|X| - n)·(|C| - B)` with `B < |C|`, then at least `n` nodes are
each covered by more than `B` scalars. -/
theorem exists_covered_nodes
    (C : Finset α) (X : Finset β) (S : α → Finset β)
    (hS : ∀ z ∈ C, S z ⊆ X)
    {A : ℕ} (hA : ∀ z ∈ C, X.card - (S z).card ≤ A)
    {B n : ℕ} (hB : B < C.card)
    (hbig : C.card * A ≤ (X.card - n) * (C.card - B))
    (hn : n ≤ X.card) :
    ∃ E : Finset β, E ⊆ X ∧ n ≤ E.card ∧
      ∀ x ∈ E, B < (C.filter (fun z => x ∈ S z)).card := by
  classical
  set good : Finset β := X.filter (fun x => B < (C.filter (fun z => x ∈ S z)).card)
    with hgood
  refine ⟨good, filter_subset _ _, ?_, fun x hx => (mem_filter.mp hx).2⟩
  -- the double count: total misses two ways
  have hswap : ∑ z ∈ C, (X.filter (fun x => x ∉ S z)).card
      = ∑ x ∈ X, (C.filter (fun z => x ∉ S z)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  -- per-scalar misses are at most `A`
  have hmiss : ∀ z ∈ C, (X.filter (fun x => x ∉ S z)).card ≤ A := by
    intro z hz
    have h1 : X.filter (fun x => x ∉ S z) = X \ S z := by
      ext x
      simp [mem_sdiff]
    rw [h1, card_sdiff, Finset.inter_eq_left.mpr (hS z hz)]
    exact hA z hz
  -- the bad nodes, each missed by at least `|C| - B` scalars
  set bad : Finset β := X.filter (fun x => ¬ B < (C.filter (fun z => x ∈ S z)).card)
    with hbad
  have hbadmiss : ∀ x ∈ bad, C.card - B ≤ (C.filter (fun z => x ∉ S z)).card := by
    intro x hx
    have hcov : (C.filter (fun z => x ∈ S z)).card ≤ B :=
      Nat.not_lt.mp (mem_filter.mp hx).2
    have hsplit : (C.filter (fun z => x ∈ S z)).card
        + (C.filter (fun z => ¬ x ∈ S z)).card = C.card :=
      card_filter_add_card_filter_not _
    omega
  -- assemble: `bad·(|C| - B) ≤ total misses ≤ |C|·A`
  have hchain : bad.card * (C.card - B) ≤ C.card * A := by
    calc bad.card * (C.card - B)
        = ∑ _x ∈ bad, (C.card - B) := by simp [sum_const, mul_comm]
      _ ≤ ∑ x ∈ bad, (C.filter (fun z => x ∉ S z)).card := sum_le_sum hbadmiss
      _ ≤ ∑ x ∈ X, (C.filter (fun z => x ∉ S z)).card :=
          sum_le_sum_of_subset (filter_subset _ _)
      _ = ∑ z ∈ C, (X.filter (fun x => x ∉ S z)).card := hswap.symm
      _ ≤ ∑ _z ∈ C, A := sum_le_sum hmiss
      _ = C.card * A := by simp [sum_const, mul_comm]
  -- bad nodes number at most `|X| - n`
  have hbadcard : bad.card ≤ X.card - n := by
    have h2 : (0 : ℕ) < C.card - B := by omega
    exact Nat.le_of_mul_le_mul_right (le_trans hchain hbig) h2
  -- good and bad partition `X`
  have hpart : good.card + bad.card = X.card :=
    card_filter_add_card_filter_not _
  omega

/-- **Coverage selection (embedding form).**  The selected nodes as an injection
`Fin n ↪ β`, each landing in `X` with coverage exceeding `B`. -/
theorem exists_covered_nodes_emb
    (C : Finset α) (X : Finset β) (S : α → Finset β)
    (hS : ∀ z ∈ C, S z ⊆ X)
    {A : ℕ} (hA : ∀ z ∈ C, X.card - (S z).card ≤ A)
    {B n : ℕ} (hB : B < C.card)
    (hbig : C.card * A ≤ (X.card - n) * (C.card - B))
    (hn : n ≤ X.card) :
    ∃ e : Fin n ↪ β, ∀ j, e j ∈ X ∧
      B < (C.filter (fun z => e j ∈ S z)).card := by
  classical
  obtain ⟨E, hEX, hEcard, hEcov⟩ := exists_covered_nodes C X S hS hA hB hbig hn
  obtain ⟨E', hE'E, hE'card⟩ := Finset.exists_subset_card_eq hEcard
  let eq : Fin n ≃ (E' : Finset β) := (E'.equivFin.trans (finCongr hE'card)).symm
  refine ⟨⟨fun j => (eq j : β), fun a b hab => eq.injective (Subtype.ext hab)⟩, fun j => ?_⟩
  have hmem : (eq j : β) ∈ E' := (eq j).2
  have hmemE : (eq j : β) ∈ E := hE'E hmem
  exact ⟨hEX hmemE, hEcov _ hmemE⟩

end Finset

/-! ## Axiom audit -/
#print axioms Finset.exists_covered_nodes
#print axioms Finset.exists_covered_nodes_emb
