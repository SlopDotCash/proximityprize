/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CrossingCountGeneral

/-!
# The `s`-set pencil bound (#389, general-`k` lift, piece 2)

Generalizes `pencil_family_card_le` from a common point to a common `s`-set: sets
through a common `Y`, pairwise meeting exactly at `Y`, with `≥ r` points beyond `Y`,
have disjoint remainders:

> **`pencil_family_card_le_general`** — `S.card · r ≤ n − Y.card`.

At `s = k − 1` this is the `(k−1)`-set pencil degree bound of the general-`k`
mean-degree programme: for `rsCode dom k` agreement families (pairwise `≤ k−1`), the
sets through a common `(k−1)`-set meet exactly there, so each `(k−1)`-set carries at
most `(n−k+1)/(t−k+1)` large agreement sets.  The remaining lift piece is the branch
analysis.  Issue #389.
-/

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.PairRank

variable {n : ℕ} [NeZero n]

/-- **The `s`-set pencil bound**: sets through a common `Y`, pairwise meeting exactly
at `Y`, each with `≥ r` points beyond `Y`, number at most `(n − |Y|)/r`. -/
theorem pencil_family_card_le_general {S : Finset (Finset (Fin n))}
    {Y : Finset (Fin n)} {r : ℕ}
    (hmem : ∀ A ∈ S, Y ⊆ A ∧ Y.card + r ≤ A.card)
    (hpair : ∀ A ∈ S, ∀ B ∈ S, A ≠ B → A ∩ B = Y) :
    S.card * r ≤ n - Y.card := by
  classical
  have hdisj : ∀ A ∈ S, ∀ B ∈ S, A ≠ B → Disjoint (A \ Y) (B \ Y) := by
    intro A hA B hB hne
    rw [Finset.disjoint_left]
    intro i hiA hiB
    have hi : i ∈ A ∩ B := Finset.mem_inter.mpr
      ⟨(Finset.mem_sdiff.mp hiA).1, (Finset.mem_sdiff.mp hiB).1⟩
    rw [hpair A hA B hB hne] at hi
    exact (Finset.mem_sdiff.mp hiA).2 hi
  have hcard : ∀ A ∈ S, r ≤ (A \ Y).card := by
    intro A hA
    obtain ⟨hY, hr⟩ := hmem A hA
    have h1 : (A \ Y).card = A.card - (Y ∩ A).card := Finset.card_sdiff
    have h2 : Y ∩ A = Y := Finset.inter_eq_left.mpr hY
    rw [h2] at h1
    omega
  calc S.card * r = ∑ _A ∈ S, r := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  _ ≤ ∑ A ∈ S, (A \ Y).card := Finset.sum_le_sum hcard
  _ = (S.biUnion (fun A => A \ Y)).card := (Finset.card_biUnion hdisj).symm
  _ ≤ ((Finset.univ : Finset (Fin n)) \ Y).card := by
      refine Finset.card_le_card ?_
      intro i hi
      obtain ⟨A, _, hiA⟩ := Finset.mem_biUnion.mp hi
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hiA).2⟩
  _ = n - Y.card := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]

end ProximityGap.PairRank

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.PairRank.pencil_family_card_le_general
