/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CrossingCountBound

/-!
# The crossing count at general pairwise intersection (#389, the general-`k` lift)

Generalizes the `k = 2` crossing/Bonferroni step to pairwise intersection `≤ s`
(`s = k − 1` for `rsCode dom k`):

> **`crossing_double_count_general`** — `Σ_x d_x(d_x−1) ≤ s·L(L−1)`: each ordered
> pair of distinct sets contributes at most `s` crossings.

> **`degree_sum_le_general`** — `Σ_x d_x ≤ n + s·L(L−1)` — the general Bonferroni.

With the `(k−1)`-subset pencil bound (sets through a common `s`-set meet exactly
there, so their remainders are disjoint — the generalization of
`pencil_family_card_le`, registered) these feed the general-`k` mean-degree branch
analysis, whose deep condition becomes `t ≳ n^{(s+1)/(s+2)}`.  Issue #389.
-/

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.PairRank

variable {n : ℕ} [NeZero n]

open Classical in
/-- **The general crossing double-count**: pairwise intersection `≤ s` gives
`Σ_x d_x(d_x−1) ≤ s·L(L−1)`. -/
theorem crossing_double_count_general {S : Finset (Finset (Fin n))} {s : ℕ}
    (hpair : ∀ A ∈ S, ∀ B ∈ S, A ≠ B → (A ∩ B).card ≤ s) :
    ∑ x : Fin n, ((S.filter (fun A => x ∈ A)).card
        * ((S.filter (fun A => x ∈ A)).card - 1))
      ≤ s * (S.card * (S.card - 1)) := by
  classical
  have hpoint : ∀ x : Fin n, (S.filter (fun A => x ∈ A)).card
      * ((S.filter (fun A => x ∈ A)).card - 1)
      = (((S ×ˢ S).filter (fun p => p.1 ≠ p.2)).filter
          (fun p => x ∈ p.1 ∧ x ∈ p.2)).card := by
    intro x
    have h1 : (((S ×ˢ S).filter (fun p => p.1 ≠ p.2)).filter
        (fun p => x ∈ p.1 ∧ x ∈ p.2))
        = (((S.filter (fun A => x ∈ A)) ×ˢ (S.filter (fun A => x ∈ A))).filter
            (fun p => p.1 ≠ p.2)) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_product]
      tauto
    rw [h1, offdiag_card]
  rw [Finset.sum_congr rfl (fun x _ => hpoint x)]
  have hswap : (∑ x : Fin n, (((S ×ˢ S).filter (fun p => p.1 ≠ p.2)).filter
      (fun p => x ∈ p.1 ∧ x ∈ p.2)).card)
      = ∑ p ∈ (S ×ˢ S).filter (fun p => p.1 ≠ p.2), (p.1 ∩ p.2).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    have : (p.1 ∩ p.2).card
        = ((Finset.univ : Finset (Fin n)).filter (fun x => x ∈ p.1 ∧ x ∈ p.2)).card := by
      congr 1
      ext x
      simp [Finset.mem_inter]
    rw [this, Finset.card_filter]
  rw [hswap]
  calc ∑ p ∈ (S ×ˢ S).filter (fun p => p.1 ≠ p.2), (p.1 ∩ p.2).card
      ≤ ∑ p ∈ (S ×ˢ S).filter (fun p => p.1 ≠ p.2), s := by
        refine Finset.sum_le_sum fun p hp => ?_
        obtain ⟨hpmem, hne⟩ := Finset.mem_filter.mp hp
        rcases Finset.mem_product.mp hpmem with ⟨h1, h2⟩
        exact hpair p.1 h1 p.2 h2 hne
  _ = ((S ×ˢ S).filter (fun p => p.1 ≠ p.2)).card * s := by
        rw [Finset.sum_const, smul_eq_mul]
  _ = s * (S.card * (S.card - 1)) := by rw [offdiag_card]; ring

open Classical in
/-- **The general Bonferroni step**: `Σ_x d_x ≤ n + s·L(L−1)`. -/
theorem degree_sum_le_general {S : Finset (Finset (Fin n))} {s : ℕ}
    (hpair : ∀ A ∈ S, ∀ B ∈ S, A ≠ B → (A ∩ B).card ≤ s) :
    ∑ x : Fin n, (S.filter (fun A => x ∈ A)).card
      ≤ n + s * (S.card * (S.card - 1)) := by
  classical
  have hpt : ∀ x : Fin n, (S.filter (fun A => x ∈ A)).card
      ≤ 1 + (S.filter (fun A => x ∈ A)).card
        * ((S.filter (fun A => x ∈ A)).card - 1) := by
    intro x
    set d := (S.filter (fun A => x ∈ A)).card
    rcases Nat.eq_zero_or_pos d with h0 | h
    · omega
    · have h1 : d - 1 ≤ d * (d - 1) := Nat.le_mul_of_pos_left _ h
      omega
  calc ∑ x : Fin n, (S.filter (fun A => x ∈ A)).card
      ≤ ∑ x : Fin n, (1 + (S.filter (fun A => x ∈ A)).card
          * ((S.filter (fun A => x ∈ A)).card - 1)) :=
        Finset.sum_le_sum fun x _ => hpt x
  _ = n + ∑ x : Fin n, (S.filter (fun A => x ∈ A)).card
        * ((S.filter (fun A => x ∈ A)).card - 1) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul, mul_one]
  _ ≤ n + s * (S.card * (S.card - 1)) :=
      Nat.add_le_add_left (crossing_double_count_general hpair) _

end ProximityGap.PairRank

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.PairRank.crossing_double_count_general
#print axioms ProximityGap.PairRank.degree_sum_le_general
