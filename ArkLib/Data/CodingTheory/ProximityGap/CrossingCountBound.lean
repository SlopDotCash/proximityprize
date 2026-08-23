/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.PencilDegreeBound

/-!
# The crossing double-count (#389, the deep-band supply proof, brick 1)

The deep-band derivation (issue thread) proves the mean-degree law for
`t ≳ (n²/2)^{1/3}` from three elementary inequalities.  This file lands the first
two in Lean:

> **`crossing_double_count`** — for a family `S` of subsets of `[n]` pairwise
> intersecting in `≤ 1` point, the pencil degrees `d_x = #{A ∈ S : x ∈ A}` satisfy
> `Σ_x d_x·(d_x − 1) ≤ |S|·(|S|−1)`: summing the crossing incidences pairwise.

> **`degree_sum_le`** — with the pointwise `d ≤ 1 + d(d−1)`:
> `Σ_x d_x ≤ n + |S|·(|S|−1)` — the Bonferroni step of the derivation.

The quadratic branch analysis joining these to the landed pencil bound (the
deep-band supply theorem) is registered brick 2.  Issue #389.
-/

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.PairRank

variable {n : ℕ} [NeZero n]

open Classical in
/-- The off-diagonal pair count: `#{(A,B) ∈ S² : A ≠ B} = |S|·(|S|−1)`. -/
theorem offdiag_card (S : Finset (Finset (Fin n))) :
    ((S ×ˢ S).filter (fun p => p.1 ≠ p.2)).card = S.card * (S.card - 1) := by
  classical
  have hsplit : ((S ×ˢ S).filter (fun p => p.1 = p.2)).card
      + ((S ×ˢ S).filter (fun p => ¬ p.1 = p.2)).card = (S ×ˢ S).card :=
    Finset.filter_card_add_filter_neg_card_eq_card (s := S ×ˢ S)
      (p := fun p => p.1 = p.2)
  have hdiag : ((S ×ˢ S).filter (fun p => p.1 = p.2)).card = S.card := by
    refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
    · intro p hp
      exact (Finset.mem_product.mp (Finset.filter_subset _ _ hp)).1
    · intro p hp p' hp' he
      have he' : p.1 = p'.1 := he
      have h1 : p.1 = p.2 := (Finset.mem_filter.mp hp).2
      have h2 : p'.1 = p'.2 := (Finset.mem_filter.mp hp').2
      exact Prod.ext_iff.mpr ⟨he', by rw [← h1, ← h2, he']⟩
    · intro A hA
      exact ⟨(A, A), Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hA, hA⟩, rfl⟩, rfl⟩
  have hprod : (S ×ˢ S).card = S.card * S.card := Finset.card_product _ _
  have hmul : S.card * S.card - S.card = S.card * (S.card - 1) := by
    cases hS : S.card with
    | zero => rfl
    | succ d =>
      rw [Nat.succ_sub_one, Nat.mul_succ, Nat.mul_comm (d + 1) d]
      omega
  simp only [ne_eq]
  omega

open Classical in
/-- **The crossing double-count**: for a family pairwise intersecting in `≤ 1` point,
`Σ_x d_x(d_x−1) ≤ |S|(|S|−1)`. -/
theorem crossing_double_count {S : Finset (Finset (Fin n))}
    (hpair : ∀ A ∈ S, ∀ B ∈ S, A ≠ B → (A ∩ B).card ≤ 1) :
    ∑ x : Fin n, ((S.filter (fun A => x ∈ A)).card
        * ((S.filter (fun A => x ∈ A)).card - 1))
      ≤ S.card * (S.card - 1) := by
  classical
  -- per-point: d_x(d_x−1) = #off-diagonal pairs through x
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
  -- swap: Σ_x #{pairs through x} = Σ_{pairs} |A ∩ B| ≤ #pairs · 1
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
      ≤ ∑ p ∈ (S ×ˢ S).filter (fun p => p.1 ≠ p.2), 1 := by
        refine Finset.sum_le_sum fun p hp => ?_
        obtain ⟨hpmem, hne⟩ := Finset.mem_filter.mp hp
        rcases Finset.mem_product.mp hpmem with ⟨h1, h2⟩
        exact hpair p.1 h1 p.2 h2 hne
  _ = ((S ×ˢ S).filter (fun p => p.1 ≠ p.2)).card := by
        rw [Finset.sum_const, smul_eq_mul, mul_one]
  _ = S.card * (S.card - 1) := offdiag_card S

open Classical in
/-- **The Bonferroni step**: `Σ_x d_x ≤ n + |S|(|S|−1)` (pointwise `d ≤ 1 + d(d−1)`). -/
theorem degree_sum_le {S : Finset (Finset (Fin n))}
    (hpair : ∀ A ∈ S, ∀ B ∈ S, A ≠ B → (A ∩ B).card ≤ 1) :
    ∑ x : Fin n, (S.filter (fun A => x ∈ A)).card
      ≤ n + S.card * (S.card - 1) := by
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
  _ ≤ n + S.card * (S.card - 1) :=
      Nat.add_le_add_left (crossing_double_count hpair) _

end ProximityGap.PairRank

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.PairRank.crossing_double_count
#print axioms ProximityGap.PairRank.degree_sum_le
