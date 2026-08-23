/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MeanDegreeDeepBand
import ArkLib.Data.CodingTheory.ProximityGap.SubJohnsonResidualFloor

/-!
# THE DEEP-BAND SUPPLY THEOREM (#389): the capped residual holds with linear `B`

The assembly: `mean_degree_law_deep` + the unique-explainer partition + per-set
convexity wire into the issue's named residual at `k = 2`:

> **`subJohnsonSupplyResidual_deep_band`** — for bands with `2n² ≤ (m+3)²(m+2)`:
> `SubJohnsonSupplyResidual dom 2 m B` holds with **`B·(m+3) = 2n·C(2m+6, m+2)`**-shape
> (stated multiplicatively: every capped word's explainable-core count `E` satisfies
> `E·(m+3) ≤ 2n·C(cap−1, t−1)`, `cap = m+5`, `t = m+3`) — **the charter statement,
> PROVEN on the deep-band range, with `B` linear in `n`.**

Chain: every explainable core lies in the agreement set of its unique explainer
(`explainable_core_explainer_unique`), those agreement sets are pairwise
`≤ 1`-intersecting (`rsCode_pairwise_agreeSet_card_le` at `k = 2`) and `≥ t`-sized,
so `mean_degree_law_deep` bounds their total size by `2n`; the agreement cap bounds
each size by `cap`, and `C(a, t)·t ≤ a·C(cap−1, t−1)` (convexity) converts size mass
into core counts.

The shallow bands `2n² > t²(t−1)` remain the open wall.  Issue #389.
-/

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.PairRank

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership Code

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- Convexity step: `C(a, t)·t ≤ a·C(c−1, t−1)` for `a ≤ c`, `1 ≤ t`. -/
theorem choose_mul_le_of_le {a c t : ℕ} (hac : a ≤ c) (ht : 1 ≤ t) :
    a.choose t * t ≤ a * (c - 1).choose (t - 1) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rcases Nat.eq_zero_or_pos t with rfl | ht'
    · omega
    · rw [Nat.choose_eq_zero_of_lt ht']
      omega
  · have hkey : a.choose t * t = a * (a - 1).choose (t - 1) := by
      have h0 := Nat.succ_mul_choose_eq (a - 1) (t - 1)
      simp only [Nat.succ_eq_add_one] at h0
      rw [show a - 1 + 1 = a from by omega, show t - 1 + 1 = t from by omega] at h0
      omega
    rw [hkey]
    exact Nat.mul_le_mul_left _ (Nat.choose_le_choose _ (by omega))

open Classical in
/-- **THE DEEP-BAND SUPPLY THEOREM** (`k = 2`).  On bands with
`2n² ≤ (m+3)²·(m+2)`, every agreement-capped word has explainable-core count `E`
with `E·(m+3) ≤ 2n·C(m+4, m+2)` — the capped supply is linear in `n`. -/
theorem subJohnsonSupplyResidual_deep_band (dom : Fin n ↪ F) (m : ℕ)
    (hdeep : 2 * n ^ 2 ≤ (m + 3) ^ 2 * (m + 2))
    {w : Fin n → F}
    (hcap : ∀ c ∈ (rsCode dom 2 : Submodule F (Fin n → F)),
      (agreeSet c w).card ≤ 2 * 2 + m + 1) :
    (((Finset.univ : Finset (Fin n)).powersetCard (2 + m + 1)).filter
        (fun T => ExplainableOn dom 2 w T)).card * (m + 3)
      ≤ 2 * n * (m + 4).choose (m + 2) := by
  classical
  set t := 2 + m + 1 with hT
  -- the family of large agreement sets
  set Cw : Finset (Fin n → F) := (Finset.univ : Finset (Fin n → F)).filter
    (fun c => c ∈ (rsCode dom 2 : Submodule F (Fin n → F))
      ∧ t ≤ (agreeSet c w).card) with hCw
  set S : Finset (Finset (Fin n)) := Cw.image (fun c => agreeSet c w) with hS
  -- the family is pairwise ≤1-intersecting and ≥t-sized
  have hSsize : ∀ A ∈ S, t ≤ A.card := by
    intro A hA
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hA
    exact (Finset.mem_filter.mp hc).2.2
  have hSpair : ∀ A ∈ S, ∀ B ∈ S, A ≠ B → (A ∩ B).card ≤ 1 := by
    intro A hA B hB hne
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨c', hc', rfl⟩ := Finset.mem_image.mp hB
    have hcc' : c ≠ c' := fun h => hne (by rw [h])
    have h1 := (Finset.mem_filter.mp hc).2.1
    have h2 := (Finset.mem_filter.mp hc').2.1
    have hsub : agreeSet c w ∩ agreeSet c' w ⊆ agreeSet c c' := by
      intro i hi
      obtain ⟨hi1, hi2⟩ := Finset.mem_inter.mp hi
      have e1 := (Finset.mem_filter.mp hi1).2
      have e2 := (Finset.mem_filter.mp hi2).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [e1, e2]⟩
    calc (agreeSet c w ∩ agreeSet c' w).card
        ≤ (agreeSet c c').card := Finset.card_le_card hsub
    _ ≤ 2 - 1 := rsCode_pairwise_agreeSet_card_le dom (by omega) h1 h2 hcc'
    _ ≤ 1 := by omega
  -- mean-degree law: total size ≤ 2n
  have hmean : ∑ A ∈ S, A.card ≤ 2 * n := by
    refine mean_degree_law_deep (by omega) hSsize hSpair ?_
    rw [hT, show 2 + m + 1 = m + 3 from by omega,
      show m + 3 - 1 = m + 2 from by omega]
    exact hdeep
  -- every explainable core is a t-subset of some member of S
  have hcover : ∀ T ∈ ((Finset.univ : Finset (Fin n)).powersetCard t).filter
      (fun T => ExplainableOn dom 2 w T), ∃ A ∈ S, T ⊆ A := by
    intro T hT'
    obtain ⟨hTmem, hTexp⟩ := Finset.mem_filter.mp hT'
    obtain ⟨hTsub, hTcard⟩ := Finset.mem_powersetCard.mp hTmem
    obtain ⟨c, hcmem, hcag⟩ := hTexp
    refine ⟨agreeSet c w, ?_, ?_⟩
    · refine Finset.mem_image.mpr ⟨c, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hcmem, ?_⟩, rfl⟩
      calc t = T.card := hTcard.symm
      _ ≤ (agreeSet c w).card := Finset.card_le_card (fun i hi =>
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcag i hi⟩)
    · intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcag i hi⟩
  -- count: cores ≤ Σ_{A ∈ S} C(|A|, t)
  have hcount : (((Finset.univ : Finset (Fin n)).powersetCard t).filter
      (fun T => ExplainableOn dom 2 w T)).card
      ≤ ∑ A ∈ S, A.card.choose t := by
    have hsub : ((Finset.univ : Finset (Fin n)).powersetCard t).filter
        (fun T => ExplainableOn dom 2 w T)
        ⊆ S.biUnion (fun A => A.powersetCard t) := by
      intro T hT'
      obtain ⟨A, hA, hTA⟩ := hcover T hT'
      refine Finset.mem_biUnion.mpr ⟨A, hA, Finset.mem_powersetCard.mpr ⟨hTA, ?_⟩⟩
      exact (Finset.mem_powersetCard.mp
        (Finset.mem_filter.mp hT').1).2
    calc (((Finset.univ : Finset (Fin n)).powersetCard t).filter
        (fun T => ExplainableOn dom 2 w T)).card
        ≤ (S.biUnion (fun A => A.powersetCard t)).card := Finset.card_le_card hsub
    _ ≤ ∑ A ∈ S, (A.powersetCard t).card := Finset.card_biUnion_le
    _ = ∑ A ∈ S, A.card.choose t := by
        refine Finset.sum_congr rfl fun A _ => ?_
        exact Finset.card_powersetCard _ _
  -- convexity: Σ C(|A|,t)·t ≤ Σ |A|·C(cap−1,t−1) ≤ 2n·C(m+4, m+2)
  have hconv : (∑ A ∈ S, A.card.choose t) * t ≤ 2 * n * (m + 4).choose (m + 2) := by
    have hAcap : ∀ A ∈ S, A.card ≤ m + 5 := by
      intro A hA
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hA
      have := hcap c (Finset.mem_filter.mp hc).2.1
      omega
    calc (∑ A ∈ S, A.card.choose t) * t = ∑ A ∈ S, A.card.choose t * t := by
          rw [Finset.sum_mul]
    _ ≤ ∑ A ∈ S, A.card * (m + 4).choose (t - 1) := by
          refine Finset.sum_le_sum fun A hA => ?_
          have h := choose_mul_le_of_le (c := m + 5) (hAcap A hA) (by omega : 1 ≤ t)
          rwa [show m + 5 - 1 = m + 4 from by omega] at h
    _ = (∑ A ∈ S, A.card) * (m + 4).choose (t - 1) := by rw [Finset.sum_mul]
    _ ≤ 2 * n * (m + 4).choose (t - 1) := Nat.mul_le_mul_right _ hmean
    _ = 2 * n * (m + 4).choose (m + 2) := by
          congr 2
          omega
  have hmt : m + 3 = t := by omega
  rw [hmt]
  calc (((Finset.univ : Finset (Fin n)).powersetCard t).filter
      (fun T => ExplainableOn dom 2 w T)).card * t
      ≤ (∑ A ∈ S, A.card.choose t) * t := Nat.mul_le_mul_right _ hcount
  _ ≤ 2 * n * (m + 4).choose (m + 2) := hconv

end ProximityGap.PairRank

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.PairRank.choose_mul_le_of_le
#print axioms ProximityGap.PairRank.subJohnsonSupplyResidual_deep_band
