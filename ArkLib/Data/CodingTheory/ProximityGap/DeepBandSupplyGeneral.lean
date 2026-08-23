/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MeanDegreeGeneral
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandSupplyTheorem

/-!
# THE DEEP-BAND SUPPLY THEOREM AT EVERY RATE (#389)

The general-`k` assembly: `mean_degree_law_deep_general` (`s = k−1`, `t = k+m+1`,
`cap = 2k+m+1`) wired through the unique-explainer cover and convexity into the
capped supply at every rate:

> **`subJohnsonSupplyResidual_deep_band_general`** — for `1 ≤ k` and bands with
> `2(k−1)·(2k+m+1)·C(n,k−1)·(n−k+1) ≤ (k+m+1)²·(m+2)·C(k+m+1,k−1)`:
> every agreement-capped word's explainable-core count `E` satisfies
> **`E·(k+m+1) ≤ 2n·C(2k+m, k+m)`** — the charter statement with linear `B`,
> at every rate on its deep range.

The shallow bands remain the open wall.  Issue #389.
-/

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.PairRank

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership Code

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- **THE DEEP-BAND SUPPLY THEOREM, EVERY RATE.**  Under the general deep condition,
every agreement-capped word has explainable-core count `E` with
`E·(k+m+1) ≤ 2n·C(2k+m, k+m)`. -/
theorem subJohnsonSupplyResidual_deep_band_general (dom : Fin n ↪ F) {k : ℕ}
    (hk : 1 ≤ k) (m : ℕ)
    (hdeep : 2 * (k - 1) * (2 * k + m + 1) * ((n.choose (k - 1)) * (n - (k - 1)))
      ≤ (k + m + 1) ^ 2 * (((k + m + 1) - (k - 1)) * (k + m + 1).choose (k - 1)))
    (hk2 : 2 ≤ k)
    {w : Fin n → F}
    (hcap : ∀ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
      (agreeSet c w).card ≤ 2 * k + m + 1) :
    (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
        (fun T => ExplainableOn dom k w T)).card * (k + m + 1)
      ≤ 2 * n * (2 * k + m).choose (k + m) := by
  classical
  set t := k + m + 1 with hT
  set Cw : Finset (Fin n → F) := (Finset.univ : Finset (Fin n → F)).filter
    (fun c => c ∈ (rsCode dom k : Submodule F (Fin n → F))
      ∧ t ≤ (agreeSet c w).card) with hCw
  set S : Finset (Finset (Fin n)) := Cw.image (fun c => agreeSet c w) with hS
  have hSsize : ∀ A ∈ S, t ≤ A.card := by
    intro A hA
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hA
    exact (Finset.mem_filter.mp hc).2.2
  have hScap : ∀ A ∈ S, A.card ≤ 2 * k + m + 1 := by
    intro A hA
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hA
    exact hcap c (Finset.mem_filter.mp hc).2.1
  have hSpair : ∀ A ∈ S, ∀ B ∈ S, A ≠ B → (A ∩ B).card ≤ k - 1 := by
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
    _ ≤ k - 1 := rsCode_pairwise_agreeSet_card_le dom hk h1 h2 hcc'
  -- the general mean-degree law
  have hmean : ∑ A ∈ S, A.card ≤ 2 * n := by
    refine mean_degree_law_deep_general (s := k - 1) (cap := 2 * k + m + 1)
      (by omega) (by omega) hSsize hScap hSpair ?_
    rw [hT]
    exact hdeep
  -- cover and count (verbatim from the k = 2 assembly)
  have hcover : ∀ T ∈ ((Finset.univ : Finset (Fin n)).powersetCard t).filter
      (fun T => ExplainableOn dom k w T), ∃ A ∈ S, T ⊆ A := by
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
  have hcount : (((Finset.univ : Finset (Fin n)).powersetCard t).filter
      (fun T => ExplainableOn dom k w T)).card
      ≤ ∑ A ∈ S, A.card.choose t := by
    have hsub : ((Finset.univ : Finset (Fin n)).powersetCard t).filter
        (fun T => ExplainableOn dom k w T)
        ⊆ S.biUnion (fun A => A.powersetCard t) := by
      intro T hT'
      obtain ⟨A, hA, hTA⟩ := hcover T hT'
      refine Finset.mem_biUnion.mpr ⟨A, hA, Finset.mem_powersetCard.mpr ⟨hTA, ?_⟩⟩
      exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hT').1).2
    calc (((Finset.univ : Finset (Fin n)).powersetCard t).filter
        (fun T => ExplainableOn dom k w T)).card
        ≤ (S.biUnion (fun A => A.powersetCard t)).card := Finset.card_le_card hsub
    _ ≤ ∑ A ∈ S, (A.powersetCard t).card := Finset.card_biUnion_le
    _ = ∑ A ∈ S, A.card.choose t := by
        refine Finset.sum_congr rfl fun A _ => ?_
        exact Finset.card_powersetCard _ _
  -- convexity
  have hconv : (∑ A ∈ S, A.card.choose t) * t
      ≤ 2 * n * (2 * k + m).choose (k + m) := by
    calc (∑ A ∈ S, A.card.choose t) * t = ∑ A ∈ S, A.card.choose t * t := by
          rw [Finset.sum_mul]
    _ ≤ ∑ A ∈ S, A.card * (2 * k + m).choose (t - 1) := by
          refine Finset.sum_le_sum fun A hA => ?_
          have h := choose_mul_le_of_le (c := 2 * k + m + 1) (hScap A hA)
            (by omega : 1 ≤ t)
          rwa [show 2 * k + m + 1 - 1 = 2 * k + m from by omega] at h
    _ = (∑ A ∈ S, A.card) * (2 * k + m).choose (t - 1) := by rw [Finset.sum_mul]
    _ ≤ 2 * n * (2 * k + m).choose (t - 1) := Nat.mul_le_mul_right _ hmean
    _ = 2 * n * (2 * k + m).choose (k + m) := by
          rw [show t - 1 = k + m from by omega]
  calc (((Finset.univ : Finset (Fin n)).powersetCard t).filter
      (fun T => ExplainableOn dom k w T)).card * t
      ≤ (∑ A ∈ S, A.card.choose t) * t := Nat.mul_le_mul_right _ hcount
  _ ≤ 2 * n * (2 * k + m).choose (k + m) := hconv

end ProximityGap.PairRank

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.PairRank.subJohnsonSupplyResidual_deep_band_general
