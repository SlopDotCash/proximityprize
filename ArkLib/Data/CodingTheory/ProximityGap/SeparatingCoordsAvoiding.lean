/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.SubspaceDesignFullVanish

/-!
# Separating coordinates avoiding a forbidden set (issue #389, GG25 §4.3 toward B2)

The **deterministic skeleton of the GG25 §4.3 / `[KRSW23, Tam24]` `η^r` separation**: a
dimension-`r` subspace `H` of a `τ`-subspace-design `C` is separated by at most `r` coordinates
chosen entirely **outside any forbidden set** `Bad` — provided there is room,
`|Bad| + θ·n + r ≤ n`, where `θ` uniformly bounds `τ`.

`exists_separating_coords_avoiding`. The proof is the peeling induction of `SeparatingCoordinates`
upgraded with the design's coordinate budget: at each step the dimension-`r'` subspace fully
vanishes on at most `τ(r')·n ≤ θ·n` coordinates (`subspaceDesign_fullVanish_card_le`), so the
forbidden union `Bad ∪ (fully-vanishing)` misses at least `n − |Bad| − θ·n ≥ r > 0` coordinates;
pick a fresh good one outside `Bad`, peel, and the room bound is preserved (`Bad` grows by one as
`r` drops by one). This is the deterministic core the probabilistic `η^r` separation bound rests on
(at each of the `r` peeling steps a `(1 − τ)`-fraction of coordinates is available).

Axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

open Finset CodingTheory

namespace ProximityGap

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι] {F : Type} [Field F]

open Classical in
theorem exists_separating_coords_avoiding {s : ℕ} {τ : ℕ → ℝ} {θ : ℝ}
    {C : Submodule F (ι → Fin s → F)} (h : IsSubspaceDesign s τ C) (hθ : ∀ j, τ j ≤ θ)
    (r : ℕ) (H : Submodule F (ι → Fin s → F)) (hHC : H ≤ C) (hr : Module.finrank F H ≤ r)
    (Bad : Finset ι)
    (hroom : (Bad.card : ℝ) + θ * Fintype.card ι + r ≤ Fintype.card ι) :
    ∃ S : Finset ι, S.card ≤ r ∧ Disjoint S Bad ∧
      H ⊓ (⨅ i ∈ S, LinearMap.ker
        (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) = ⊥ := by
  induction r generalizing H Bad with
  | zero =>
    refine ⟨∅, le_refl _, Finset.disjoint_empty_left _, ?_⟩
    have hH : H = ⊥ := Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hr)
    simp [hH]
  | succ k ih =>
    by_cases hH : H = ⊥
    · exact ⟨∅, Nat.zero_le _, Finset.disjoint_empty_left _, by simp [hH]⟩
    · have hrank1 : 1 ≤ Module.finrank F H := by
        rw [Nat.one_le_iff_ne_zero]; exact fun h0 => hH (Submodule.finrank_eq_zero.mp h0)
      set full := univ.filter (fun i : ι => H ≤ LinearMap.ker
        (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) with hfulldef
      have hfv : (full.card : ℝ) ≤ θ * Fintype.card ι :=
        le_trans (subspaceDesign_fullVanish_card_le h hrank1 hHC rfl)
          (mul_le_mul_of_nonneg_right (hθ _) (by positivity))
      -- the union of forbidden + fully-vanishing coords is smaller than the whole domain
      have hlt : (Bad ∪ full).card < Fintype.card ι := by
        have hub : ((Bad ∪ full).card : ℝ) < (Fintype.card ι : ℝ) := by
          have hcu : ((Bad ∪ full).card : ℝ) ≤ (Bad.card : ℝ) + (full.card : ℝ) := by
            exact_mod_cast Finset.card_union_le Bad full
          have hk1 : (0 : ℝ) ≤ (k : ℝ) := by positivity
          push_cast at hroom
          linarith
        exact_mod_cast hub
      have hne : (Bad ∪ full) ≠ univ := by
        intro heq; rw [heq, Finset.card_univ] at hlt; exact lt_irrefl _ hlt
      have hexi : ∃ i₀ : ι, i₀ ∉ Bad ∪ full := by
        by_contra hcon; push_neg at hcon
        exact hne (Finset.eq_univ_iff_forall.mpr hcon)
      obtain ⟨i₀, hi₀⟩ := hexi
      rw [Finset.mem_union, not_or] at hi₀
      obtain ⟨hi₀Bad, hi₀full⟩ := hi₀
      have hi₀ker : ¬ (H ≤ LinearMap.ker
          (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i₀)) := by
        simpa [hfulldef] using hi₀full
      set Ki : Submodule F (ι → Fin s → F) :=
        LinearMap.ker (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i₀) with hKi
      have hlt' : H ⊓ Ki < H := lt_of_le_of_ne inf_le_left (fun heq => hi₀ker (heq ▸ inf_le_right))
      have hdrop : Module.finrank F (H ⊓ Ki : Submodule F (ι → Fin s → F)) ≤ k := by
        have := Submodule.finrank_lt_finrank_of_lt hlt'; omega
      have hroom' : ((insert i₀ Bad).card : ℝ) + θ * Fintype.card ι + k ≤ Fintype.card ι := by
        rw [Finset.card_insert_of_notMem hi₀Bad]; push_cast at hroom ⊢; linarith
      obtain ⟨S', hS'card, hS'dis, hS'sep⟩ :=
        ih (H ⊓ Ki) (le_trans inf_le_left hHC) hdrop (insert i₀ Bad) hroom'
      refine ⟨insert i₀ S', (Finset.card_insert_le _ _).trans (Nat.succ_le_succ hS'card), ?_, ?_⟩
      · rw [Finset.disjoint_insert_left]
        exact ⟨hi₀Bad, hS'dis.mono_right (Finset.subset_insert _ _)⟩
      · rw [Finset.iInf_insert]
        rw [show H ⊓ (Ki ⊓ ⨅ i ∈ S', LinearMap.ker
              (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i))
            = (H ⊓ Ki) ⊓ ⨅ i ∈ S', LinearMap.ker
              (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i) from by rw [← inf_assoc]]
        exact hS'sep

end ProximityGap

#print axioms ProximityGap.exists_separating_coords_avoiding
