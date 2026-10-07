/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Chung Thai Nguyen
-/
import ArkLib.Data.CodingTheory.Basic.Distance

/-!
# Minimum block distance of rowwise codes

Adapted from ArkLib main `35ddcaa83f683011f944f58904be779495a5709a`.
This set-based form is independent of the matrix interleaving interface. A nonempty
row index preserves minimum distance, including the empty/subsingleton-code cases.
-/

namespace Code

/-- Interleaving over a nonempty row index preserves minimum block distance:
`minDist (interleavedCodeSet C) = minDist C`.

For `≥`, two distinct interleaved words differ in some row, whose Hamming distance is bounded
by their block distance. For `≤`, place a minimum-distance base pair in one row and repeat
one endpoint in every other row. The subsingleton case is handled separately, both sides
being zero there. -/
theorem minDist_rowwiseCode
    {κ ι A : Type*} [Fintype κ] [Nonempty κ] [Fintype ι] [DecidableEq A]
    (C : Set (ι → A)) :
    minDist {V : ι → κ → A | ∀ k, (fun i ↦ V i k) ∈ C} = minDist C := by
  classical
  let IC : Set (ι → κ → A) := {V | ∀ k, (fun i ↦ V i k) ∈ C}
  change minDist IC = minDist C
  by_cases hC : Set.Nontrivial C
  · obtain ⟨u, hu, v, hv, huv⟩ := hC
    let k0 : κ := Classical.choice ‹Nonempty κ›
    let U : ι → κ → A := fun i _ ↦ u i
    let V : ι → κ → A := fun i k ↦ if k = k0 then v i else u i
    have hU : U ∈ IC := by
      intro k
      change (fun i ↦ u i) ∈ C
      exact hu
    have hV : V ∈ IC := by
      intro k
      by_cases hk : k = k0
      · subst k
        change (fun i ↦ if k0 = k0 then v i else u i) ∈ C
        simpa using hv
      · change (fun i ↦ if k = k0 then v i else u i) ∈ C
        simp [hk, hu]
    have hUV : U ≠ V := by
      intro h
      apply huv
      funext i
      have := congrFun (congrFun h i) k0
      simpa [U, V] using this
    have hupper : minDist IC ≤ minDist C := by
      have hS : {d | ∃ x ∈ C, ∃ y ∈ C, x ≠ y ∧ hammingDist x y = d}.Nonempty :=
        ⟨hammingDist u v, u, hu, v, hv, huv, rfl⟩
      have hmem : ∃ x ∈ C, ∃ y ∈ C, x ≠ y ∧ hammingDist x y = minDist C := by
        exact Nat.sInf_mem hS
      obtain ⟨x, hx, y, hy, hxy, hdist⟩ := hmem
      let X : ι → κ → A := fun i _ ↦ x i
      let Y : ι → κ → A := fun i k ↦ if k = k0 then y i else x i
      have hX : X ∈ IC := by
        intro k
        change (fun i ↦ x i) ∈ C
        exact hx
      have hY : Y ∈ IC := by
        intro k
        by_cases hk : k = k0
        · subst k
          change (fun i ↦ if k0 = k0 then y i else x i) ∈ C
          simpa using hy
        · change (fun i ↦ if k = k0 then y i else x i) ∈ C
          simp [hk, hx]
      have hXY : X ≠ Y := by
        intro h
        apply hxy
        funext i
        have := congrFun (congrFun h i) k0
        simpa [X, Y] using this
      apply Nat.sInf_le
      refine ⟨X, hX, Y, hY, hXY, ?_⟩
      rw [← hdist]
      unfold hammingDist
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hne hxy_i
        apply hne
        funext k
        simp [X, Y, hxy_i]
      · intro hxy_i hEq
        apply hxy_i
        have := congrFun hEq k0
        simpa [X, Y] using this
    have hSIC : {d | ∃ x ∈ IC, ∃ y ∈ IC, x ≠ y ∧ hammingDist x y = d}.Nonempty :=
      ⟨hammingDist U V, U, hU, V, hV, hUV, rfl⟩
    have hmemIC : ∃ X ∈ IC, ∃ Y ∈ IC, X ≠ Y ∧ hammingDist X Y = minDist IC := by
      exact Nat.sInf_mem hSIC
    obtain ⟨X, hX, Y, hY, hXY, hdist⟩ := hmemIC
    have hex : ∃ i k, X i k ≠ Y i k := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hXY
      obtain ⟨k, hk⟩ := Function.ne_iff.mp hi
      exact ⟨i, k, hk⟩
    obtain ⟨i0, k, hik⟩ := hex
    have hrow : (fun i ↦ X i k) ≠ fun i ↦ Y i k := by
      intro h
      exact hik (congrFun h i0)
    have hlower : minDist C ≤ minDist IC := by
      calc
        minDist C ≤ hammingDist (fun i ↦ X i k) (fun i ↦ Y i k) := by
          apply Nat.sInf_le
          exact ⟨_, hX k, _, hY k, hrow, rfl⟩
        _ ≤ hammingDist X Y := by
          unfold hammingDist
          apply Finset.card_le_card
          intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
          intro h
          exact hi (congrFun h k)
        _ = minDist IC := hdist
    exact le_antisymm hupper hlower
  · have hCsub : Set.Subsingleton C := Set.not_nontrivial_iff.mp hC
    have hICsub : Set.Subsingleton IC := by
      intro U hU V hV
      funext i k
      have h := hCsub (hU k) (hV k)
      exact congrFun h i
    have hbase : minDist C = 0 := by
      unfold minDist
      have hempty : {d | ∃ x ∈ C, ∃ y ∈ C, x ≠ y ∧ hammingDist x y = d} = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro d ⟨x, hx, y, hy, hxy, -⟩
        exact hxy (hCsub hx hy)
      rw [hempty, Nat.sInf_empty]
    have hinter : minDist IC = 0 := by
      unfold minDist
      have hempty : {d | ∃ x ∈ IC, ∃ y ∈ IC, x ≠ y ∧ hammingDist x y = d} = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro d ⟨x, hx, y, hy, hxy, -⟩
        exact hxy (hICsub hx hy)
      rw [hempty, Nat.sInf_empty]
    rw [hbase, hinter]

end Code
