/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib

/-!
# Greedy disjoint-cover bound

A pure-combinatorial brick for greedy chain-extraction arguments (the structural spine of
the CZ25 dimension count, issue #93, and similar list-decoding recentring arguments).

The setup: a chain of `m` elements, the `i`-th of which "covers" a finset `cover i ⊆ univ`
of fresh coordinates; the covers are pairwise disjoint, each has size `≥ η`, and their union
sits inside a budget set of size `≤ M`.  Then `m·η ≤ M`, hence `m ≤ M / η`.

This is exactly the accounting BKR06/CZ25-style greedy arguments need: each newly-extracted
close codeword (after recentring) contributes `≥ η·n` agreement coordinates disjoint from the
previously-covered ones, and the total agreement mass is bounded by the design budget
`(1 − τ(r₀))·n`, forcing the chain length `≤ (1 − τ(r₀))/η`.

All declarations are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/

namespace GreedyDisjointCover

open Finset BigOperators

variable {ι κ : Type*} [DecidableEq κ] [Fintype κ]

/-- **Disjoint covers fit in their union.**  If the `cover i` (`i ∈ s`) are pairwise
disjoint, then `∑_{i ∈ s} #(cover i) = #(⋃ cover i)`. -/
theorem sum_card_eq_card_biUnion_of_disjoint
    (s : Finset ι) (cover : ι → Finset κ)
    (hdisj : (s : Set ι).Pairwise (fun i j => Disjoint (cover i) (cover j))) :
    ∑ i ∈ s, (cover i).card = (s.biUnion cover).card := by
  rw [Finset.card_biUnion]
  intro i hi j hj hij
  exact hdisj hi hj hij

/-- **Greedy disjoint-cover bound (sum form).**  If each of the `m := #s` covers has size
`≥ η` and the covers are pairwise disjoint with union inside a budget set `B` of size `≤ M`,
then `m · η ≤ M`. -/
theorem card_mul_le_of_disjoint_covers
    (s : Finset ι) (cover : ι → Finset κ) (B : Finset κ) (η M : ℕ)
    (hdisj : (s : Set ι).Pairwise (fun i j => Disjoint (cover i) (cover j)))
    (hsize : ∀ i ∈ s, η ≤ (cover i).card)
    (hsub : ∀ i ∈ s, cover i ⊆ B)
    (hM : B.card ≤ M) :
    s.card * η ≤ M := by
  classical
  -- `m·η ≤ ∑ #(cover i) = #(⋃ cover i) ≤ #B ≤ M`
  have hsum_ge : s.card * η ≤ ∑ i ∈ s, (cover i).card := by
    calc s.card * η = ∑ _i ∈ s, η := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ i ∈ s, (cover i).card := Finset.sum_le_sum hsize
  have hunion_le : (s.biUnion cover).card ≤ B.card := by
    apply Finset.card_le_card
    intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨i, hi, hxi⟩ := hx
    exact hsub i hi hxi
  rw [sum_card_eq_card_biUnion_of_disjoint s cover hdisj] at hsum_ge
  exact le_trans hsum_ge (le_trans hunion_le hM)

/-- **Greedy chain-length bound (real form).**  Under the disjoint-cover hypotheses with a
positive coordinate-mass `η > 0`, the chain length `m := #s` satisfies `m ≤ M / η` over `ℝ`.
This is the shape consumed by list-decoding dimension counts: `m ≤ (1 − τ(r₀))·n / (η·n)`. -/
theorem card_le_div_of_disjoint_covers
    (s : Finset ι) (cover : ι → Finset κ) (B : Finset κ) (η M : ℕ) (hη : 0 < η)
    (hdisj : (s : Set ι).Pairwise (fun i j => Disjoint (cover i) (cover j)))
    (hsize : ∀ i ∈ s, η ≤ (cover i).card)
    (hsub : ∀ i ∈ s, cover i ⊆ B)
    (hM : B.card ≤ M) :
    (s.card : ℝ) ≤ (M : ℝ) / (η : ℝ) := by
  have hmul : s.card * η ≤ M :=
    card_mul_le_of_disjoint_covers s cover B η M hdisj hsize hsub hM
  have hηR : (0 : ℝ) < η := by exact_mod_cast hη
  rw [le_div_iff₀ hηR]
  calc (s.card : ℝ) * (η : ℝ) = ((s.card * η : ℕ) : ℝ) := by push_cast; ring
    _ ≤ (M : ℝ) := by exact_mod_cast hmul

/-- **Real-mass variant.**  The same bound stated with real-valued lower mass `δ : ℝ`
(`0 < δ`) per cover and a real budget `M : ℝ`: if each cover has card `≥ δ` and the disjoint
union has total card `≤ M`, then `#s ≤ M / δ`.  (Coordinate counts are naturals; the masses
and budget are reals, matching the `(1 − τ)·n` / `η·n` bookkeeping.) -/
theorem card_le_div_of_disjoint_covers_real
    (s : Finset ι) (cover : ι → Finset κ) (δ M : ℝ) (hδ : 0 < δ)
    (hdisj : (s : Set ι).Pairwise (fun i j => Disjoint (cover i) (cover j)))
    (hsize : ∀ i ∈ s, δ ≤ ((cover i).card : ℝ))
    (hbudget : ((s.biUnion cover).card : ℝ) ≤ M) :
    (s.card : ℝ) ≤ M / δ := by
  classical
  rw [le_div_iff₀ hδ]
  have hsum_ge : (s.card : ℝ) * δ ≤ ∑ i ∈ s, ((cover i).card : ℝ) := by
    calc (s.card : ℝ) * δ = ∑ _i ∈ s, δ := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ s, ((cover i).card : ℝ) := Finset.sum_le_sum hsize
  have hsum_eq : ∑ i ∈ s, ((cover i).card : ℝ) = ((s.biUnion cover).card : ℝ) := by
    rw [← sum_card_eq_card_biUnion_of_disjoint s cover hdisj]
    push_cast
    ring
  rw [hsum_eq] at hsum_ge
  exact le_trans hsum_ge hbudget

#print axioms GreedyDisjointCover.sum_card_eq_card_biUnion_of_disjoint
#print axioms GreedyDisjointCover.card_mul_le_of_disjoint_covers
#print axioms GreedyDisjointCover.card_le_div_of_disjoint_covers
#print axioms GreedyDisjointCover.card_le_div_of_disjoint_covers_real

end GreedyDisjointCover
