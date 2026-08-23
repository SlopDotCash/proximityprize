/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GVCounting

/-!
# The Gilbert–Varshamov existence bound

There exists a code `C ⊆ (ι → F)` whose codewords are pairwise at Hamming distance `> r`
(`r = ⌊δ·n⌋`, i.e. minimum distance `≥ r+1`) and which is large:

  `qⁿ = |ι → F|  ≤  |C| · Vol_q(δ, n)`,    i.e.   `|C| ≥ qⁿ / Vol_q(δ, n)`.

Proof (classical greedy / sphere-covering): take a **maximum-cardinality** packing `C` (a code with
pairwise distance `> r`); it exists by finiteness. Maximality forces the radius-`r` balls around `C`
to cover the space — any uncovered point could be adjoined, contradicting maximality — and then the
covering count `card_le_card_mul_hammingBallVolume_of_covering` (`GVCounting`) gives the bound.

## Main result (`sorry`-free; axioms = `propext, Classical.choice, Quot.sound`)

* `exists_packing_card_mul_hammingBallVolume_ge`.
-/

namespace CodingTheory

open Finset

/-- **Gilbert–Varshamov existence bound.** There is a code with pairwise distance `> ⌊δ·n⌋` and
size at least `qⁿ / Vol_q(δ, n)`. -/
theorem exists_packing_card_mul_hammingBallVolume_ge
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Fintype F] [DecidableEq F] (δ : ℝ) :
    ∃ C : Finset (ι → F),
      (∀ c ∈ C, ∀ c' ∈ C, c ≠ c' → ⌊δ * Fintype.card ι⌋₊ < hammingDist c c') ∧
      Fintype.card (ι → F)
        ≤ C.card * hammingBallVolume (Fintype.card F) δ (Fintype.card ι) := by
  classical
  set r : ℕ := ⌊δ * Fintype.card ι⌋₊ with hr
  -- Maximum-cardinality packing exists (the empty code is a packing).
  obtain ⟨C, hCmem, hCmax⟩ :=
    Finset.exists_max_image
      (Finset.univ.filter
        (fun C : Finset (ι → F) => ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' → r < hammingDist c c'))
      Finset.card ⟨∅, by simp⟩
  rw [Finset.mem_filter] at hCmem
  have hpack : ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' → r < hammingDist c c' := hCmem.2
  -- Maximality ⇒ the radius-`r` balls around `C` cover everything.
  have hcover : ∀ x : ι → F, ∃ c ∈ C, x ∈ ListDecodable.hammingBall c r := by
    intro x
    by_cases hx : x ∈ C
    · exact ⟨x, hx, by simp [ListDecodable.hammingBall]⟩
    · have hnotpack :
          ¬ (∀ c ∈ insert x C, ∀ c' ∈ insert x C, c ≠ c' → r < hammingDist c c') := by
        intro hcontra
        have hmem : (insert x C) ∈ Finset.univ.filter
            (fun C : Finset (ι → F) => ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' → r < hammingDist c c') :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcontra⟩
        have hle := hCmax _ hmem
        rw [Finset.card_insert_of_notMem hx] at hle
        omega
      push_neg at hnotpack
      obtain ⟨a, ha, b, hb, hab, hdist⟩ := hnotpack
      rw [Finset.mem_insert] at ha hb
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · exact absurd (ha.trans hb.symm) hab
      · refine ⟨b, hb, ?_⟩
        have key : hammingDist b x ≤ r := by
          rw [hammingDist_comm, ← ha]; exact hdist
        simp only [ListDecodable.hammingBall, Set.mem_setOf_eq]
        convert key using 2
      · refine ⟨a, ha, ?_⟩
        have key : hammingDist a x ≤ r := by rw [← hb]; exact hdist
        simp only [ListDecodable.hammingBall, Set.mem_setOf_eq]
        convert key using 2
      · exact absurd hdist (not_le.mpr (hpack a ha b hb hab))
  exact ⟨C, hpack, card_le_card_mul_hammingBallVolume_of_covering C δ hcover⟩

end CodingTheory

-- Axiom audit.
#print axioms CodingTheory.exists_packing_card_mul_hammingBallVolume_ge
