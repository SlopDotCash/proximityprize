/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.InformationTheory.Hamming

/-!
# Unique decoding below half the minimum distance (Finset form)

A clean, self-contained (Mathlib-only) statement of the classical unique-decoding fact, phrased
directly on a `Finset` of words: if the words are pairwise at Hamming distance `≥ d` and all lie
within Hamming radius `r` of a center `y`, with `2r < d`, then there is at most one of them.

`card_le_one_of_two_mul_radius_lt`: the list size in the unique-decoding regime is `≤ 1`. This is
the sharp `L = 1` endpoint of the average-radius list-decoding hierarchy (cf. the average-radius
Plotkin bound `CodingTheory.avg_radius_plotkin`): minimum distance forces a *singleton* list once
the radius is below `d/2`. The proof is the triangle inequality: two distinct codewords within `r`
of `y` would be within `2r < d` of each other.
-/

open Finset

variable {ι : Type*} [Fintype ι] {F : Type*} [DecidableEq F]

namespace CodingTheory

/-- **Unique decoding below half the minimum distance.** If the words in `T` are pairwise at
Hamming distance `≥ d`, all lie within Hamming distance `r` of a center `y`, and `2r < d`, then `T`
has at most one element. -/
theorem card_le_one_of_two_mul_radius_lt (T : Finset (ι → F)) (y : ι → F) (d r : ℕ)
    (hlt : 2 * r < d)
    (hpair : ∀ c ∈ T, ∀ c' ∈ T, c ≠ c' → d ≤ hammingDist c c')
    (hball : ∀ c ∈ T, hammingDist c y ≤ r) :
    T.card ≤ 1 := by
  by_contra h
  rw [not_le] at h
  obtain ⟨c, hc, c', hc', hne⟩ := Finset.one_lt_card.mp h
  have h1 : d ≤ hammingDist c c' := hpair c hc c' hc' hne
  have h2 : hammingDist c c' ≤ hammingDist c y + hammingDist y c' := hammingDist_triangle c y c'
  have h3 : hammingDist c y ≤ r := hball c hc
  have h4 : hammingDist y c' ≤ r := by rw [hammingDist_comm]; exact hball c' hc'
  omega

end CodingTheory

#print axioms CodingTheory.card_le_one_of_two_mul_radius_lt
