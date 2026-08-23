/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib

/-!
# Averaging / first-moment existence

Pure-combinatorial bricks for the "averaging" step shared by list-decoding lower bounds
(GHSZ02 Cor 20, random-RS MCA #99, first-moment bad-γ #67): from a lower bound on the
*total* (or average) of a finite family of nonnegative quantities, extract a single index
whose value meets the average.  These are the `∃ received word w with ≥ E[#close codewords]`
existence steps, isolated as reusable real-valued lemmas.

All declarations are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/

namespace AveragingExistence

open Finset BigOperators

variable {ι : Type*}

/-- **First-moment existence (sum form).**  If `∑_{i ∈ s} f i ≥ c` and `s` is nonempty, some
`i ∈ s` has `f i ≥ c / #s`.  (The mean is at most the max.) -/
theorem exists_ge_sum_div_card
    (s : Finset ι) (hs : s.Nonempty) (f : ι → ℝ) (c : ℝ)
    (hsum : c ≤ ∑ i ∈ s, f i) :
    ∃ i ∈ s, c / s.card ≤ f i := by
  classical
  obtain ⟨j, hj, hmax⟩ := s.exists_max_image f hs
  refine ⟨j, hj, ?_⟩
  have hcard_pos : (0 : ℝ) < s.card := by
    exact_mod_cast Finset.card_pos.mpr hs
  rw [div_le_iff₀ hcard_pos]
  calc c ≤ ∑ i ∈ s, f i := hsum
    _ ≤ ∑ _i ∈ s, f j := Finset.sum_le_sum (fun i hi => hmax i hi)
    _ = s.card * f j := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = f j * s.card := by ring
