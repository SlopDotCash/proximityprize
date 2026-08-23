/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.CodeGeometry

/-!
# The Plotkin bound

For an injective family of `L` codewords with pairwise Hamming distance `≥ d`,

  `L · (L − 1) · d  ≤  L² · (n · (1 − 1/q))`,

the classical Plotkin inequality (for `d > n(1−1/q)` it rearranges to `L ≤ d / (d − n(1−1/q))`).
The proof combines the in-tree Gram/PSD upper bound on the total pairwise distance
(`CodeGeometry.sum_sum_hammingDist_le`, `∑ᵢⱼ Δ(cᵢ,cⱼ) ≤ L²·n·(1−1/q)`) with the off-diagonal lower
bound `∑ᵢⱼ Δ(cᵢ,cⱼ) ≥ L·(L−1)·d` (every distinct pair is `≥ d` apart).  Together with the Singleton,
Hamming/sphere-packing, and Gilbert–Varshamov bounds this rounds out the classical bounds suite.
`sorry`/`axiom`-free.
-/

namespace ArkLib.CS25

open scoped BigOperators
open Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {α : Type} [Fintype α] [DecidableEq α]

/-- **Plotkin bound (indexed form).** For an injective family of `L` codewords with pairwise Hamming
distance `≥ d`, `L·(L−1)·d ≤ L²·(n·(1−1/q))`. -/
theorem plotkin_indexed {L : ℕ} (c : Fin L → ι → α) (hq : 0 < Fintype.card α) (d : ℕ)
    (hd : ∀ i j : Fin L, i ≠ j → (d : ℝ) ≤ hammingDist (c i) (c j)) :
    (L : ℝ) * ((L : ℝ) - 1) * d
      ≤ (L : ℝ) * (L : ℝ) * ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card α : ℝ))) := by
  have hupper := CodeGeometry.sum_sum_hammingDist_le c hq
  have hstep : ∑ i : Fin L, ∑ j : Fin L, (if i = j then (0 : ℝ) else (d : ℝ))
      ≤ ∑ i : Fin L, ∑ j : Fin L, (hammingDist (c i) (c j) : ℝ) := by
    refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
    by_cases hij : i = j
    · simp only [hij, if_pos]; positivity
    · simp only [hij, if_neg, not_false_iff]; exact hd i j hij
  have heval : ∑ i : Fin L, ∑ j : Fin L, (if i = j then (0 : ℝ) else (d : ℝ))
      = (L : ℝ) * ((L : ℝ) - 1) * d := by
    have h1 : ∀ (i j : Fin L), (if i = j then (0 : ℝ) else (d : ℝ))
        = (d : ℝ) - (if i = j then (d : ℝ) else 0) := by
      intro i j; by_cases hij : i = j <;> simp [hij]
    simp only [h1, Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_ite_eq, Finset.mem_univ,
      if_true, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [heval] at hstep
  linarith

end ArkLib.CS25

-- Axiom audit.
#print axioms ArkLib.CS25.plotkin_indexed
