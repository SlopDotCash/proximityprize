/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.PlotkinBound

/-!
# The Plotkin bound — cardinality form

The usable cardinality form of the Plotkin bound, derived from the quadratic `plotkin_indexed`: for
an injective family of `L ≥ 1` codewords with pairwise Hamming distance `≥ d`,

  `L · (d − n·(1 − 1/q)) ≤ d`.

When `d > n(1 − 1/q)` (the high-distance regime) this rearranges to `L ≤ d / (d − n(1−1/q))`, bounding
the number of codewords.  `sorry`/`axiom`-free.
-/

namespace ArkLib.CS25

open scoped BigOperators
open Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {α : Type} [Fintype α] [DecidableEq α]

/-- **Plotkin bound, cardinality form.**  For an injective family of `L ≥ 1` codewords with pairwise
distance `≥ d`, `L·(d − n·(1−1/q)) ≤ d`. -/
theorem plotkin_card_le {L : ℕ} (c : Fin L → ι → α) (hq : 0 < Fintype.card α) (d : ℕ)
    (hd : ∀ i j : Fin L, i ≠ j → (d : ℝ) ≤ hammingDist (c i) (c j)) (hL : 1 ≤ L) :
    (L : ℝ) * ((d : ℝ) - (Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card α : ℝ))) ≤ (d : ℝ) := by
  have hp := plotkin_indexed c hq d hd
  have hL0 : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  nlinarith [hp, hL0, mul_pos hL0 hL0]

end ArkLib.CS25

-- Axiom audit.
#print axioms ArkLib.CS25.plotkin_card_le
