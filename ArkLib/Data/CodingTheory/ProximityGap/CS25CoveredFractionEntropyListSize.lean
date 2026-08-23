/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CS25CoveredFractionListSize
import ArkLib.Data.CodingTheory.ProximityGap.CS25BallEntropy

/-!
# Entropy-form covered fraction via the second moment and a list-size bound (#82)

Combining the second-moment covered-fraction bound `covered_count_mul_listSize_ge`
(`|𝒞|·V ≤ |close|·L`) with the entropy ball bound `filter_ball_card_ge_qEntropy`
(`q^{n·H_q(r/n)} ≤ (n+1)·V`) gives the **entropy (rate) form** of the second-moment covered fraction:

  `|𝒞| · q^{n·H_q(r/n)}  ≤  (n+1) · |close| · L`,

i.e. `|close| ≳ |𝒞|·q^{n·H_q(r/n)} / ((n+1)·L)`.  This is the second-moment companion to
`covered_fraction_entropy_general` (which uses the near-codeword count `|near|` in place of the
list-size bound `L`).  `sorry`/`axiom`-free.
-/

namespace ArkLib.CS25

open scoped BigOperators
open Finset CodingTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Fintype F] [DecidableEq F] [AddCommGroup F]

/-- **Entropy-form covered fraction via the second moment (#82).**  For `q = |F| ≥ 2`, `n = |ι|`,
`0 < r < n`, a uniform list-size bound `closeCount 𝒞 r ≤ L`, and `|𝒞|·V > 0`:
`|𝒞| · q^{n·H_q(r/n)} ≤ (n+1) · |close| · L`. -/
theorem covered_count_entropy_listSize (hq : 2 ≤ Fintype.card F) (𝒞 : Finset (ι → F))
    (r L : ℕ) (hr0 : 0 < r) (hrn : r < Fintype.card ι)
    (hL : ∀ w : ι → F, closeCount 𝒞 r w ≤ L)
    (hpos : 0 < 𝒞.card * (univ.filter (fun w : ι → F => hammingDist w 0 ≤ r)).card) :
    (𝒞.card : ℝ)
        * (Fintype.card F : ℝ)
          ^ ((Fintype.card ι : ℝ) * qEntropy (Fintype.card F) ((r : ℝ) / (Fintype.card ι : ℝ)))
      ≤ ((Fintype.card ι : ℝ) + 1)
          * (univ.filter (fun w : ι → F => closeCount 𝒞 r w ≠ 0)).card * L := by
  have hball := filter_ball_card_ge_qEntropy hq r hr0 hrn
  have hVeq : (univ.filter (fun w : ι → F => hammingDist (0 : ι → F) w ≤ r)).card
      = (univ.filter (fun w : ι → F => hammingDist w 0 ≤ r)).card := by
    congr 1; ext w; simp only [Finset.mem_filter, hammingDist_comm]
  rw [hVeq] at hball
  have hcov : ((𝒞.card : ℝ)
        * (univ.filter (fun w : ι → F => hammingDist w 0 ≤ r)).card)
      ≤ ((univ.filter (fun w : ι → F => closeCount 𝒞 r w ≠ 0)).card : ℝ) * L := by
    exact_mod_cast covered_count_mul_listSize_ge 𝒞 r L hL hpos
  calc (𝒞.card : ℝ)
          * (Fintype.card F : ℝ)
            ^ ((Fintype.card ι : ℝ) * qEntropy (Fintype.card F) ((r : ℝ) / (Fintype.card ι : ℝ)))
        ≤ (𝒞.card : ℝ)
            * (((Fintype.card ι : ℝ) + 1)
              * (univ.filter (fun w : ι → F => hammingDist w 0 ≤ r)).card) :=
          mul_le_mul_of_nonneg_left hball (Nat.cast_nonneg _)
      _ = ((Fintype.card ι : ℝ) + 1)
            * ((𝒞.card : ℝ) * (univ.filter (fun w : ι → F => hammingDist w 0 ≤ r)).card) := by ring
      _ ≤ ((Fintype.card ι : ℝ) + 1)
            * (((univ.filter (fun w : ι → F => closeCount 𝒞 r w ≠ 0)).card : ℝ) * L) :=
          mul_le_mul_of_nonneg_left hcov (by positivity)
      _ = ((Fintype.card ι : ℝ) + 1)
            * (univ.filter (fun w : ι → F => closeCount 𝒞 r w ≠ 0)).card * L := by ring

end ArkLib.CS25

-- Axiom audit.
#print axioms ArkLib.CS25.covered_count_entropy_listSize
