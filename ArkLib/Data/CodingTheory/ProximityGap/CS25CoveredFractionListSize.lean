/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CS25SecondMomentReduction

/-!
# Covered fraction via the second moment and a list-size bound (#82)

A clean second-moment derivation of the CS25 covered-fraction lower bound, using a **list-decoding
list-size bound** as the only input.  If every word has at most `L` close codewords
(`closeCount 𝒞 r w ≤ L` — a uniform list-size bound), then

  `|𝒞| · V  ≤  |close| · L`,    i.e.   `|close| ≥ |𝒞|·V / L`,

where `V = |B(0,r)|` and `close = {w : Δ₀(w,𝒞) ≤ r}`.  The proof is Paley-Zygmund
(`sq_card_mul_volume_le_card_close_mul_sum_sq`: `(|𝒞|·V)² ≤ |close|·∑ closeCount²`) combined with the
pointwise list-size bound `∑ closeCount² ≤ L·∑ closeCount = L·|𝒞|·V` (`sum_closeCount_eq`) and a
`ℕ`-cancellation.  This is the second-moment companion to the weight-enumerator covered fraction
(`rs_card_close_mul_sum_ge`): with the in-tree Johnson list-size bound supplying `L` in the
Johnson-decoding range, it gives a concrete covered fraction.  `sorry`/`axiom`-free.
-/

namespace ArkLib.CS25

open scoped BigOperators
open Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Fintype F] [DecidableEq F] [AddCommGroup F]

/-- **Covered fraction via the second moment and a list-size bound (#82).**
`closeCount 𝒞 r w ≤ L` for all `w` ⟹ `|𝒞|·V ≤ |close|·L`. -/
theorem covered_count_mul_listSize_ge (𝒞 : Finset (ι → F)) (r : ℕ) (L : ℕ)
    (hL : ∀ w : ι → F, closeCount 𝒞 r w ≤ L)
    (hpos : 0 < 𝒞.card * (univ.filter (fun w : ι → F => hammingDist w 0 ≤ r)).card) :
    𝒞.card * (univ.filter (fun w : ι → F => hammingDist w 0 ≤ r)).card
      ≤ (univ.filter (fun w : ι → F => closeCount 𝒞 r w ≠ 0)).card * L := by
  have hsum_sq : (∑ w : ι → F, (closeCount 𝒞 r w) ^ 2)
      ≤ L * (𝒞.card * (univ.filter (fun w : ι → F => hammingDist w 0 ≤ r)).card) := by
    rw [← sum_closeCount_eq 𝒞 r, Finset.mul_sum]
    refine Finset.sum_le_sum (fun w _ => ?_)
    rw [sq]
    exact Nat.mul_le_mul_right _ (hL w)
  have hPZ := sq_card_mul_volume_le_card_close_mul_sum_sq 𝒞 r
  have key : ∀ (M A : ℕ), M ^ 2 ≤ A * (L * M) → 0 < M → M ≤ A * L := by
    intro M A h hM
    rw [sq, ← mul_assoc] at h
    exact Nat.le_of_mul_le_mul_right h hM
  exact key _ _ (le_trans hPZ (Nat.mul_le_mul_left _ hsum_sq)) hpos

end ArkLib.CS25

-- Axiom audit.
#print axioms ArkLib.CS25.covered_count_mul_listSize_ge
