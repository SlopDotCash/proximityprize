/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CS25BallIntersection

/-!
# Second-moment off-diagonal sum as a sum of list-decoding list sizes (#82)

A Fubini double-count identity for the CS25 second-moment machinery:

  `∑_{e∈C} |B(0,δ)∩B(e,δ)|  =  ∑_{w∈B(0,δ)} |{e∈C : Δ(w,e) ≤ δ}|`.

The right-hand summand `|{e∈C : Δ(w,e) ≤ δ}|` is exactly the **list-decoding list size** of `C` at the
received word `w` and radius `δ`.  Since `∑_{e∈C} jointCoverCount δ 0 e = E[N²]/|C|`
(`sum_sq_secondMomentCount_eq`), this rewrites the second moment in terms of list sizes — so any
uniform list-size bound `L` (e.g. the in-tree Johnson bound in the unique/Johnson-decoding range)
yields `∑_{e∈C} jointCoverCount δ 0 e ≤ |B(0,δ)|·L`, controlling the off-diagonal of the second
moment.  Both statements are elementary (`Finset` double counting), `sorry`/`axiom`-free.
-/

namespace ArkLib.CS25

open scoped BigOperators NNReal ENNReal
open Code

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Fintype F] [DecidableEq F] [AddCommGroup F]

/-- **Fubini: second-moment off-diagonal sum = sum of list sizes.**
`∑_{e∈C} |B(0,δ)∩B(e,δ)| = ∑_{w∈B(0,δ)} |{e∈C : Δ(w,e) ≤ δ}|`.  Pure double counting: the joint
cover count is `#{w : w∈B(0,δ) ∧ w∈B(e,δ)}`; summing over `e` and exchanging the order of summation
groups by `w`, with the `w∈B(0,δ)` factor pulled out (it is `e`-independent). -/
theorem sum_jointCoverCount_eq_sum_listSize (C : Finset (ι → F)) (δ : ℝ≥0) :
    ∑ e ∈ C, jointCoverCount δ 0 e
      = ∑ w ∈ Finset.univ.filter
            (fun w : ι → F => (relHammingDist w 0 : ENNReal) ≤ (δ : ENNReal)),
          (C.filter (fun e => (relHammingDist w e : ENNReal) ≤ (δ : ENNReal))).card := by
  classical
  have hLHS : ∀ e, jointCoverCount δ 0 e
      = ∑ w ∈ (Finset.univ : Finset (ι → F)),
          (if (relHammingDist w 0 : ENNReal) ≤ (δ : ENNReal)
              ∧ (relHammingDist w e : ENNReal) ≤ (δ : ENNReal) then 1 else 0) := by
    intro e; rw [jointCoverCount, Finset.card_filter]
  simp only [hLHS]
  rw [Finset.sum_comm, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  by_cases hw : (relHammingDist w 0 : ENNReal) ≤ (δ : ENNReal)
  · simp only [hw, true_and, if_true]; rw [Finset.card_filter]
  · simp only [hw, false_and, if_false, Finset.sum_const_zero]

/-- **Second-moment off-diagonal sum bounded by `|B(0,δ)| · L`**, for any uniform bound `L` on the
list-decoding list size `|{e∈C : Δ(w,e) ≤ δ}|`.  With `sum_sq_secondMomentCount_eq`
(`E[N²] = |C|·∑ jointCoverCount`) and the in-tree Johnson list-size bound, this controls the second
moment in the Johnson-decoding range. -/
theorem sum_jointCoverCount_le_card_mul_listSize (C : Finset (ι → F)) (δ : ℝ≥0) (L : ℕ)
    (hL : ∀ w : ι → F,
      (C.filter (fun e => (relHammingDist w e : ENNReal) ≤ (δ : ENNReal))).card ≤ L) :
    ∑ e ∈ C, jointCoverCount δ 0 e
      ≤ (Finset.univ.filter
          (fun w : ι → F => (relHammingDist w 0 : ENNReal) ≤ (δ : ENNReal))).card * L := by
  rw [sum_jointCoverCount_eq_sum_listSize]
  refine le_trans (Finset.sum_le_sum (fun w _ => hL w)) ?_
  rw [Finset.sum_const, smul_eq_mul]

end ArkLib.CS25

-- Axiom audit.
#print axioms ArkLib.CS25.sum_jointCoverCount_eq_sum_listSize
#print axioms ArkLib.CS25.sum_jointCoverCount_le_card_mul_listSize
