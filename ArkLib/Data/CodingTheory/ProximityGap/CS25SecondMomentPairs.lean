/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators

/-!
# Second moment as a pair count (CS25 #82, deliverable 2)

The generic identity behind `E[N²]`: for a count `X(w) = #{c : Q w c}`,

  `∑_w X(w)² = ∑_c ∑_{c'} #{w : Q w c ∧ Q w c'}`.

Applied to `X(w) = #{c ∈ RS : δᵣ(w,c) ≤ δ}`, the right side is `∑_{c,c'} |B(c)∩B(c')|`, which (by
translation invariance and RS linearity) becomes `|RS| · ∑_d A_d · I(d)` — the weight-enumerator /
ball-intersection form of the CS25 second moment.
-/

open scoped BigOperators

namespace ArkLib.CS25

/-- **Second moment as a pair count.** `∑_w (#{c : Q w c})² = ∑_c ∑_{c'} #{w : Q w c ∧ Q w c'}`. -/
theorem sum_sq_card_filter_eq_sum_pairs {α β : Type*} [Fintype α] [Fintype β]
    (Q : α → β → Prop) [DecidableEq α] [DecidableEq β] [∀ w c, Decidable (Q w c)] :
    (∑ w : α, ((Finset.univ.filter (fun c => Q w c)).card) ^ 2)
      = ∑ c : β, ∑ c' : β,
          (Finset.univ.filter (fun w => Q w c ∧ Q w c')).card := by
  classical
  have hpt : ∀ w : α,
      ((Finset.univ.filter (fun c => Q w c)).card) ^ 2
        = ∑ c : β, ∑ c' : β, (if Q w c ∧ Q w c' then 1 else 0) := by
    intro w
    rw [sq, Finset.card_filter, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun c' _ => ?_))
    by_cases h1 : Q w c <;> by_cases h2 : Q w c' <;> simp [h1, h2]
  simp_rw [hpt]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c' _ => ?_)
  exact (Finset.card_filter (s := Finset.univ)
    (p := fun w : α => Q w c ∧ Q w c')).symm

end ArkLib.CS25
